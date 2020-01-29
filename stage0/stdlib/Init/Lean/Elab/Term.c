// Lean compiler output
// Module: Init.Lean.Elab.Term
// Imports: Init.Lean.Util.Sorry Init.Lean.Structure Init.Lean.Meta Init.Lean.Hygiene Init.Lean.Util.RecDepth Init.Lean.Elab.Log Init.Lean.Elab.Alias Init.Lean.Elab.ResolveName Init.Lean.Elab.Level
#include "runtime/lean.h"
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
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Term_throwError___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTermAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__4;
lean_object* l_Lean_Elab_Term_elabChar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_1__mkMessageAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__4;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabNum___closed__1;
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Elab_Term_mkForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__1;
lean_object* l_Lean_mkAppStx(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadQuotation;
lean_object* l_Lean_Elab_Term_elabRawNumLit___closed__1;
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__8;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabNum(lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry___main(lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayLit___closed__1;
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock(lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayLit___closed__8;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabRawStrLit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabRawCharLit___closed__3;
lean_object* l_PersistentArray_foldlMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__8;
lean_object* l_Lean_Elab_Term_State_inhabited;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChar(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__9;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit(lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__1;
lean_object* l_Lean_Elab_Term_elabArrayLit___closed__13;
lean_object* l___private_Init_Lean_Elab_Term_12__resolveLocalName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__1;
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___main___closed__6;
lean_object* l_Lean_Elab_Term_monadLog___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Term_tryPostpone___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__9;
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_assignExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ppGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_hasSorry___main___closed__1;
lean_object* l_Lean_Elab_Term_mkTermElabAttribute___closed__3;
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__2;
extern lean_object* l_IO_Prim_fopenFlags___closed__12;
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCacheWhen(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole___closed__2;
lean_object* l_Lean_Elab_Term_monadLog___closed__3;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChar___closed__3;
lean_object* l_Lean_Elab_Term_getDeclName_x3f(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChar___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__3;
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__1;
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Lean_Elab_Term_elabTermAux___main___closed__4;
lean_object* l___private_Init_Lean_Elab_Term_14__mkConsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam___closed__1;
lean_object* l_Lean_Elab_Term_elabParen(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Elab_Term_monadLog___spec__1(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabNum___closed__2;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Elab_Term_getLocalInsts___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCacheWhen___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Term_throwError___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__2(lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_9__mkPairsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_6__exceptionToSorry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayLit___closed__2;
uint8_t l___private_Init_Lean_Elab_Term_4__isCDot___closed__1;
extern lean_object* l_Lean_Parser_Term_type___elambda__1___closed__2;
uint8_t l_List_elem___main___at_Lean_addAliasEntry___spec__18(lean_object*, lean_object*);
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_4__isCDot___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_elabQuotedName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_format(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole___closed__1;
lean_object* l_Lean_Meta_Exception_toMessageData(lean_object*);
extern lean_object* l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit___closed__2;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSort___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_tryCoe___closed__2;
lean_object* l_Lean_Elab_Term_resolveName___closed__3;
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_logTrace___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__2;
lean_object* l_Lean_Elab_Term_elabTypeStx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__5;
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_14__mkConsts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getEnv___boxed(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName___closed__3;
lean_object* l_Lean_Elab_ElabFnTable_insert___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_charLitKind___closed__2;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_mkAppTypeMismatchMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot(lean_object*);
lean_object* l_Lean_Elab_Term_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkForallUsedOnly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Meta_ExprDefEq_17__checkTypesAndAssign___closed__5;
lean_object* lean_io_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__5;
lean_object* l___private_Init_Lean_Elab_Term_8__elabTermUsing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__6;
lean_object* l_Lean_Elab_Term_monadQuotation___closed__2;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabHole(lean_object*);
lean_object* l_Lean_Elab_Term_withoutPostponing(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit___closed__3;
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__13;
lean_object* l_Lean_Elab_Term_decLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabRawStrLit___closed__2;
lean_object* l_Lean_Elab_Term_elabParen___closed__3;
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__1;
lean_object* l_Lean_Elab_Term_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Literal_type___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache(lean_object*);
lean_object* l_Lean_Elab_Term_mkForallUsedOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadLog___closed__7;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toStr___closed__1;
extern lean_object* l_Lean_Parser_Term_num___elambda__1___closed__1;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabListLit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBadCDot___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__8;
lean_object* l___private_Init_Lean_Elab_Term_11__resolveLocalNameAux___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__2;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Elab_Term_logTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__1;
lean_object* l_Lean_Elab_Term_withIncRecDepth(lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_10__elabCDot(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_5__expandCDot___closed__3;
lean_object* l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__3;
extern lean_object* l_Lean_Parser_Term_typeAscription___elambda__1___closed__2;
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabTermAux___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwError(lean_object*);
lean_object* l_Lean_Elab_Term_elabSort___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMCtx(lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Elab_Term_withLCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayLit___closed__6;
lean_object* l_Lean_Elab_Term_monadLog___closed__10;
lean_object* l_Lean_Elab_Term_resolveName___closed__6;
lean_object* l_Lean_Elab_Term_elabTypeStx___rarg(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_Elab_Term_elabParen___closed__6;
extern lean_object* l_Lean_Parser_Term_tupleTail___elambda__1___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__1;
extern lean_object* l_Lean_Parser_Term_cons___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_dbgTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabRawStrLit___closed__3;
extern lean_object* l_Lean_Parser_Term_sort___elambda__1___closed__2;
extern lean_object* l_Lean_Meta_MetaHasEval___rarg___closed__4;
lean_object* l_Lean_Elab_Term_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_Exception_hasToString(lean_object*);
lean_object* l_Lean_Elab_Term_elabParen___closed__5;
lean_object* l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__2;
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l_Lean_Elab_Term_resolveName___closed__5;
lean_object* l_Lean_Elab_Term_mkFreshExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_LVal_hasToString(lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__2;
lean_object* l_Lean_Elab_Term_trace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l_Lean_Elab_Term_elabBadCDot___closed__1;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_expandCDot_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabResult_inhabited___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock___closed__3;
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppGoal(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__1;
lean_object* l_Lean_Elab_Term_termElabAttribute___closed__2;
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getTraceState(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole___closed__3;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshTypeMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___main___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshAnonymousIdent(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParen___closed__2;
lean_object* l_Lean_Elab_Term_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_whnf(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayLit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadLog___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParen___closed__1;
lean_object* l_Lean_Elab_Term_elabListLit___closed__1;
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_11__resolveLocalNameAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftMetaM(lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l_Lean_Elab_Term_elabListLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withIncRecDepth___rarg___closed__1;
lean_object* l_Lean_Elab_Term_elabListLit___closed__2;
lean_object* l_Lean_Elab_Term_tryCoe___closed__4;
lean_object* l_Lean_Elab_Term_mkFreshAnonymousName___boxed(lean_object*);
extern lean_object* l_Lean_Meta_dbgTrace___rarg___closed__1;
lean_object* l_Lean_Elab_Term_mkConst___closed__6;
lean_object* l_Lean_Elab_Term_monadLog___closed__5;
extern lean_object* l_Lean_Parser_termParser___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_2__fromMetaException(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withIncRecDepth___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_2__fromMetaException___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParen___closed__4;
lean_object* l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_object* l_Lean_Elab_Term_elabLevel(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_termIdToAntiquot___closed__4;
lean_object* l_Lean_Elab_Term_monadLog___closed__1;
lean_object* l_Lean_Syntax_isCharLit_x3f(lean_object*);
lean_object* l_Array_isEqvAux___main___at_Lean_Elab_Term_withMVarContext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_14__mkConsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__5;
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
lean_object* l_Lean_Elab_Term_elabRawCharLit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshAnonymousName___rarg(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__3;
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Elab_Term_elabTermAux___main___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withMVarContext(lean_object*);
lean_object* l_Lean_Elab_Term_termElabAttribute___closed__4;
lean_object* l_Lean_Elab_Term_addContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_observing(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withMacroExpansion(lean_object*);
lean_object* l_Lean_Elab_Term_getTraceState___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_State_inhabited___closed__1;
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_Lean_Elab_Term_dbgTrace(lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayLit___closed__11;
lean_object* l_Lean_Elab_Term_decLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_MetavarContext_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_5__expandCDot(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryCoe___closed__1;
lean_object* l_Lean_Elab_Term_mkConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__3;
lean_object* l_Lean_Elab_Term_monadLog___closed__8;
extern lean_object* l_Lean_Expr_isSyntheticSorry___closed__1;
lean_object* l_Lean_Elab_Term_isExprMVarAssigned___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabProp___rarg(lean_object*);
lean_object* l_PersistentHashMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__3;
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_Elab_Term_termElabAttribute___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshInstanceName(lean_object*);
lean_object* l_Lean_Elab_Term_elabChar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__3;
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Parser_Term_quotedName___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__3;
lean_object* l_Lean_Elab_Term_levelMVarToParam___closed__2;
lean_object* l_Lean_Elab_Term_elabStr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabParen(lean_object*);
lean_object* l_Lean_Elab_Term_mkConst___closed__2;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabQuotedName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__1;
lean_object* l_Lean_Elab_Term_TermElabM_inhabited(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInstMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__6;
extern lean_object* l_Lean_Parser_darrow___elambda__1___rarg___closed__3;
lean_object* l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__7;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_8__elabTermUsing(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_7__postponeElabTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_setTraceState___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__7;
lean_object* l_Lean_Elab_Term_elabTacticBlock___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkConst___closed__4;
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallUsedOnly(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___main___closed__5;
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_6__exceptionToSorry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_1__mkMessageAux(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Term_monadQuotation___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_13__mkFreshLevelMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTypeStx(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__3;
lean_object* l_Lean_Elab_Term_monadLog___closed__6;
extern lean_object* l_Lean_strLitKind___closed__2;
lean_object* l_Lean_Elab_Term_withFreshMacroScope(lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__7;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___main(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_termElabAttribute___closed__3;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Elab_Term_State_inhabited___closed__2;
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Elab_getMacros(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__3;
lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__3;
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_namedHole___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftLevelM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabListLit___closed__4;
extern lean_object* l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabRawStrLit___closed__1;
lean_object* l_Lean_Syntax_prettyPrint(lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter;
lean_object* l_Lean_Elab_Term_elabRawStrLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_whnfForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Lean_Elab_Term_trySynthInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx(lean_object*);
lean_object* l_Lean_Elab_Term_isClass___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__3;
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__5;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit___closed__3;
lean_object* l_Lean_Elab_Term_monadLog___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabTypeStx___rarg___closed__1;
lean_object* l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(lean_object*);
extern lean_object* l_Lean_Elab_Exception_hasToString___closed__1;
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTermAux___main___spec__3(lean_object*, size_t, lean_object*);
extern lean_object* l_PersistentArray_empty___closed__3;
lean_object* l_Lean_Elab_Term_mkBuiltinTermElabTable(lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabStr___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit___closed__3;
lean_object* l_Lean_Elab_Term_elabProp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_assignExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_applyResult___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadQuotation___closed__4;
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule(lean_object*);
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkTermElabAttribute(lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Elab_Term_elabTermAux___main___spec__6(lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind___closed__2;
uint8_t l_PersistentHashMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__4(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_12__resolveLocalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTacticBlock___closed__2;
extern lean_object* l_Lean_Parser_Term_fun___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__7;
lean_object* l_Lean_Elab_Term_monadLog___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAppM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_8__elabTermUsing___main(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Elab_Term_mkConst___closed__7;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_expandCDot_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__3;
lean_object* l_Lean_Elab_Term_elabTermAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLevel___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSort(lean_object*);
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__5(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_15__regTraceClasses(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_7__postponeElabTerm___closed__1;
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftLevelM(lean_object*);
lean_object* l_Lean_Elab_Term_elabProp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__8;
lean_object* l_Lean_Elab_addMacroStack(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit___closed__2;
lean_object* l_Lean_Elab_Term_elabTermAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_termElabAttribute___closed__5;
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__1;
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_throwError___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addBuiltinTermElab___closed__1;
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_whnfCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrNamespace___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__1;
lean_object* l_Lean_Elab_Level_elabLevel___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addBuiltinTermElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLocalInsts(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProp(lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_7__postponeElabTerm___closed__2;
lean_object* l_Lean_Elab_Term_mkFreshInstanceName___rarg(lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__2;
lean_object* l_Lean_Elab_Term_isClass(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabResult_inhabited;
lean_object* l_Lean_Elab_Term_withMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_String_posOfAux___main___closed__1;
lean_object* l_Lean_Elab_Term_elabArrayLit___closed__4;
lean_object* l_Lean_Elab_Term_TermElabM_inhabited___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshAnonymousIdent___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabRawNumLit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___main___closed__3;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l___private_Init_Lean_Elab_Term_9__mkPairsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__1;
extern lean_object* l_Lean_Parser_Term_cdot___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__3;
lean_object* l_Lean_Elab_Term_throwTypeMismatchError(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayLit___closed__9;
lean_object* l_Lean_Elab_Term_resolveName___closed__9;
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__1;
lean_object* l_Lean_Elab_Term_elabListLit___closed__5;
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Elab_Term_mkConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkConst___closed__3;
lean_object* l_Lean_Elab_Term_resolveName___closed__4;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__2;
lean_object* l_Lean_ParametricAttribute_setParam___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_14__mkConsts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNamedHole___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__1;
lean_object* l_Lean_Elab_Term_elabArrayLit___closed__10;
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__2;
lean_object* l_Lean_Elab_Term_monadLog___closed__2;
extern lean_object* l_Lean_Meta_Exception_toStr___closed__7;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_declareBuiltinMacro___closed__4;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit___closed__1;
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__10;
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole(lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshAnonymousName(lean_object*);
lean_object* l_Lean_Elab_Term_withLCtx(lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_Lean_Elab_Term_traceAtCmdPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabTermAux___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Parser_Parser_15__throwParserCategoryAlreadyDefined___rarg___closed__2;
lean_object* l_Lean_Elab_Term_withoutPostponing___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_prop___elambda__1___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit___closed__1;
extern lean_object* l_Lean_Meta_Exception_mkAppTypeMismatchMessage___closed__8;
lean_object* l_Lean_Elab_Term_Exception_inhabited;
lean_object* l_Lean_Elab_Term_elabHole(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_str___elambda__1___closed__2;
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__2;
lean_object* l_Lean_Elab_Term_elabBadCDot___closed__2;
lean_object* l_Lean_Elab_Term_liftMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__4;
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__7;
extern lean_object* l_Lean_mkAppStx___closed__5;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_13__mkFreshLevelMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__3;
lean_object* l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName(lean_object*);
lean_object* l_Lean_Elab_Term_elabStr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__5;
extern lean_object* l_Lean_Meta_evalNat___main___closed__4;
lean_object* l_Lean_Elab_Term_getLCtx(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__6;
lean_object* l_Lean_Elab_Term_traceAtCmdPos(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_5__expandCDot___closed__2;
uint8_t l_HashMapImp_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__2(lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_Elab_Term_elabTacticBlock___closed__3;
lean_object* l_Lean_Elab_Term_decLevel___closed__5;
lean_object* l_PersistentHashMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_inhabited___rarg(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Elab_Term_monadLog___closed__9;
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_5__expandCDot___closed__1;
lean_object* l_Lean_Elab_Term_mkConst___closed__5;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__5(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit___closed__2;
lean_object* l_Lean_Elab_Term_elabArrayLit___closed__12;
lean_object* l_Lean_nameToExprAux___main(lean_object*);
lean_object* l_Lean_Elab_Term_throwError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit___closed__2;
extern lean_object* l_Bool_HasRepr___closed__2;
lean_object* l_Lean_Elab_Term_ensureType___closed__2;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__2;
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerSyntheticMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_decLevel___closed__3;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__1;
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__1(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlM___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_decLevel_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureType___closed__1;
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNamedHole(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Term_throwError___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentHashMap_containsAtAux___main___at_Lean_Parser_isValidSyntaxNodeKind___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandCDot_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_EnvExtension_setState___closed__1;
lean_object* l_Lean_Elab_Term_liftLevelM___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName___closed__2;
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadLog___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Term_13__mkFreshLevelMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__2;
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCacheWhen___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_logTrace___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_3__fromMetaState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkConst___closed__1;
lean_object* l_Lean_Elab_Term_isExprMVarAssigned(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_whnf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabHole___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_unfoldDefinition_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSort(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_levelMVarToParam___lambda__1(lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Elab_Term_4__isCDot(lean_object*);
lean_object* l_Lean_Elab_Term_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withMVarContext___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_Term_elabListLit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withIncRecDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_expandCDot_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___closed__1;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__2;
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Term_13__mkFreshLevelMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__5;
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabStr___closed__3;
lean_object* l_Lean_Elab_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getEnv(lean_object*);
lean_object* l_Lean_Elab_Term_getOpenDecls(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkTermIdFrom(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabListLit(lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayLit___closed__3;
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_decLevel___closed__4;
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__12;
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__3;
extern lean_object* l_Lean_KernelException_toMessageData___closed__12;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit___closed__1;
lean_object* l_Lean_Elab_Term_monadLog___closed__11;
lean_object* l_Lean_Elab_Term_mkTacticMVar___closed__2;
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Parser_Parser_26__BuiltinParserAttribute_add___closed__2;
lean_object* l_Lean_Elab_Term_addBuiltinTermElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabStr(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock___closed__2;
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Term_throwError___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOpenDecls___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getTraceState___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__4;
extern lean_object* l_Lean_Meta_evalNat___main___closed__3;
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkHole___closed__2;
extern lean_object* l_Lean_Meta_evalNat___main___closed__5;
lean_object* l_Lean_Elab_Term_resolveName___closed__2;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabListLit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkPairs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabStr___closed__1;
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___closed__11;
lean_object* l___private_Init_Lean_Elab_Term_5__expandCDot___closed__4;
lean_object* l_Lean_Elab_Term_isDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_decLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLCtx___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ppGoal(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_setTraceState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostpone(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkPairs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadLog___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadQuotation___closed__3;
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
lean_object* l_Lean_Elab_Term_elabTacticBlock(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
uint8_t l_Lean_SMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadLog___lambda__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNum(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_3__fromMetaState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabListLit___closed__3;
extern lean_object* l_Lean_Unhygienic_run___rarg___closed__1;
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Lean_Elab_Term_addContext(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_coeOfOptExpr___closed__1;
extern lean_object* l_Lean_Parser_Term_listLit___elambda__1___closed__2;
uint8_t l_Lean_LocalInstance_beq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__4;
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l_Lean_Elab_Term_elabRawCharLit___closed__1;
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_decLevel___closed__2;
lean_object* l_Lean_Elab_Term_decLevel___closed__1;
lean_object* l_Lean_Elab_Term_elabTermAux___main___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot___closed__1;
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__1;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Term_elabRawCharLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_builtinTermElabTable;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_mkTermElabAttribute___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMCtx___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_applyResult(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__1;
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1;
lean_object* l_Lean_Elab_Term_mkTacticMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Array_isEqvAux___main___at_Lean_Elab_Term_withMVarContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot___closed__2;
lean_object* l_Lean_Elab_Term_elabRawCharLit___closed__4;
extern lean_object* l_Lean_levelOne;
lean_object* l_Lean_Message_toString(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_char___elambda__1___closed__2;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_expandCDot_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Term_trace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabRawCharLit___closed__2;
lean_object* l_Lean_Elab_Term_mkFreshInstanceName___boxed(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChar___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__1;
lean_object* l_Lean_Elab_Term_resolveName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__1;
lean_object* l_Lean_Elab_Term_resolveName___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__2;
lean_object* l_IO_ofExcept___at___private_Init_Lean_Elab_Util_6__ElabAttribute_add___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCache(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_Inhabited___closed__1;
lean_object* l_Lean_Elab_Term_registerSyntheticMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasTypeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot___closed__3;
lean_object* l_Lean_Elab_Term_mkTacticMVar___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabNum___closed__3;
lean_object* l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__5;
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
extern lean_object* l_Lean_initAttr;
extern lean_object* l_Lean_Parser_Term_arrayLit___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_getOptions___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBadCDot___closed__3;
lean_object* l_Lean_Elab_Term_elabArrayLit___closed__5;
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_throwError___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadLog;
lean_object* l_Lean_Elab_Term_getMCtx___rarg(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlM___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__4;
lean_object* l_Lean_Elab_Term_monadLog___closed__4;
lean_object* l_Lean_Elab_Term_liftMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayLit___closed__7;
lean_object* l___private_Init_Lean_Elab_Term_9__mkPairsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit(lean_object*);
lean_object* l_Lean_Elab_Term_mkTermElabAttribute___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__2;
extern lean_object* l___private_Init_Lean_Parser_Parser_13__antiquotNestedExpr___elambda__1___rarg___closed__2;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* l_Lean_Meta_decLevel_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_monadLog___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock___closed__1;
lean_object* l_Lean_Elab_Term_expandCDot_x3f(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
extern lean_object* l_Lean_Elab_declareBuiltinMacro___closed__3;
lean_object* l_Lean_Elab_Term_mkFreshTypeMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBadCDot(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_decLevel___closed__6;
extern lean_object* l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__3;
lean_object* l_Lean_Elab_Term_tryCoe___closed__3;
lean_object* _init_l_Lean_Elab_Term_State_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_EnvExtension_setState___closed__1;
x_2 = l_Lean_MetavarContext_Inhabited___closed__1;
x_3 = l_Lean_Meta_MetaHasEval___rarg___closed__4;
x_4 = l_Lean_NameGenerator_Inhabited___closed__3;
x_5 = l_Lean_TraceState_Inhabited___closed__1;
x_6 = l_PersistentArray_empty___closed__3;
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
x_3 = l_PersistentArray_empty___closed__3;
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
x_6 = l___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___closed__1;
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
x_4 = lean_ctor_get(x_1, 3);
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
x_6 = l_PersistentArray_push___rarg(x_5, x_1);
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
x_15 = l_PersistentArray_push___rarg(x_11, x_1);
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
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Term_throwError___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_getPos(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
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
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
}
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_throwError___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_4, 2);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 3);
x_9 = l_Lean_FileMap_toPosition(x_6, x_8);
x_10 = l_Lean_Elab_Term_addContext(x_1, x_4, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_box(0);
x_14 = l_String_splitAux___main___closed__1;
lean_inc(x_7);
x_15 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set(x_15, 4, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*5, x_2);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_box(0);
x_19 = l_String_splitAux___main___closed__1;
lean_inc(x_7);
x_20 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
lean_ctor_set(x_20, 4, x_16);
lean_ctor_set_uint8(x_20, sizeof(void*)*5, x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_4, 2);
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get(x_3, 0);
x_25 = l_Lean_FileMap_toPosition(x_22, x_24);
x_26 = l_Lean_Elab_Term_addContext(x_1, x_4, x_5);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_box(0);
x_30 = l_String_splitAux___main___closed__1;
lean_inc(x_23);
x_31 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_31, 4, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*5, x_2);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_box(0);
x_35 = l_String_splitAux___main___closed__1;
lean_inc(x_23);
x_36 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_25);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
lean_ctor_set(x_36, 4, x_32);
lean_ctor_set_uint8(x_36, sizeof(void*)*5, x_2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
}
}
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Term_throwError___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Elab_getPos___at_Lean_Elab_Term_throwError___spec__2(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_throwError___spec__3(x_1, x_2, x_9, x_4, x_8);
lean_dec(x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 8);
lean_inc(x_5);
lean_inc(x_5);
x_6 = l_Lean_Elab_getBetterRef(x_1, x_5);
x_7 = l_Lean_Elab_addMacroStack(x_2, x_5);
x_8 = 2;
x_9 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_throwError___spec__1(x_7, x_8, x_6, x_3, x_4);
lean_dec(x_3);
lean_dec(x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
lean_object* l_Lean_Elab_Term_throwError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwError___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Term_throwError___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getPos___at_Lean_Elab_Term_throwError___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
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
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Term_throwError___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_throwError___spec__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_throwError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_throwError___rarg(x_1, x_2, x_3, x_4);
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
lean_object* _init_l_Lean_Elab_Term_withIncRecDepth___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_withIncRecDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 4);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_nat_dec_eq(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
x_50 = l_coeDecidableEq(x_49);
if (x_50 == 0)
{
x_5 = x_4;
goto block_45;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_2);
x_51 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
x_52 = l_Lean_Elab_Term_throwError___rarg(x_1, x_51, x_3, x_4);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
block_45:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
lean_ctor_set(x_7, 3, x_11);
x_12 = lean_apply_2(x_2, x_3, x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_ctor_get(x_7, 2);
x_16 = lean_ctor_get(x_7, 3);
x_17 = lean_ctor_get(x_7, 4);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_16, x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_19);
lean_ctor_set(x_20, 4, x_17);
lean_ctor_set(x_3, 0, x_20);
x_21 = lean_apply_2(x_2, x_3, x_5);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get(x_3, 3);
x_26 = lean_ctor_get(x_3, 4);
x_27 = lean_ctor_get(x_3, 5);
x_28 = lean_ctor_get(x_3, 6);
x_29 = lean_ctor_get(x_3, 7);
x_30 = lean_ctor_get(x_3, 8);
x_31 = lean_ctor_get(x_3, 9);
x_32 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_33 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
lean_inc(x_31);
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
x_34 = lean_ctor_get(x_22, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_22, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_22, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_22, 4);
lean_inc(x_38);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 lean_ctor_release(x_22, 4);
 x_39 = x_22;
} else {
 lean_dec_ref(x_22);
 x_39 = lean_box(0);
}
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_37, x_40);
lean_dec(x_37);
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(0, 5, 0);
} else {
 x_42 = x_39;
}
lean_ctor_set(x_42, 0, x_34);
lean_ctor_set(x_42, 1, x_35);
lean_ctor_set(x_42, 2, x_36);
lean_ctor_set(x_42, 3, x_41);
lean_ctor_set(x_42, 4, x_38);
x_43 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_23);
lean_ctor_set(x_43, 2, x_24);
lean_ctor_set(x_43, 3, x_25);
lean_ctor_set(x_43, 4, x_26);
lean_ctor_set(x_43, 5, x_27);
lean_ctor_set(x_43, 6, x_28);
lean_ctor_set(x_43, 7, x_29);
lean_ctor_set(x_43, 8, x_30);
lean_ctor_set(x_43, 9, x_31);
lean_ctor_set_uint8(x_43, sizeof(void*)*10, x_32);
lean_ctor_set_uint8(x_43, sizeof(void*)*10 + 1, x_33);
x_44 = lean_apply_2(x_2, x_43, x_5);
return x_44;
}
}
}
}
lean_object* l_Lean_Elab_Term_withIncRecDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withIncRecDepth___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_withIncRecDepth___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_withIncRecDepth___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 9);
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
x_9 = lean_ctor_get(x_2, 9);
lean_dec(x_9);
lean_ctor_set(x_2, 9, x_5);
x_10 = lean_apply_2(x_1, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_2, 3);
x_15 = lean_ctor_get(x_2, 4);
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_ctor_get(x_2, 6);
x_18 = lean_ctor_get(x_2, 7);
x_19 = lean_ctor_get(x_2, 8);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_15);
lean_ctor_set(x_22, 5, x_16);
lean_ctor_set(x_22, 6, x_17);
lean_ctor_set(x_22, 7, x_18);
lean_ctor_set(x_22, 8, x_19);
lean_ctor_set(x_22, 9, x_5);
lean_ctor_set_uint8(x_22, sizeof(void*)*10, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*10 + 1, x_21);
x_23 = lean_apply_2(x_1, x_22, x_3);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
x_27 = lean_ctor_get(x_3, 3);
x_28 = lean_ctor_get(x_3, 4);
x_29 = lean_ctor_get(x_3, 5);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_29, x_30);
x_32 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_25);
lean_ctor_set(x_32, 2, x_26);
lean_ctor_set(x_32, 3, x_27);
lean_ctor_set(x_32, 4, x_28);
lean_ctor_set(x_32, 5, x_31);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 5);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 6);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 7);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 8);
lean_inc(x_41);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_43 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
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
 x_44 = x_2;
} else {
 lean_dec_ref(x_2);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 10, 2);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_34);
lean_ctor_set(x_45, 2, x_35);
lean_ctor_set(x_45, 3, x_36);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_38);
lean_ctor_set(x_45, 6, x_39);
lean_ctor_set(x_45, 7, x_40);
lean_ctor_set(x_45, 8, x_41);
lean_ctor_set(x_45, 9, x_29);
lean_ctor_set_uint8(x_45, sizeof(void*)*10, x_42);
lean_ctor_set_uint8(x_45, sizeof(void*)*10 + 1, x_43);
x_46 = lean_apply_2(x_1, x_45, x_32);
return x_46;
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
lean_object* l_mkHashMap___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_PersistentHashMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__1;
x_3 = l_PersistentHashMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__2;
return x_1;
}
}
lean_object* l_Lean_Elab_Term_mkBuiltinTermElabTable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1;
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
uint8_t l_AssocList_contains___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
uint8_t l_HashMapImp_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_contains___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__3(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__5(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = x_2 >> x_5;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_PersistentHashMap_containsAtAux___main___at_Lean_Parser_isValidSyntaxNodeKind___spec__3(x_17, x_18, x_3);
lean_dec(x_17);
return x_19;
}
}
}
uint8_t l_PersistentHashMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__5(x_3, x_4, x_2);
return x_5;
}
}
uint8_t l_Lean_SMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_HashMapImp_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__2(x_4, x_2);
lean_dec(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_PersistentHashMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__4(x_5, x_2);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 1;
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_HashMapImp_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__2(x_9, x_2);
lean_dec(x_9);
return x_10;
}
}
}
lean_object* _init_l_Lean_Elab_Term_addBuiltinTermElab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid builtin term elaborator, elaborator for '");
return x_1;
}
}
lean_object* l_Lean_Elab_Term_addBuiltinTermElab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_Term_builtinTermElabTable;
x_6 = lean_io_ref_get(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_SMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__1(x_8, x_1);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_free_object(x_6);
x_12 = lean_io_ref_get(x_5, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_io_ref_reset(x_5, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_ElabFnTable_insert___rarg(x_13, x_1, x_3);
x_18 = lean_io_ref_set(x_5, x_17, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_3);
x_27 = l_Lean_Name_toString___closed__1;
x_28 = l_Lean_Name_toStringWithSep___main(x_27, x_1);
x_29 = l_Lean_Elab_Term_addBuiltinTermElab___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l___private_Init_Lean_Parser_Parser_15__throwParserCategoryAlreadyDefined___rarg___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_33);
return x_6;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_6, 0);
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_6);
x_36 = l_Lean_SMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__1(x_34, x_1);
x_37 = l_coeDecidableEq(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_io_ref_get(x_5, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_io_ref_reset(x_5, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Elab_ElabFnTable_insert___rarg(x_39, x_1, x_3);
x_44 = lean_io_ref_set(x_5, x_43, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_39);
lean_dec(x_3);
lean_dec(x_1);
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_47 = x_41;
} else {
 lean_dec_ref(x_41);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_3);
lean_dec(x_1);
x_49 = lean_ctor_get(x_38, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_51 = x_38;
} else {
 lean_dec_ref(x_38);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_3);
x_53 = l_Lean_Name_toString___closed__1;
x_54 = l_Lean_Name_toStringWithSep___main(x_53, x_1);
x_55 = l_Lean_Elab_Term_addBuiltinTermElab___closed__1;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = l___private_Init_Lean_Parser_Parser_15__throwParserCategoryAlreadyDefined___rarg___closed__2;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_35);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_3);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_6);
if (x_61 == 0)
{
return x_6;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_6, 0);
x_63 = lean_ctor_get(x_6, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_6);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_HashMapImp_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__5(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_PersistentHashMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentHashMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__4(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_SMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_SMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_addBuiltinTermElab___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_regBuiltinTermElab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_declareBuiltinMacro___closed__4;
x_2 = l_Lean_mkAppStx___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addBuiltinTermElab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__5;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to emit registration code for builtin term elaborator '");
return x_1;
}
}
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_5 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__2;
lean_inc(x_3);
x_6 = l_Lean_Name_append___main(x_5, x_3);
x_7 = lean_box(0);
x_8 = l_Lean_nameToExprAux___main(x_2);
lean_inc(x_3);
x_9 = l_Lean_nameToExprAux___main(x_3);
lean_inc(x_3);
x_10 = l_Lean_mkConst(x_3, x_7);
x_11 = l_Lean_Parser_declareBuiltinParser___closed__8;
x_12 = lean_array_push(x_11, x_8);
x_13 = lean_array_push(x_12, x_9);
x_14 = lean_array_push(x_13, x_10);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__6;
x_17 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_14, x_14, x_15, x_16);
lean_dec(x_14);
x_18 = l_Lean_Parser_declareBuiltinParser___closed__7;
lean_inc(x_6);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_7);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_box(0);
x_21 = 0;
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_Options_empty;
x_25 = l_Lean_Environment_addAndCompile(x_1, x_24, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_25);
lean_dec(x_6);
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_3);
x_28 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__7;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Char_HasRepr___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_3);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = l_Lean_initAttr;
x_36 = lean_box(0);
x_37 = l_Lean_ParametricAttribute_setParam___rarg(x_35, x_34, x_6, x_36);
x_38 = l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1(x_37, x_4);
lean_dec(x_37);
return x_38;
}
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid attribute 'builtinTermElab', must be persistent");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected term elaborator type at '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' `TermElab` expected");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TermElab");
return x_1;
}
}
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_coeDecidableEq(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__2;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_mkAppStx___closed__6;
lean_inc(x_1);
x_10 = l_Lean_Elab_syntaxNodeKindOfAttrParam(x_1, x_9, x_3);
x_11 = l_IO_ofExcept___at___private_Init_Lean_Elab_Util_6__ElabAttribute_add___spec__1(x_10, x_5);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_25; 
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
lean_inc(x_2);
lean_inc(x_1);
x_25 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_26 = l___private_Init_Lean_Parser_Parser_26__BuiltinParserAttribute_add___closed__2;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_13);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lean_ConstantInfo_type(x_28);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 4)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = l_Lean_mkAppStx___closed__1;
x_40 = lean_string_dec_eq(x_38, x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_1);
x_41 = lean_box(0);
x_15 = x_41;
goto block_24;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_Elab_declareBuiltinMacro___closed__3;
x_43 = lean_string_dec_eq(x_37, x_42);
lean_dec(x_37);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_1);
x_44 = lean_box(0);
x_15 = x_44;
goto block_24;
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_Lean_mkAppStx___closed__5;
x_46 = lean_string_dec_eq(x_36, x_45);
lean_dec(x_36);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_35);
lean_dec(x_12);
lean_dec(x_1);
x_47 = lean_box(0);
x_15 = x_47;
goto block_24;
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__5;
x_49 = lean_string_dec_eq(x_35, x_48);
lean_dec(x_35);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_12);
lean_dec(x_1);
x_50 = lean_box(0);
x_15 = x_50;
goto block_24;
}
else
{
lean_object* x_51; 
lean_dec(x_14);
x_51 = l_Lean_Elab_Term_declareBuiltinTermElab(x_1, x_12, x_2, x_13);
return x_51;
}
}
}
}
}
else
{
lean_object* x_52; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_1);
x_52 = lean_box(0);
x_15 = x_52;
goto block_24;
}
}
else
{
lean_object* x_53; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_1);
x_53 = lean_box(0);
x_15 = x_53;
goto block_24;
}
}
else
{
lean_object* x_54; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_1);
x_54 = lean_box(0);
x_15 = x_54;
goto block_24;
}
}
else
{
lean_object* x_55; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_1);
x_55 = lean_box(0);
x_15 = x_55;
goto block_24;
}
}
else
{
lean_object* x_56; 
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_1);
x_56 = lean_box(0);
x_15 = x_56;
goto block_24;
}
}
else
{
lean_object* x_57; 
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_1);
x_57 = lean_box(0);
x_15 = x_57;
goto block_24;
}
}
block_24:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
x_16 = l_Lean_Name_toString___closed__1;
x_17 = l_Lean_Name_toStringWithSep___main(x_16, x_2);
x_18 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__3;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__4;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_22, 0, x_21);
if (lean_is_scalar(x_14)) {
 x_23 = lean_alloc_ctor(1, 2, 0);
} else {
 x_23 = x_14;
 lean_ctor_set_tag(x_23, 1);
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
}
else
{
uint8_t x_58; 
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_11);
if (x_58 == 0)
{
return x_11;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_11, 0);
x_60 = lean_ctor_get(x_11, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_11);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinTermElab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Builtin term elaborator");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__2;
x_2 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__3;
x_3 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__4;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__5;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("termElab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_mkTermElabAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_mkTermElabAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Elab_Term_mkTermElabAttribute___closed__2;
x_3 = l_Lean_mkAppStx___closed__6;
x_4 = l_Lean_Elab_Term_mkTermElabAttribute___closed__3;
x_5 = l_Lean_Parser_termParser___closed__1;
x_6 = l_Lean_Elab_Term_builtinTermElabTable;
x_7 = l_Lean_Elab_mkElabAttribute___rarg(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Term_termElabAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1;
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
x_4 = l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__1;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_AttributeImpl_inhabited___closed__2;
x_2 = l_Lean_Elab_Term_termElabAttribute___closed__4;
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_formatStxAux___main(x_6, x_7, x_5);
x_9 = l_Lean_Options_empty;
x_10 = l_Lean_Format_pretty(x_8, x_9);
x_11 = l_List_repr___rarg___closed__2;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_List_repr___rarg___closed__3;
x_14 = lean_string_append(x_12, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Elab_Term_getDeclName_x3f(lean_object* x_1, lean_object* x_2) {
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
x_3 = lean_ctor_get(x_1, 4);
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
x_3 = lean_ctor_get(x_1, 7);
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
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_logTrace___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_throwError___spec__3(x_3, x_2, x_6, x_4, x_5);
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_9, 2);
x_13 = l_PersistentArray_push___rarg(x_12, x_11);
lean_ctor_set(x_9, 2, x_13);
x_14 = lean_box(0);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_22 = l_PersistentArray_push___rarg(x_18, x_15);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set(x_23, 5, x_21);
x_24 = lean_box(0);
lean_ctor_set(x_7, 1, x_23);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_7, 1);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_inc(x_26);
lean_dec(x_7);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_25, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 5);
lean_inc(x_32);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 lean_ctor_release(x_25, 4);
 lean_ctor_release(x_25, 5);
 x_33 = x_25;
} else {
 lean_dec_ref(x_25);
 x_33 = lean_box(0);
}
x_34 = l_PersistentArray_push___rarg(x_29, x_26);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 6, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_31);
lean_ctor_set(x_35, 5, x_32);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_getPos___at_Lean_Elab_Term_throwError___spec__2(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_logAt___at_Lean_Elab_Term_logTrace___spec__2(x_7, x_2, x_3, x_4, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_logTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_9, 1);
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_inc(x_10);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_3);
x_15 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = 0;
x_17 = l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(x_2, x_16, x_15, x_4, x_5);
return x_17;
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
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_log___at_Lean_Elab_Term_logTrace___spec__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_logTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_logTrace(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_trace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Elab_Term_getOptions(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_1);
x_10 = l_Lean_checkTraceOption(x_8, x_1);
lean_dec(x_8);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_6);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_3, x_13);
x_15 = l_Lean_Elab_Term_logTrace(x_1, x_2, x_14, x_4, x_9);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
lean_inc(x_1);
x_18 = l_Lean_checkTraceOption(x_16, x_1);
lean_dec(x_16);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_box(0);
x_23 = lean_apply_1(x_3, x_22);
x_24 = l_Lean_Elab_Term_logTrace(x_1, x_2, x_23, x_4, x_17);
return x_24;
}
}
}
}
lean_object* l_Lean_Elab_Term_trace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_trace(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_traceAtCmdPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Term_getOptions(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_1);
x_9 = l_Lean_checkTraceOption(x_7, x_1);
lean_dec(x_7);
x_10 = l_coeDecidableEq(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_5);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_2, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_Elab_Term_logTrace(x_1, x_14, x_13, x_3, x_8);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_1);
x_18 = l_Lean_checkTraceOption(x_16, x_1);
lean_dec(x_16);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_box(0);
x_23 = lean_apply_1(x_2, x_22);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Term_logTrace(x_1, x_24, x_23, x_3, x_17);
return x_25;
}
}
}
}
lean_object* l_Lean_Elab_Term_traceAtCmdPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_traceAtCmdPos(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
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
lean_object* l___private_Init_Lean_Elab_Term_1__mkMessageAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = l_Lean_Syntax_getPos(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Elab_mkMessageCore(x_5, x_6, x_3, x_4, x_8);
lean_dec(x_8);
lean_dec(x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Elab_mkMessageCore(x_5, x_6, x_3, x_4, x_10);
lean_dec(x_10);
lean_dec(x_6);
return x_11;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_1__mkMessageAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l___private_Init_Lean_Elab_Term_1__mkMessageAux(x_1, x_2, x_3, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Term_2__fromMetaException(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Meta_Exception_toMessageData(x_3);
x_5 = 2;
x_6 = l___private_Init_Lean_Elab_Term_1__mkMessageAux(x_1, x_2, x_4, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Term_2__fromMetaException___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_fget(x_4, x_5);
lean_inc(x_2);
x_10 = l_PersistentArray_foldlMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__2(x_1, x_2, x_9, x_6);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
x_6 = x_10;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = 0;
lean_inc(x_2);
x_11 = l___private_Init_Lean_Elab_Term_1__mkMessageAux(x_2, x_1, x_9, x_10);
x_12 = l_PersistentArray_push___rarg(x_6, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_5 = x_14;
x_6 = x_12;
goto _start;
}
}
}
lean_object* l_PersistentArray_foldlMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__3(x_1, x_2, x_5, x_5, x_6, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__4(x_1, x_2, x_8, x_8, x_9, x_4);
return x_10;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = 0;
lean_inc(x_2);
x_11 = l___private_Init_Lean_Elab_Term_1__mkMessageAux(x_2, x_1, x_9, x_10);
x_12 = l_PersistentArray_push___rarg(x_6, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_5 = x_14;
x_6 = x_12;
goto _start;
}
}
}
lean_object* l_PersistentArray_foldlM___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_2);
x_6 = l_PersistentArray_foldlMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__2(x_1, x_2, x_5, x_4);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__5(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
lean_object* l___private_Init_Lean_Elab_Term_3__fromMetaState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
x_12 = l_PersistentArray_foldlM___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__1(x_1, x_2, x_8, x_10);
lean_dec(x_8);
lean_ctor_set(x_4, 4, x_5);
lean_ctor_set(x_3, 2, x_12);
lean_ctor_set(x_3, 0, x_4);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_ctor_get(x_3, 4);
x_17 = lean_ctor_get(x_3, 5);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_18 = l_PersistentArray_foldlM___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__1(x_1, x_2, x_8, x_14);
lean_dec(x_8);
lean_ctor_set(x_4, 4, x_5);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_16);
lean_ctor_set(x_19, 5, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
x_22 = lean_ctor_get(x_4, 2);
x_23 = lean_ctor_get(x_4, 3);
x_24 = lean_ctor_get(x_4, 4);
x_25 = lean_ctor_get(x_4, 5);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 5);
lean_inc(x_31);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_32 = x_3;
} else {
 lean_dec_ref(x_3);
 x_32 = lean_box(0);
}
x_33 = l_PersistentArray_foldlM___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__1(x_1, x_2, x_26, x_28);
lean_dec(x_26);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_20);
lean_ctor_set(x_34, 1, x_21);
lean_ctor_set(x_34, 2, x_22);
lean_ctor_set(x_34, 3, x_23);
lean_ctor_set(x_34, 4, x_5);
lean_ctor_set(x_34, 5, x_25);
if (lean_is_scalar(x_32)) {
 x_35 = lean_alloc_ctor(0, 6, 0);
} else {
 x_35 = x_32;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_29);
lean_ctor_set(x_35, 4, x_30);
lean_ctor_set(x_35, 5, x_31);
return x_35;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_PersistentArray_foldlMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_foldlMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_PersistentArray_foldlM___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_foldlM___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_Term_3__fromMetaState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_liftMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = lean_apply_2(x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
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
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
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
x_21 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_19);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_20, x_7);
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
x_25 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_24, x_7);
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
x_37 = lean_apply_2(x_2, x_34, x_36);
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
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_39, x_32);
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
x_46 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_43);
x_47 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_44, x_32);
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
lean_object* l_Lean_Elab_Term_liftMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_liftMetaM___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_liftMetaM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_liftMetaM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_ppGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Lean_Meta_ppGoal(x_2, x_8, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
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
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get(x_5, 2);
x_21 = lean_ctor_get(x_5, 3);
x_22 = lean_ctor_get(x_5, 4);
x_23 = lean_ctor_get(x_5, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
x_25 = l_Lean_TraceState_Inhabited___closed__1;
x_26 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_19);
lean_ctor_set(x_26, 2, x_20);
lean_ctor_set(x_26, 3, x_21);
lean_ctor_set(x_26, 4, x_25);
lean_ctor_set(x_26, 5, x_23);
x_27 = l_Lean_Meta_ppGoal(x_2, x_24, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_29, x_22);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
lean_object* l_Lean_Elab_Term_ppGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_ppGoal(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_isDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_6, 4, x_10);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; 
x_14 = 1;
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_14);
lean_ctor_set_uint8(x_12, sizeof(void*)*1 + 1, x_14);
lean_ctor_set_uint8(x_12, sizeof(void*)*1 + 2, x_14);
lean_ctor_set_uint8(x_12, sizeof(void*)*1 + 3, x_14);
x_15 = l_Lean_Meta_isExprDefEq(x_2, x_3, x_9, x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_17, x_8);
lean_ctor_set(x_15, 1, x_18);
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
x_21 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_20, x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_4);
x_26 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_24);
x_27 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_25, x_8);
lean_ctor_set(x_15, 1, x_27);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
lean_inc(x_4);
x_30 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_28);
x_31 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_29, x_8);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_12, 0);
x_34 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 4);
x_35 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 5);
x_36 = lean_ctor_get_uint8(x_12, sizeof(void*)*1 + 6);
lean_inc(x_33);
lean_dec(x_12);
x_37 = 1;
x_38 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 1, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 2, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 3, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 4, x_34);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 5, x_35);
lean_ctor_set_uint8(x_38, sizeof(void*)*1 + 6, x_36);
lean_ctor_set(x_9, 0, x_38);
x_39 = l_Lean_Meta_isExprDefEq(x_2, x_3, x_9, x_6);
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
x_43 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_41, x_8);
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
lean_inc(x_4);
x_48 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_45);
x_49 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_46, x_8);
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_51 = lean_ctor_get(x_9, 0);
x_52 = lean_ctor_get(x_9, 1);
x_53 = lean_ctor_get(x_9, 2);
x_54 = lean_ctor_get(x_9, 3);
x_55 = lean_ctor_get(x_9, 4);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_9);
x_56 = lean_ctor_get(x_51, 0);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_51, sizeof(void*)*1 + 4);
x_58 = lean_ctor_get_uint8(x_51, sizeof(void*)*1 + 5);
x_59 = lean_ctor_get_uint8(x_51, sizeof(void*)*1 + 6);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_60 = x_51;
} else {
 lean_dec_ref(x_51);
 x_60 = lean_box(0);
}
x_61 = 1;
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 1, 7);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*1 + 1, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*1 + 2, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*1 + 3, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*1 + 4, x_57);
lean_ctor_set_uint8(x_62, sizeof(void*)*1 + 5, x_58);
lean_ctor_set_uint8(x_62, sizeof(void*)*1 + 6, x_59);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_52);
lean_ctor_set(x_63, 2, x_53);
lean_ctor_set(x_63, 3, x_54);
lean_ctor_set(x_63, 4, x_55);
x_64 = l_Lean_Meta_isExprDefEq(x_2, x_3, x_63, x_6);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_66, x_8);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_72 = x_64;
} else {
 lean_dec_ref(x_64);
 x_72 = lean_box(0);
}
lean_inc(x_4);
x_73 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_70);
x_74 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_71, x_8);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_72;
}
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_76 = lean_ctor_get(x_6, 0);
x_77 = lean_ctor_get(x_6, 1);
x_78 = lean_ctor_get(x_6, 2);
x_79 = lean_ctor_get(x_6, 3);
x_80 = lean_ctor_get(x_6, 4);
x_81 = lean_ctor_get(x_6, 5);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_6);
x_82 = lean_ctor_get(x_4, 0);
lean_inc(x_82);
x_83 = l_Lean_TraceState_Inhabited___closed__1;
x_84 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_77);
lean_ctor_set(x_84, 2, x_78);
lean_ctor_set(x_84, 3, x_79);
lean_ctor_set(x_84, 4, x_83);
lean_ctor_set(x_84, 5, x_81);
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_82, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_82, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_82, 4);
lean_inc(x_89);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 lean_ctor_release(x_82, 2);
 lean_ctor_release(x_82, 3);
 lean_ctor_release(x_82, 4);
 x_90 = x_82;
} else {
 lean_dec_ref(x_82);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_85, 0);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_85, sizeof(void*)*1 + 4);
x_93 = lean_ctor_get_uint8(x_85, sizeof(void*)*1 + 5);
x_94 = lean_ctor_get_uint8(x_85, sizeof(void*)*1 + 6);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_95 = x_85;
} else {
 lean_dec_ref(x_85);
 x_95 = lean_box(0);
}
x_96 = 1;
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 1, 7);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_91);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*1 + 1, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*1 + 2, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*1 + 3, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*1 + 4, x_92);
lean_ctor_set_uint8(x_97, sizeof(void*)*1 + 5, x_93);
lean_ctor_set_uint8(x_97, sizeof(void*)*1 + 6, x_94);
if (lean_is_scalar(x_90)) {
 x_98 = lean_alloc_ctor(0, 5, 0);
} else {
 x_98 = x_90;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_86);
lean_ctor_set(x_98, 2, x_87);
lean_ctor_set(x_98, 3, x_88);
lean_ctor_set(x_98, 4, x_89);
x_99 = l_Lean_Meta_isExprDefEq(x_2, x_3, x_98, x_84);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
x_103 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_101, x_80);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_100);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = lean_ctor_get(x_99, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_107 = x_99;
} else {
 lean_dec_ref(x_99);
 x_107 = lean_box(0);
}
lean_inc(x_4);
x_108 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_105);
x_109 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_106, x_80);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
lean_object* l_Lean_Elab_Term_isDefEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_isDefEq(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_Meta_inferType(x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
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
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
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
x_21 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_19);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_20, x_7);
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
x_25 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_24, x_7);
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
x_37 = l_Lean_Meta_inferType(x_2, x_34, x_36);
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
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_39, x_32);
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
x_46 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_43);
x_47 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_44, x_32);
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
lean_object* l_Lean_Elab_Term_inferType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_inferType(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_whnf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_Meta_whnf(x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
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
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
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
x_21 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_19);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_20, x_7);
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
x_25 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_24, x_7);
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
x_37 = l_Lean_Meta_whnf(x_2, x_34, x_36);
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
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_39, x_32);
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
x_46 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_43);
x_47 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_44, x_32);
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
lean_object* l_Lean_Elab_Term_whnf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_whnf(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_whnfForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_Meta_whnfForall(x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
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
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
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
x_21 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_19);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_20, x_7);
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
x_25 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_24, x_7);
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
x_37 = l_Lean_Meta_whnfForall(x_2, x_34, x_36);
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
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_39, x_32);
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
x_46 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_43);
x_47 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_44, x_32);
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
lean_object* l_Lean_Elab_Term_whnfForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_whnfForall(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_whnfCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
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
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
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
x_21 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_19);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_20, x_7);
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
x_25 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_24, x_7);
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
x_37 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_2, x_34, x_36);
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
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_39, x_32);
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
x_46 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_43);
x_47 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_44, x_32);
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
lean_object* l_Lean_Elab_Term_whnfCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_whnfCore(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_unfoldDefinition_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
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
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
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
x_21 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_19);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_20, x_7);
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
x_25 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_24, x_7);
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
x_37 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_2, x_34, x_36);
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
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_39, x_32);
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
x_46 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_43);
x_47 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_44, x_32);
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
lean_object* l_Lean_Elab_Term_unfoldDefinition_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_unfoldDefinition_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Lean_Meta_instantiateMVars(x_2, x_8, x_5);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
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
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get(x_5, 2);
x_21 = lean_ctor_get(x_5, 3);
x_22 = lean_ctor_get(x_5, 4);
x_23 = lean_ctor_get(x_5, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
x_25 = l_Lean_TraceState_Inhabited___closed__1;
x_26 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_19);
lean_ctor_set(x_26, 2, x_20);
lean_ctor_set(x_26, 3, x_21);
lean_ctor_set(x_26, 4, x_25);
lean_ctor_set(x_26, 5, x_23);
x_27 = l_Lean_Meta_instantiateMVars(x_2, x_24, x_26);
lean_dec(x_24);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_29, x_22);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
lean_object* l_Lean_Elab_Term_instantiateMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_instantiateMVars(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_isClass(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_Meta_isClass(x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
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
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
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
x_21 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_19);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_20, x_7);
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
x_25 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_24, x_7);
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
x_37 = l_Lean_Meta_isClass(x_2, x_34, x_36);
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
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_39, x_32);
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
x_46 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_43);
x_47 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_44, x_32);
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
lean_object* l_Lean_Elab_Term_isClass___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_isClass(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_7);
x_8 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_2, x_3, x_10, x_6);
lean_ctor_set(x_8, 1, x_11);
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
x_14 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_2, x_3, x_13, x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_4, 2);
x_19 = lean_ctor_get(x_4, 3);
x_20 = lean_ctor_get(x_4, 4);
x_21 = lean_ctor_get(x_4, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_22 = l_Lean_TraceState_Inhabited___closed__1;
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_22);
lean_ctor_set(x_23, 5, x_21);
x_24 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_2, x_3, x_26, x_20);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_mkFreshLevelMVar(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_mkFreshExprMVar(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_21 = l_Lean_Meta_mkFreshExprMVar(x_19, x_4, x_3, x_10, x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_5, x_6, x_23, x_9);
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
x_27 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_5, x_6, x_26, x_9);
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
x_47 = l_Lean_Meta_mkFreshExprMVar(x_45, x_4, x_3, x_35, x_46);
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
x_51 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_5, x_6, x_49, x_33);
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
x_59 = l_Lean_Meta_mkFreshExprMVar(x_54, x_4, x_3, x_57, x_53);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 1);
x_62 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_5, x_6, x_61, x_56);
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
x_65 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_5, x_6, x_64, x_56);
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
x_76 = l_Lean_Meta_mkFreshExprMVar(x_54, x_4, x_3, x_73, x_75);
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
x_80 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_5, x_6, x_78, x_71);
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
lean_object* l_Lean_Elab_Term_mkFreshExprMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_mkFreshTypeMVar(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
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
x_15 = l_Lean_Meta_mkFreshExprMVar(x_14, x_3, x_2, x_9, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_17, x_8);
lean_ctor_set(x_15, 1, x_18);
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
x_21 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_20, x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
x_25 = lean_ctor_get(x_6, 2);
x_26 = lean_ctor_get(x_6, 3);
x_27 = lean_ctor_get(x_6, 4);
x_28 = lean_ctor_get(x_6, 5);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
x_30 = l_Lean_TraceState_Inhabited___closed__1;
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_25);
lean_ctor_set(x_31, 3, x_26);
lean_ctor_set(x_31, 4, x_30);
lean_ctor_set(x_31, 5, x_28);
x_32 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_mkSort(x_33);
x_36 = l_Lean_Meta_mkFreshExprMVar(x_35, x_3, x_2, x_29, x_34);
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
x_40 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_38, x_27);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshTypeMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_Term_mkFreshTypeMVar(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_getLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_Meta_getLevel(x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
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
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
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
x_21 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_19);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_20, x_7);
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
x_25 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_24, x_7);
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
x_37 = l_Lean_Meta_getLevel(x_2, x_34, x_36);
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
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_39, x_32);
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
x_46 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_43);
x_47 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_44, x_32);
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
lean_object* l_Lean_Elab_Term_getLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_getLevel(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_mkForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_6, 4, x_10);
x_11 = l_Lean_Meta_mkForall(x_2, x_3, x_9, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_13, x_8);
lean_ctor_set(x_11, 1, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_16, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_4);
x_22 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_20);
x_23 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_21, x_8);
lean_ctor_set(x_11, 1, x_23);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
lean_inc(x_4);
x_26 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_24);
x_27 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_25, x_8);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_6, 0);
x_30 = lean_ctor_get(x_6, 1);
x_31 = lean_ctor_get(x_6, 2);
x_32 = lean_ctor_get(x_6, 3);
x_33 = lean_ctor_get(x_6, 4);
x_34 = lean_ctor_get(x_6, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_6);
x_35 = lean_ctor_get(x_4, 0);
lean_inc(x_35);
x_36 = l_Lean_TraceState_Inhabited___closed__1;
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_34);
x_38 = l_Lean_Meta_mkForall(x_2, x_3, x_35, x_37);
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
x_42 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_40, x_33);
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
lean_inc(x_4);
x_47 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_44);
x_48 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_45, x_33);
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
}
lean_object* l_Lean_Elab_Term_mkForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_mkForall(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_mkForallUsedOnly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_6, 4, x_10);
x_11 = l_Lean_Meta_mkForallUsedOnly(x_2, x_3, x_9, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_13, x_8);
lean_ctor_set(x_11, 1, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_16, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_4);
x_22 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_20);
x_23 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_21, x_8);
lean_ctor_set(x_11, 1, x_23);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
lean_inc(x_4);
x_26 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_24);
x_27 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_25, x_8);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_6, 0);
x_30 = lean_ctor_get(x_6, 1);
x_31 = lean_ctor_get(x_6, 2);
x_32 = lean_ctor_get(x_6, 3);
x_33 = lean_ctor_get(x_6, 4);
x_34 = lean_ctor_get(x_6, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_6);
x_35 = lean_ctor_get(x_4, 0);
lean_inc(x_35);
x_36 = l_Lean_TraceState_Inhabited___closed__1;
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_34);
x_38 = l_Lean_Meta_mkForallUsedOnly(x_2, x_3, x_35, x_37);
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
x_42 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_40, x_33);
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
lean_inc(x_4);
x_47 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_44);
x_48 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_45, x_33);
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
}
lean_object* l_Lean_Elab_Term_mkForallUsedOnly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_mkForallUsedOnly(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_mkLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_6, 4, x_10);
x_11 = l_Lean_Meta_mkLambda(x_2, x_3, x_9, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_13, x_8);
lean_ctor_set(x_11, 1, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_16, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_4);
x_22 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_20);
x_23 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_21, x_8);
lean_ctor_set(x_11, 1, x_23);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
lean_inc(x_4);
x_26 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_24);
x_27 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_25, x_8);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_6, 0);
x_30 = lean_ctor_get(x_6, 1);
x_31 = lean_ctor_get(x_6, 2);
x_32 = lean_ctor_get(x_6, 3);
x_33 = lean_ctor_get(x_6, 4);
x_34 = lean_ctor_get(x_6, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_6);
x_35 = lean_ctor_get(x_4, 0);
lean_inc(x_35);
x_36 = l_Lean_TraceState_Inhabited___closed__1;
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_34);
x_38 = l_Lean_Meta_mkLambda(x_2, x_3, x_35, x_37);
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
x_42 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_40, x_33);
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
lean_inc(x_4);
x_47 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_44);
x_48 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_45, x_33);
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
}
lean_object* l_Lean_Elab_Term_mkLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_mkLambda(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_mkLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_mkOptionalNode___closed__2;
x_7 = lean_array_push(x_6, x_2);
x_8 = l_Lean_Elab_Term_mkLambda(x_1, x_7, x_3, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_mkLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_mkLet(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_trySynthInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_Meta_trySynthInstance(x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
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
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
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
x_21 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_19);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_20, x_7);
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
x_25 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_24, x_7);
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
x_37 = l_Lean_Meta_trySynthInstance(x_2, x_34, x_36);
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
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_39, x_32);
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
x_46 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_43);
x_47 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_44, x_32);
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
lean_object* l_Lean_Elab_Term_trySynthInstance___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_trySynthInstance(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_mkAppM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_6, 4, x_10);
x_11 = l_Lean_Meta_mkAppM(x_2, x_3, x_9, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_13, x_8);
lean_ctor_set(x_11, 1, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_16, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_4);
x_22 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_20);
x_23 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_21, x_8);
lean_ctor_set(x_11, 1, x_23);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
lean_inc(x_4);
x_26 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_24);
x_27 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_25, x_8);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_6, 0);
x_30 = lean_ctor_get(x_6, 1);
x_31 = lean_ctor_get(x_6, 2);
x_32 = lean_ctor_get(x_6, 3);
x_33 = lean_ctor_get(x_6, 4);
x_34 = lean_ctor_get(x_6, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_6);
x_35 = lean_ctor_get(x_4, 0);
lean_inc(x_35);
x_36 = l_Lean_TraceState_Inhabited___closed__1;
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_34);
x_38 = l_Lean_Meta_mkAppM(x_2, x_3, x_35, x_37);
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
x_42 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_40, x_33);
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
lean_inc(x_4);
x_47 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_44);
x_48 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_45, x_33);
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
}
lean_object* l_Lean_Elab_Term_mkAppM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_mkAppM(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_decLevel_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_Meta_decLevel_x3f(x_2, x_8, x_5);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
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
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
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
x_21 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_19);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_20, x_7);
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
x_25 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_24, x_7);
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
x_37 = l_Lean_Meta_decLevel_x3f(x_2, x_34, x_36);
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
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_39, x_32);
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
x_46 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_43);
x_47 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_44, x_32);
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
lean_object* l_Lean_Elab_Term_decLevel_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_decLevel_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_decLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid universe level, ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_decLevel___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_decLevel___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_decLevel___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_decLevel___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_decLevel___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" is not greater than 0");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_decLevel___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_decLevel___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_decLevel___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_decLevel___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_decLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Elab_Term_decLevel_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = l_Lean_Elab_Term_decLevel___closed__3;
x_10 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Elab_Term_decLevel___closed__6;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Elab_Term_throwError___rarg(x_1, x_12, x_3, x_7);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_3);
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
lean_object* l_Lean_Elab_Term_decLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_decLevel(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_liftLevelM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_2, 6);
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
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Level_elabLevel___boxed), 3, 1);
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
lean_object* l_Lean_Elab_Term_withMacroExpansion___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 8);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_4, 8, x_9);
x_10 = lean_apply_2(x_3, x_4, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
x_15 = lean_ctor_get(x_4, 4);
x_16 = lean_ctor_get(x_4, 5);
x_17 = lean_ctor_get(x_4, 6);
x_18 = lean_ctor_get(x_4, 7);
x_19 = lean_ctor_get(x_4, 8);
x_20 = lean_ctor_get(x_4, 9);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_22 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
lean_inc(x_20);
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
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_2);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
x_25 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_12);
lean_ctor_set(x_25, 2, x_13);
lean_ctor_set(x_25, 3, x_14);
lean_ctor_set(x_25, 4, x_15);
lean_ctor_set(x_25, 5, x_16);
lean_ctor_set(x_25, 6, x_17);
lean_ctor_set(x_25, 7, x_18);
lean_ctor_set(x_25, 8, x_24);
lean_ctor_set(x_25, 9, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*10, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*10 + 1, x_22);
x_26 = lean_apply_2(x_3, x_25, x_5);
return x_26;
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
lean_object* l_Lean_Elab_Term_registerSyntheticMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 2, x_3);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_5, 1, x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get(x_5, 5);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set(x_18, 2, x_3);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
x_20 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_14);
lean_ctor_set(x_20, 3, x_15);
lean_ctor_set(x_20, 4, x_16);
lean_ctor_set(x_20, 5, x_17);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_Elab_Term_registerSyntheticMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_registerSyntheticMVar(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
lean_inc(x_16);
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
x_18 = 0;
x_19 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_8);
lean_ctor_set(x_19, 2, x_9);
lean_ctor_set(x_19, 3, x_10);
lean_ctor_set(x_19, 4, x_11);
lean_ctor_set(x_19, 5, x_12);
lean_ctor_set(x_19, 6, x_13);
lean_ctor_set(x_19, 7, x_14);
lean_ctor_set(x_19, 8, x_15);
lean_ctor_set(x_19, 9, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*10, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*10 + 1, x_17);
x_20 = lean_apply_2(x_1, x_19, x_3);
return x_20;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_termIdToAntiquot___closed__4;
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
x_10 = l_Lean_Elab_Term_mkExplicitBinder___closed__5;
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
x_3 = lean_ctor_get(x_1, 6);
x_4 = l_List_elem___main___at_Lean_addAliasEntry___spec__18(x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_levelMVarToParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("u");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_levelMVarToParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_levelMVarToParam___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_getMCtx___rarg(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Term_levelMVarToParam___lambda__1___boxed), 2, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_Elab_Term_levelMVarToParam___closed__2;
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_MetavarContext_levelMVarToParam(x_6, x_8, x_1, x_9, x_10);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_ctor_set(x_13, 1, x_16);
x_17 = lean_ctor_get(x_11, 3);
lean_inc(x_17);
lean_dec(x_11);
lean_ctor_set(x_4, 0, x_17);
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 2);
x_20 = lean_ctor_get(x_13, 3);
x_21 = lean_ctor_get(x_13, 4);
x_22 = lean_ctor_get(x_13, 5);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_21);
lean_ctor_set(x_24, 5, x_22);
lean_ctor_set(x_7, 0, x_24);
x_25 = lean_ctor_get(x_11, 3);
lean_inc(x_25);
lean_dec(x_11);
lean_ctor_set(x_4, 0, x_25);
return x_4;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
x_28 = lean_ctor_get(x_7, 2);
x_29 = lean_ctor_get(x_7, 3);
x_30 = lean_ctor_get(x_7, 4);
x_31 = lean_ctor_get(x_7, 5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_26, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_26, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_26, 5);
lean_inc(x_36);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 lean_ctor_release(x_26, 5);
 x_37 = x_26;
} else {
 lean_dec_ref(x_26);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_11, 0);
lean_inc(x_38);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 6, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_33);
lean_ctor_set(x_39, 3, x_34);
lean_ctor_set(x_39, 4, x_35);
lean_ctor_set(x_39, 5, x_36);
x_40 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_27);
lean_ctor_set(x_40, 2, x_28);
lean_ctor_set(x_40, 3, x_29);
lean_ctor_set(x_40, 4, x_30);
lean_ctor_set(x_40, 5, x_31);
x_41 = lean_ctor_get(x_11, 3);
lean_inc(x_41);
lean_dec(x_11);
lean_ctor_set(x_4, 1, x_40);
lean_ctor_set(x_4, 0, x_41);
return x_4;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_42 = lean_ctor_get(x_4, 0);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_4);
x_44 = lean_alloc_closure((void*)(l_Lean_Elab_Term_levelMVarToParam___lambda__1___boxed), 2, 1);
lean_closure_set(x_44, 0, x_2);
x_45 = l_Lean_Elab_Term_levelMVarToParam___closed__2;
x_46 = lean_unsigned_to_nat(1u);
x_47 = l_Lean_MetavarContext_levelMVarToParam(x_42, x_44, x_1, x_45, x_46);
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_43, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_43, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_43, 4);
lean_inc(x_52);
x_53 = lean_ctor_get(x_43, 5);
lean_inc(x_53);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 lean_ctor_release(x_43, 4);
 lean_ctor_release(x_43, 5);
 x_54 = x_43;
} else {
 lean_dec_ref(x_43);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_48, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_48, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_48, 4);
lean_inc(x_58);
x_59 = lean_ctor_get(x_48, 5);
lean_inc(x_59);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 lean_ctor_release(x_48, 4);
 lean_ctor_release(x_48, 5);
 x_60 = x_48;
} else {
 lean_dec_ref(x_48);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 6, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_56);
lean_ctor_set(x_62, 3, x_57);
lean_ctor_set(x_62, 4, x_58);
lean_ctor_set(x_62, 5, x_59);
if (lean_is_scalar(x_54)) {
 x_63 = lean_alloc_ctor(0, 6, 0);
} else {
 x_63 = x_54;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_49);
lean_ctor_set(x_63, 2, x_50);
lean_ctor_set(x_63, 3, x_51);
lean_ctor_set(x_63, 4, x_52);
lean_ctor_set(x_63, 5, x_53);
x_64 = lean_ctor_get(x_47, 3);
lean_inc(x_64);
lean_dec(x_47);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
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
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_ctor_set(x_1, 4, x_5);
x_6 = l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__2;
x_7 = l_Lean_Name_appendIndexAfter(x_6, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
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
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_13, x_15);
x_17 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_11);
lean_ctor_set(x_17, 3, x_12);
lean_ctor_set(x_17, 4, x_16);
lean_ctor_set(x_17, 5, x_14);
x_18 = l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__2;
x_19 = l_Lean_Name_appendIndexAfter(x_18, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
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
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_ctor_set(x_1, 3, x_5);
x_6 = l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__2;
x_7 = l_Lean_Name_appendIndexAfter(x_6, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
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
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_12, x_15);
x_17 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_11);
lean_ctor_set(x_17, 3, x_16);
lean_ctor_set(x_17, 4, x_13);
lean_ctor_set(x_17, 5, x_14);
x_18 = l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__2;
x_19 = l_Lean_Name_appendIndexAfter(x_18, x_12);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
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
uint8_t _init_l___private_Init_Lean_Elab_Term_4__isCDot___closed__1() {
_start:
{
uint8_t x_1; 
x_1 = l_String_posOfAux___main___closed__1;
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
uint8_t l___private_Init_Lean_Elab_Term_4__isCDot(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Parser_Term_cdot___elambda__1___closed__2;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = l___private_Init_Lean_Elab_Term_4__isCDot___closed__1;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_5 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_6 = lean_array_get_size(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
x_9 = l_coeDecidableEq(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_4__isCDot___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elab_Term_4__isCDot(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_5__expandCDot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_Prim_fopenFlags___closed__12;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_5__expandCDot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_IO_Prim_fopenFlags___closed__12;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Init_Lean_Elab_Term_5__expandCDot___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_5__expandCDot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_IO_Prim_fopenFlags___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_5__expandCDot___closed__4() {
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
lean_object* l___private_Init_Lean_Elab_Term_5__expandCDot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_5 = l_Lean_Parser_Term_cdot___elambda__1___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_4, 5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_ctor_set(x_4, 5, x_10);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 9);
lean_dec(x_12);
lean_ctor_set(x_3, 9, x_8);
if (x_6 == 0)
{
uint8_t x_72; 
x_72 = l_String_posOfAux___main___closed__1;
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_3);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_2);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_4);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_1);
x_75 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
lean_dec(x_3);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_2);
x_13 = x_78;
x_14 = x_77;
goto block_71;
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; 
x_79 = l_Lean_Syntax_getArgs(x_1);
x_80 = lean_array_get_size(x_79);
lean_dec(x_79);
x_81 = lean_nat_dec_eq(x_80, x_9);
lean_dec(x_80);
x_82 = l_coeDecidableEq(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_3);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_2);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_4);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_1);
x_85 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
lean_dec(x_3);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_2);
x_13 = x_88;
x_14 = x_87;
goto block_71;
}
}
block_71:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = l_Lean_Elab_Term_getMainModule___rarg(x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_box(0);
x_22 = l___private_Init_Lean_Elab_Term_5__expandCDot___closed__3;
x_23 = l_Lean_addMacroScope(x_20, x_22, x_16);
x_24 = lean_box(0);
x_25 = l___private_Init_Lean_Elab_Term_5__expandCDot___closed__2;
x_26 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_24);
x_27 = l_Array_empty___closed__1;
x_28 = lean_array_push(x_27, x_26);
x_29 = l___private_Init_Lean_Elab_Term_5__expandCDot___closed__4;
x_30 = lean_array_push(x_28, x_29);
x_31 = l_Lean_mkTermIdFromIdent___closed__2;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
lean_inc(x_32);
x_33 = lean_array_push(x_17, x_32);
lean_ctor_set(x_13, 1, x_33);
lean_ctor_set(x_13, 0, x_32);
lean_ctor_set(x_18, 0, x_13);
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_box(0);
x_37 = l___private_Init_Lean_Elab_Term_5__expandCDot___closed__3;
x_38 = l_Lean_addMacroScope(x_34, x_37, x_16);
x_39 = lean_box(0);
x_40 = l___private_Init_Lean_Elab_Term_5__expandCDot___closed__2;
x_41 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_38);
lean_ctor_set(x_41, 3, x_39);
x_42 = l_Array_empty___closed__1;
x_43 = lean_array_push(x_42, x_41);
x_44 = l___private_Init_Lean_Elab_Term_5__expandCDot___closed__4;
x_45 = lean_array_push(x_43, x_44);
x_46 = l_Lean_mkTermIdFromIdent___closed__2;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
lean_inc(x_47);
x_48 = lean_array_push(x_17, x_47);
lean_ctor_set(x_13, 1, x_48);
lean_ctor_set(x_13, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_13);
lean_ctor_set(x_49, 1, x_35);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_50 = lean_ctor_get(x_13, 0);
x_51 = lean_ctor_get(x_13, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_13);
x_52 = l_Lean_Elab_Term_getMainModule___rarg(x_14);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_box(0);
x_57 = l___private_Init_Lean_Elab_Term_5__expandCDot___closed__3;
x_58 = l_Lean_addMacroScope(x_53, x_57, x_50);
x_59 = lean_box(0);
x_60 = l___private_Init_Lean_Elab_Term_5__expandCDot___closed__2;
x_61 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_58);
lean_ctor_set(x_61, 3, x_59);
x_62 = l_Array_empty___closed__1;
x_63 = lean_array_push(x_62, x_61);
x_64 = l___private_Init_Lean_Elab_Term_5__expandCDot___closed__4;
x_65 = lean_array_push(x_63, x_64);
x_66 = l_Lean_mkTermIdFromIdent___closed__2;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
lean_inc(x_67);
x_68 = lean_array_push(x_51, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
if (lean_is_scalar(x_55)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_55;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_54);
return x_70;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_89 = lean_ctor_get(x_3, 0);
x_90 = lean_ctor_get(x_3, 1);
x_91 = lean_ctor_get(x_3, 2);
x_92 = lean_ctor_get(x_3, 3);
x_93 = lean_ctor_get(x_3, 4);
x_94 = lean_ctor_get(x_3, 5);
x_95 = lean_ctor_get(x_3, 6);
x_96 = lean_ctor_get(x_3, 7);
x_97 = lean_ctor_get(x_3, 8);
x_98 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_99 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_3);
x_100 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_100, 0, x_89);
lean_ctor_set(x_100, 1, x_90);
lean_ctor_set(x_100, 2, x_91);
lean_ctor_set(x_100, 3, x_92);
lean_ctor_set(x_100, 4, x_93);
lean_ctor_set(x_100, 5, x_94);
lean_ctor_set(x_100, 6, x_95);
lean_ctor_set(x_100, 7, x_96);
lean_ctor_set(x_100, 8, x_97);
lean_ctor_set(x_100, 9, x_8);
lean_ctor_set_uint8(x_100, sizeof(void*)*10, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*10 + 1, x_99);
if (x_6 == 0)
{
uint8_t x_126; 
x_126 = l_String_posOfAux___main___closed__1;
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_100);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_1);
lean_ctor_set(x_127, 1, x_2);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_4);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_1);
x_129 = l_Lean_Elab_Term_getCurrMacroScope(x_100, x_4);
lean_dec(x_100);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_2);
x_101 = x_132;
x_102 = x_131;
goto block_125;
}
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_136; 
x_133 = l_Lean_Syntax_getArgs(x_1);
x_134 = lean_array_get_size(x_133);
lean_dec(x_133);
x_135 = lean_nat_dec_eq(x_134, x_9);
lean_dec(x_134);
x_136 = l_coeDecidableEq(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_100);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_1);
lean_ctor_set(x_137, 1, x_2);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_4);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_1);
x_139 = l_Lean_Elab_Term_getCurrMacroScope(x_100, x_4);
lean_dec(x_100);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_2);
x_101 = x_142;
x_102 = x_141;
goto block_125;
}
}
block_125:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_105 = x_101;
} else {
 lean_dec_ref(x_101);
 x_105 = lean_box(0);
}
x_106 = l_Lean_Elab_Term_getMainModule___rarg(x_102);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
x_111 = l___private_Init_Lean_Elab_Term_5__expandCDot___closed__3;
x_112 = l_Lean_addMacroScope(x_107, x_111, x_103);
x_113 = lean_box(0);
x_114 = l___private_Init_Lean_Elab_Term_5__expandCDot___closed__2;
x_115 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_115, 2, x_112);
lean_ctor_set(x_115, 3, x_113);
x_116 = l_Array_empty___closed__1;
x_117 = lean_array_push(x_116, x_115);
x_118 = l___private_Init_Lean_Elab_Term_5__expandCDot___closed__4;
x_119 = lean_array_push(x_117, x_118);
x_120 = l_Lean_mkTermIdFromIdent___closed__2;
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
lean_inc(x_121);
x_122 = lean_array_push(x_104, x_121);
if (lean_is_scalar(x_105)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_105;
}
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
if (lean_is_scalar(x_109)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_109;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_108);
return x_124;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_143 = lean_ctor_get(x_4, 0);
x_144 = lean_ctor_get(x_4, 1);
x_145 = lean_ctor_get(x_4, 2);
x_146 = lean_ctor_get(x_4, 3);
x_147 = lean_ctor_get(x_4, 4);
x_148 = lean_ctor_get(x_4, 5);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_4);
x_149 = lean_unsigned_to_nat(1u);
x_150 = lean_nat_add(x_148, x_149);
x_151 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_151, 0, x_143);
lean_ctor_set(x_151, 1, x_144);
lean_ctor_set(x_151, 2, x_145);
lean_ctor_set(x_151, 3, x_146);
lean_ctor_set(x_151, 4, x_147);
lean_ctor_set(x_151, 5, x_150);
x_152 = lean_ctor_get(x_3, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_3, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_3, 2);
lean_inc(x_154);
x_155 = lean_ctor_get(x_3, 3);
lean_inc(x_155);
x_156 = lean_ctor_get(x_3, 4);
lean_inc(x_156);
x_157 = lean_ctor_get(x_3, 5);
lean_inc(x_157);
x_158 = lean_ctor_get(x_3, 6);
lean_inc(x_158);
x_159 = lean_ctor_get(x_3, 7);
lean_inc(x_159);
x_160 = lean_ctor_get(x_3, 8);
lean_inc(x_160);
x_161 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_162 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 lean_ctor_release(x_3, 9);
 x_163 = x_3;
} else {
 lean_dec_ref(x_3);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 10, 2);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_152);
lean_ctor_set(x_164, 1, x_153);
lean_ctor_set(x_164, 2, x_154);
lean_ctor_set(x_164, 3, x_155);
lean_ctor_set(x_164, 4, x_156);
lean_ctor_set(x_164, 5, x_157);
lean_ctor_set(x_164, 6, x_158);
lean_ctor_set(x_164, 7, x_159);
lean_ctor_set(x_164, 8, x_160);
lean_ctor_set(x_164, 9, x_148);
lean_ctor_set_uint8(x_164, sizeof(void*)*10, x_161);
lean_ctor_set_uint8(x_164, sizeof(void*)*10 + 1, x_162);
if (x_6 == 0)
{
uint8_t x_190; 
x_190 = l_String_posOfAux___main___closed__1;
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_164);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_1);
lean_ctor_set(x_191, 1, x_2);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_151);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_1);
x_193 = l_Lean_Elab_Term_getCurrMacroScope(x_164, x_151);
lean_dec(x_164);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_2);
x_165 = x_196;
x_166 = x_195;
goto block_189;
}
}
else
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_200; 
x_197 = l_Lean_Syntax_getArgs(x_1);
x_198 = lean_array_get_size(x_197);
lean_dec(x_197);
x_199 = lean_nat_dec_eq(x_198, x_149);
lean_dec(x_198);
x_200 = l_coeDecidableEq(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_164);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_1);
lean_ctor_set(x_201, 1, x_2);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_151);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_1);
x_203 = l_Lean_Elab_Term_getCurrMacroScope(x_164, x_151);
lean_dec(x_164);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_2);
x_165 = x_206;
x_166 = x_205;
goto block_189;
}
}
block_189:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_167 = lean_ctor_get(x_165, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_169 = x_165;
} else {
 lean_dec_ref(x_165);
 x_169 = lean_box(0);
}
x_170 = l_Lean_Elab_Term_getMainModule___rarg(x_166);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
x_174 = lean_box(0);
x_175 = l___private_Init_Lean_Elab_Term_5__expandCDot___closed__3;
x_176 = l_Lean_addMacroScope(x_171, x_175, x_167);
x_177 = lean_box(0);
x_178 = l___private_Init_Lean_Elab_Term_5__expandCDot___closed__2;
x_179 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_179, 0, x_174);
lean_ctor_set(x_179, 1, x_178);
lean_ctor_set(x_179, 2, x_176);
lean_ctor_set(x_179, 3, x_177);
x_180 = l_Array_empty___closed__1;
x_181 = lean_array_push(x_180, x_179);
x_182 = l___private_Init_Lean_Elab_Term_5__expandCDot___closed__4;
x_183 = lean_array_push(x_181, x_182);
x_184 = l_Lean_mkTermIdFromIdent___closed__2;
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
lean_inc(x_185);
x_186 = lean_array_push(x_168, x_185);
if (lean_is_scalar(x_169)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_169;
}
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
if (lean_is_scalar(x_173)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_173;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_172);
return x_188;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_expandCDot_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l___private_Init_Lean_Elab_Term_4__isCDot(x_7);
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
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_expandCDot_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = x_2;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = lean_array_fget(x_2, x_1);
x_13 = lean_box(0);
x_14 = x_13;
x_15 = lean_array_fset(x_2, x_1, x_14);
lean_inc(x_4);
lean_inc(x_12);
x_16 = l___private_Init_Lean_Elab_Term_5__expandCDot(x_12, x_3, x_4, x_5);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_1, x_21);
x_23 = x_19;
lean_dec(x_12);
x_24 = lean_array_fset(x_15, x_1, x_23);
lean_dec(x_1);
x_1 = x_22;
x_2 = x_24;
x_3 = x_20;
x_5 = x_18;
goto _start;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_expandCDot_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l___private_Init_Lean_Elab_Term_4__isCDot(x_7);
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
lean_object* _init_l_Lean_Elab_Term_expandCDot_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_darrow___elambda__1___rarg___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandCDot_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_142; uint8_t x_143; 
x_142 = l_Lean_mkAppStx___closed__8;
lean_inc(x_1);
x_143 = l_Lean_Syntax_isOfKind(x_1, x_142);
if (x_143 == 0)
{
uint8_t x_144; 
x_144 = 0;
x_4 = x_144;
goto block_141;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_145 = l_Lean_Syntax_getArgs(x_1);
x_146 = lean_array_get_size(x_145);
lean_dec(x_145);
x_147 = lean_unsigned_to_nat(2u);
x_148 = lean_nat_dec_eq(x_146, x_147);
lean_dec(x_146);
x_4 = x_148;
goto block_141;
}
block_141:
{
uint8_t x_5; 
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_expandCDot_x3f___spec__1(x_8, x_8, x_9, x_10);
lean_dec(x_9);
x_12 = l_coeDecidableEq(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_15 = l_Array_empty___closed__1;
lean_inc(x_2);
x_16 = l_Array_umapMAux___main___at_Lean_Elab_Term_expandCDot_x3f___spec__2(x_10, x_8, x_15, x_2, x_3);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_1, 1, x_19);
x_21 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_18);
lean_dec(x_2);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Term_getMainModule___rarg(x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_20, x_20, x_10, x_15);
lean_dec(x_20);
x_27 = l_Lean_nullKind___closed__2;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_30 = lean_array_push(x_29, x_28);
x_31 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_32 = lean_array_push(x_30, x_31);
x_33 = lean_array_push(x_32, x_1);
x_34 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_23, 0, x_36);
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_dec(x_23);
x_38 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_20, x_20, x_10, x_15);
lean_dec(x_20);
x_39 = l_Lean_nullKind___closed__2;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_42 = lean_array_push(x_41, x_40);
x_43 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_44 = lean_array_push(x_42, x_43);
x_45 = lean_array_push(x_44, x_1);
x_46 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_37);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_1, 0);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_1);
x_52 = lean_array_get_size(x_51);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_expandCDot_x3f___spec__1(x_51, x_51, x_52, x_53);
lean_dec(x_52);
x_55 = l_coeDecidableEq(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_2);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_3);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_58 = l_Array_empty___closed__1;
lean_inc(x_2);
x_59 = l_Array_umapMAux___main___at_Lean_Elab_Term_expandCDot_x3f___spec__2(x_53, x_51, x_58, x_2, x_3);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_50);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_61);
lean_dec(x_2);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = l_Lean_Elab_Term_getMainModule___rarg(x_66);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
x_70 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_63, x_63, x_53, x_58);
lean_dec(x_63);
x_71 = l_Lean_nullKind___closed__2;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_74 = lean_array_push(x_73, x_72);
x_75 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_76 = lean_array_push(x_74, x_75);
x_77 = lean_array_push(x_76, x_64);
x_78 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
if (lean_is_scalar(x_69)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_69;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_68);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_2);
lean_dec(x_1);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_3);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_91; 
x_84 = lean_unsigned_to_nat(0u);
x_85 = l_Lean_Syntax_getArg(x_1, x_84);
x_86 = lean_unsigned_to_nat(1u);
x_87 = l_Lean_Syntax_getArg(x_1, x_86);
x_88 = l_Lean_Syntax_getArgs(x_87);
lean_dec(x_87);
x_89 = lean_array_get_size(x_88);
x_90 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_expandCDot_x3f___spec__3(x_1, x_88, x_89, x_84);
lean_dec(x_89);
lean_dec(x_1);
x_91 = l_coeDecidableEq(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_88);
lean_dec(x_85);
lean_dec(x_2);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_3);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_94 = l_Array_empty___closed__1;
lean_inc(x_2);
x_95 = l_Array_umapMAux___main___at_Lean_Elab_Term_expandCDot_x3f___spec__2(x_84, x_88, x_94, x_2, x_3);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_97);
lean_dec(x_2);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = l_Lean_Elab_Term_getMainModule___rarg(x_101);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_104 = lean_ctor_get(x_102, 0);
lean_dec(x_104);
x_105 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_99, x_99, x_84, x_94);
lean_dec(x_99);
x_106 = l_Lean_nullKind___closed__2;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_109 = lean_array_push(x_108, x_107);
x_110 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_111 = lean_array_push(x_109, x_110);
x_112 = lean_array_push(x_94, x_85);
x_113 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_98, x_98, x_84, x_94);
lean_dec(x_98);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_array_push(x_112, x_114);
x_116 = l_Lean_mkAppStx___closed__8;
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = lean_array_push(x_111, x_117);
x_119 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_102, 0, x_121);
return x_102;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_122 = lean_ctor_get(x_102, 1);
lean_inc(x_122);
lean_dec(x_102);
x_123 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_99, x_99, x_84, x_94);
lean_dec(x_99);
x_124 = l_Lean_nullKind___closed__2;
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_127 = lean_array_push(x_126, x_125);
x_128 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_129 = lean_array_push(x_127, x_128);
x_130 = lean_array_push(x_94, x_85);
x_131 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_98, x_98, x_84, x_94);
lean_dec(x_98);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_124);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_array_push(x_130, x_132);
x_134 = l_Lean_mkAppStx___closed__8;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = lean_array_push(x_129, x_135);
x_137 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_122);
return x_140;
}
}
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_expandCDot_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_expandCDot_x3f___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_expandCDot_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_expandCDot_x3f___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_isSyntheticSorry___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__1;
x_2 = l_Bool_HasRepr___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Term_6__exceptionToSorry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = 0;
x_60 = lean_box(0);
lean_inc(x_4);
x_61 = l_Lean_Elab_Term_mkFreshTypeMVar(x_1, x_59, x_60, x_4, x_5);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_6 = x_62;
x_7 = x_63;
goto block_58;
}
else
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_3, 0);
lean_inc(x_64);
lean_dec(x_3);
x_6 = x_64;
x_7 = x_5;
goto block_58;
}
block_58:
{
lean_object* x_8; 
lean_inc(x_6);
x_8 = l_Lean_Elab_Term_getLevel(x_1, x_6, x_4, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Expr_hasSorry___main___closed__1;
x_15 = l_Lean_mkConst(x_14, x_13);
x_16 = l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__3;
x_17 = l_Lean_mkAppB(x_15, x_6, x_16);
x_18 = lean_ctor_get(x_2, 4);
lean_inc(x_18);
x_19 = l_Lean_MessageData_hasSyntheticSorry___main(x_18);
lean_dec(x_18);
x_20 = l_coeDecidableEq(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_11, 2);
x_23 = l_PersistentArray_push___rarg(x_22, x_2);
lean_ctor_set(x_11, 2, x_23);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 2);
x_27 = lean_ctor_get(x_11, 3);
x_28 = lean_ctor_get(x_11, 4);
x_29 = lean_ctor_get(x_11, 5);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_30 = l_PersistentArray_push___rarg(x_26, x_2);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_27);
lean_ctor_set(x_31, 4, x_28);
lean_ctor_set(x_31, 5, x_29);
lean_ctor_set(x_8, 1, x_31);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
}
else
{
lean_dec(x_2);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Expr_hasSorry___main___closed__1;
x_37 = l_Lean_mkConst(x_36, x_35);
x_38 = l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__3;
x_39 = l_Lean_mkAppB(x_37, x_6, x_38);
x_40 = lean_ctor_get(x_2, 4);
lean_inc(x_40);
x_41 = l_Lean_MessageData_hasSyntheticSorry___main(x_40);
lean_dec(x_40);
x_42 = l_coeDecidableEq(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_33, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_33, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_33, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_33, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_33, 5);
lean_inc(x_48);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 lean_ctor_release(x_33, 3);
 lean_ctor_release(x_33, 4);
 lean_ctor_release(x_33, 5);
 x_49 = x_33;
} else {
 lean_dec_ref(x_33);
 x_49 = lean_box(0);
}
x_50 = l_PersistentArray_push___rarg(x_45, x_2);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 6, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_44);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_51, 3, x_46);
lean_ctor_set(x_51, 4, x_47);
lean_ctor_set(x_51, 5, x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_39);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
else
{
lean_object* x_53; 
lean_dec(x_2);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_39);
lean_ctor_set(x_53, 1, x_33);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_6);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_8);
if (x_54 == 0)
{
return x_8;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_8, 0);
x_56 = lean_ctor_get(x_8, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_8);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_6__exceptionToSorry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Term_6__exceptionToSorry(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_tryPostpone(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*10);
x_4 = l_coeDecidableEq(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
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
lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_4 = l_Lean_Expr_getAppFn___main(x_1);
x_5 = l_Lean_Expr_isMVar(x_4);
lean_dec(x_4);
x_6 = l_coeDecidableEq(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_tryPostpone(x_2, x_3);
return x_9;
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
lean_object* _init_l___private_Init_Lean_Elab_Term_7__postponeElabTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("postpone");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_7__postponeElabTerm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__1;
x_2 = l___private_Init_Lean_Elab_Term_7__postponeElabTerm___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Term_7__postponeElabTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_20 = l_Lean_Elab_Term_getOptions(x_3, x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Init_Lean_Elab_Term_7__postponeElabTerm___closed__2;
x_24 = l_Lean_checkTraceOption(x_21, x_23);
lean_dec(x_21);
x_25 = l_coeDecidableEq(x_24);
if (x_25 == 0)
{
x_5 = x_22;
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_inc(x_1);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_1);
x_27 = l___private_Init_Lean_Meta_ExprDefEq_17__checkTypesAndAssign___closed__5;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = l_Lean_MessageData_coeOfOptExpr___closed__1;
x_30 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Elab_Term_logTrace(x_23, x_1, x_30, x_3, x_22);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_5 = x_32;
goto block_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Elab_Term_logTrace(x_23, x_1, x_35, x_3, x_22);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_5 = x_37;
goto block_19;
}
}
block_19:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = 2;
x_7 = lean_box(0);
lean_inc(x_3);
x_8 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_2, x_6, x_7, x_3, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_mvarId_x21(x_9);
x_12 = lean_ctor_get(x_3, 8);
lean_inc(x_12);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_Elab_Term_registerSyntheticMVar(x_1, x_11, x_13, x_3, x_10);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_9);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected syntax");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_8__elabTermUsing___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_2);
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
x_14 = l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__3;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_Term_throwError___rarg(x_2, x_15, x_6, x_7);
lean_dec(x_2);
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
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
x_27 = l_coeDecidableEq(x_26);
if (x_27 == 0)
{
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
else
{
lean_object* x_28; 
lean_free_object(x_19);
lean_dec(x_20);
x_28 = l___private_Init_Lean_Elab_Term_6__exceptionToSorry(x_2, x_25, x_3, x_6, x_23);
lean_dec(x_2);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
x_32 = l_coeDecidableEq(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_20);
x_34 = l___private_Init_Lean_Elab_Term_6__exceptionToSorry(x_2, x_30, x_3, x_6, x_29);
lean_dec(x_2);
return x_34;
}
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
uint8_t x_36; 
lean_dec(x_18);
x_36 = !lean_is_exclusive(x_19);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_19, 1);
x_38 = lean_ctor_get(x_19, 0);
lean_dec(x_38);
x_39 = l_coeDecidableEq(x_4);
if (x_39 == 0)
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
else
{
lean_object* x_40; 
lean_free_object(x_19);
lean_dec(x_37);
x_40 = l___private_Init_Lean_Elab_Term_7__postponeElabTerm(x_2, x_3, x_6, x_1);
return x_40;
}
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_dec(x_19);
x_42 = l_coeDecidableEq(x_4);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_20);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
else
{
lean_object* x_44; 
lean_dec(x_41);
x_44 = l___private_Init_Lean_Elab_Term_7__postponeElabTerm(x_2, x_3, x_6, x_1);
return x_44;
}
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Lean_Elab_Term_8__elabTermUsing___main(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Init_Lean_Elab_Term_8__elabTermUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Term_8__elabTermUsing___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Term_8__elabTermUsing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Lean_Elab_Term_8__elabTermUsing(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
return x_9;
}
}
lean_object* _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getEnv___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwError), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwUnsupportedSyntax___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__1;
x_2 = l_Lean_Elab_Term_monadQuotation___closed__1;
x_3 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__2;
x_4 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__4;
return x_1;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabTermAux___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTermAux___main___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
}
case 1:
{
lean_object* x_17; size_t x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = x_2 >> x_5;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabTermAux___main___spec__4(x_21, x_22, lean_box(0), x_23, x_3);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
}
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTermAux___main___spec__3(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_Term_elabTermAux___main___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_Elab_Term_elabTermAux___main___spec__6(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_PersistentHashMap_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_HashMapImp_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__5(x_4, x_2);
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
x_9 = l_HashMapImp_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__5(x_8, x_2);
lean_dec(x_8);
return x_9;
}
}
}
lean_object* _init_l_Lean_Elab_Term_elabTermAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elaboration function for '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabTermAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabTermAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabTermAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabTermAux___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabTermAux___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has not been implemented");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabTermAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabTermAux___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabTermAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabTermAux___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabTermAux___main(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_ctor_set(x_5, 5, x_9);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_177; lean_object* x_178; uint8_t x_179; uint8_t x_180; 
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
x_22 = lean_ctor_get(x_4, 9);
lean_dec(x_22);
lean_inc(x_7);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_ctor_set(x_4, 9, x_7);
x_177 = lean_ctor_get(x_11, 3);
lean_inc(x_177);
x_178 = lean_ctor_get(x_11, 4);
lean_inc(x_178);
x_179 = lean_nat_dec_eq(x_177, x_178);
lean_dec(x_178);
lean_dec(x_177);
x_180 = l_coeDecidableEq(x_179);
if (x_180 == 0)
{
lean_dec(x_4);
x_23 = x_5;
goto block_176;
}
else
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_1);
x_181 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
x_182 = l_Lean_Elab_Term_throwError___rarg(x_3, x_181, x_4, x_5);
lean_dec(x_3);
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
return x_182;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_182, 0);
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_182);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
block_176:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_94; 
x_25 = lean_ctor_get(x_11, 3);
x_26 = lean_nat_add(x_25, x_8);
lean_dec(x_25);
lean_ctor_set(x_11, 3, x_26);
lean_inc(x_7);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_27 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_27, 0, x_11);
lean_ctor_set(x_27, 1, x_12);
lean_ctor_set(x_27, 2, x_13);
lean_ctor_set(x_27, 3, x_14);
lean_ctor_set(x_27, 4, x_15);
lean_ctor_set(x_27, 5, x_16);
lean_ctor_set(x_27, 6, x_17);
lean_ctor_set(x_27, 7, x_18);
lean_ctor_set(x_27, 8, x_19);
lean_ctor_set(x_27, 9, x_7);
lean_ctor_set_uint8(x_27, sizeof(void*)*10, x_20);
lean_ctor_set_uint8(x_27, sizeof(void*)*10 + 1, x_21);
x_89 = l_Lean_Elab_Term_getOptions(x_27, x_23);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__3;
x_93 = l_Lean_checkTraceOption(x_90, x_92);
lean_dec(x_90);
x_94 = l_coeDecidableEq(x_93);
if (x_94 == 0)
{
x_28 = x_91;
goto block_88;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_inc(x_3);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_3);
x_96 = l_Lean_Elab_Term_logTrace(x_92, x_3, x_95, x_27, x_91);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_28 = x_97;
goto block_88;
}
block_88:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = l_Lean_Elab_Term_termElabAttribute;
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_PersistentEnvExtension_getState___rarg(x_30, x_32);
lean_dec(x_32);
lean_dec(x_30);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_3);
x_35 = l_Lean_Syntax_getKind(x_3);
x_36 = l_Lean_SMap_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__1(x_34, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_48; lean_object* x_49; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_37 = l_Lean_Elab_Term_getEnv___rarg(x_28);
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
x_66 = l_Lean_Elab_Term_getCurrMacroScope(x_27, x_39);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Elab_Term_getEnv___rarg(x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_environment_main_module(x_70);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_67);
lean_inc(x_3);
x_74 = l_Lean_Elab_getMacros(x_38, x_3, x_73);
lean_dec(x_38);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
lean_dec(x_11);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_1);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_inc(x_27);
x_79 = l_Lean_Elab_Term_throwError___rarg(x_3, x_78, x_27, x_71);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_48 = x_80;
x_49 = x_81;
goto block_65;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_71);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_48 = x_83;
x_49 = x_84;
goto block_65;
}
}
else
{
lean_object* x_85; 
lean_dec(x_40);
lean_dec(x_35);
lean_dec(x_27);
x_85 = lean_ctor_get(x_74, 0);
lean_inc(x_85);
lean_dec(x_74);
x_41 = x_85;
x_42 = x_71;
goto block_47;
}
block_47:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_inc(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_19);
x_45 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_45, 0, x_11);
lean_ctor_set(x_45, 1, x_12);
lean_ctor_set(x_45, 2, x_13);
lean_ctor_set(x_45, 3, x_14);
lean_ctor_set(x_45, 4, x_15);
lean_ctor_set(x_45, 5, x_16);
lean_ctor_set(x_45, 6, x_17);
lean_ctor_set(x_45, 7, x_18);
lean_ctor_set(x_45, 8, x_44);
lean_ctor_set(x_45, 9, x_7);
lean_ctor_set_uint8(x_45, sizeof(void*)*10, x_20);
lean_ctor_set_uint8(x_45, sizeof(void*)*10 + 1, x_21);
x_3 = x_41;
x_4 = x_45;
x_5 = x_42;
goto _start;
}
block_65:
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
lean_dec(x_50);
lean_dec(x_35);
lean_dec(x_27);
lean_dec(x_3);
if (lean_is_scalar(x_40)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_40;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_48);
lean_dec(x_40);
x_52 = l_Lean_Name_toString___closed__1;
x_53 = l_Lean_Name_toStringWithSep___main(x_52, x_35);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Lean_Elab_Term_elabTermAux___main___closed__3;
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Elab_Term_elabTermAux___main___closed__6;
x_59 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Elab_Term_throwError___rarg(x_3, x_59, x_27, x_49);
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
return x_60;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_35);
lean_dec(x_11);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
x_86 = lean_ctor_get(x_36, 0);
lean_inc(x_86);
lean_dec(x_36);
lean_inc(x_28);
x_87 = l___private_Init_Lean_Elab_Term_8__elabTermUsing___main(x_28, x_3, x_1, x_2, x_86, x_27, x_28);
return x_87;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; uint8_t x_172; 
x_98 = lean_ctor_get(x_11, 0);
x_99 = lean_ctor_get(x_11, 1);
x_100 = lean_ctor_get(x_11, 2);
x_101 = lean_ctor_get(x_11, 3);
x_102 = lean_ctor_get(x_11, 4);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_11);
x_103 = lean_nat_add(x_101, x_8);
lean_dec(x_101);
x_104 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_104, 0, x_98);
lean_ctor_set(x_104, 1, x_99);
lean_ctor_set(x_104, 2, x_100);
lean_ctor_set(x_104, 3, x_103);
lean_ctor_set(x_104, 4, x_102);
lean_inc(x_7);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_104);
x_105 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_12);
lean_ctor_set(x_105, 2, x_13);
lean_ctor_set(x_105, 3, x_14);
lean_ctor_set(x_105, 4, x_15);
lean_ctor_set(x_105, 5, x_16);
lean_ctor_set(x_105, 6, x_17);
lean_ctor_set(x_105, 7, x_18);
lean_ctor_set(x_105, 8, x_19);
lean_ctor_set(x_105, 9, x_7);
lean_ctor_set_uint8(x_105, sizeof(void*)*10, x_20);
lean_ctor_set_uint8(x_105, sizeof(void*)*10 + 1, x_21);
x_167 = l_Lean_Elab_Term_getOptions(x_105, x_23);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__3;
x_171 = l_Lean_checkTraceOption(x_168, x_170);
lean_dec(x_168);
x_172 = l_coeDecidableEq(x_171);
if (x_172 == 0)
{
x_106 = x_169;
goto block_166;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_inc(x_3);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_3);
x_174 = l_Lean_Elab_Term_logTrace(x_170, x_3, x_173, x_105, x_169);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_106 = x_175;
goto block_166;
}
block_166:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_107 = l_Lean_Elab_Term_termElabAttribute;
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec(x_109);
x_111 = l_Lean_PersistentEnvExtension_getState___rarg(x_108, x_110);
lean_dec(x_110);
lean_dec(x_108);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
lean_inc(x_3);
x_113 = l_Lean_Syntax_getKind(x_3);
x_114 = l_Lean_SMap_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__1(x_112, x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_126; lean_object* x_127; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_115 = l_Lean_Elab_Term_getEnv___rarg(x_106);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
x_144 = l_Lean_Elab_Term_getCurrMacroScope(x_105, x_117);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_Elab_Term_getEnv___rarg(x_146);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_environment_main_module(x_148);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_145);
lean_inc(x_3);
x_152 = l_Lean_Elab_getMacros(x_116, x_3, x_151);
lean_dec(x_116);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; 
lean_dec(x_104);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_1);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec(x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec(x_153);
x_155 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_155);
lean_inc(x_105);
x_157 = l_Lean_Elab_Term_throwError___rarg(x_3, x_156, x_105, x_149);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_126 = x_158;
x_127 = x_159;
goto block_143;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_149);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_126 = x_161;
x_127 = x_162;
goto block_143;
}
}
else
{
lean_object* x_163; 
lean_dec(x_118);
lean_dec(x_113);
lean_dec(x_105);
x_163 = lean_ctor_get(x_152, 0);
lean_inc(x_163);
lean_dec(x_152);
x_119 = x_163;
x_120 = x_149;
goto block_125;
}
block_125:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_inc(x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_3);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_19);
x_123 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_123, 0, x_104);
lean_ctor_set(x_123, 1, x_12);
lean_ctor_set(x_123, 2, x_13);
lean_ctor_set(x_123, 3, x_14);
lean_ctor_set(x_123, 4, x_15);
lean_ctor_set(x_123, 5, x_16);
lean_ctor_set(x_123, 6, x_17);
lean_ctor_set(x_123, 7, x_18);
lean_ctor_set(x_123, 8, x_122);
lean_ctor_set(x_123, 9, x_7);
lean_ctor_set_uint8(x_123, sizeof(void*)*10, x_20);
lean_ctor_set_uint8(x_123, sizeof(void*)*10 + 1, x_21);
x_3 = x_119;
x_4 = x_123;
x_5 = x_120;
goto _start;
}
block_143:
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
lean_dec(x_128);
lean_dec(x_113);
lean_dec(x_105);
lean_dec(x_3);
if (lean_is_scalar(x_118)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_118;
 lean_ctor_set_tag(x_129, 1);
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_126);
lean_dec(x_118);
x_130 = l_Lean_Name_toString___closed__1;
x_131 = l_Lean_Name_toStringWithSep___main(x_130, x_113);
x_132 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = l_Lean_Elab_Term_elabTermAux___main___closed__3;
x_135 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = l_Lean_Elab_Term_elabTermAux___main___closed__6;
x_137 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_Elab_Term_throwError___rarg(x_3, x_137, x_105, x_127);
lean_dec(x_3);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
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
lean_object* x_164; lean_object* x_165; 
lean_dec(x_113);
lean_dec(x_104);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
x_164 = lean_ctor_get(x_114, 0);
lean_inc(x_164);
lean_dec(x_114);
lean_inc(x_106);
x_165 = l___private_Init_Lean_Elab_Term_8__elabTermUsing___main(x_106, x_3, x_1, x_2, x_164, x_105, x_106);
return x_165;
}
}
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_280; lean_object* x_281; uint8_t x_282; uint8_t x_283; 
x_187 = lean_ctor_get(x_4, 0);
x_188 = lean_ctor_get(x_4, 1);
x_189 = lean_ctor_get(x_4, 2);
x_190 = lean_ctor_get(x_4, 3);
x_191 = lean_ctor_get(x_4, 4);
x_192 = lean_ctor_get(x_4, 5);
x_193 = lean_ctor_get(x_4, 6);
x_194 = lean_ctor_get(x_4, 7);
x_195 = lean_ctor_get(x_4, 8);
x_196 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_197 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_4);
lean_inc(x_7);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
x_198 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_198, 0, x_187);
lean_ctor_set(x_198, 1, x_188);
lean_ctor_set(x_198, 2, x_189);
lean_ctor_set(x_198, 3, x_190);
lean_ctor_set(x_198, 4, x_191);
lean_ctor_set(x_198, 5, x_192);
lean_ctor_set(x_198, 6, x_193);
lean_ctor_set(x_198, 7, x_194);
lean_ctor_set(x_198, 8, x_195);
lean_ctor_set(x_198, 9, x_7);
lean_ctor_set_uint8(x_198, sizeof(void*)*10, x_196);
lean_ctor_set_uint8(x_198, sizeof(void*)*10 + 1, x_197);
x_280 = lean_ctor_get(x_187, 3);
lean_inc(x_280);
x_281 = lean_ctor_get(x_187, 4);
lean_inc(x_281);
x_282 = lean_nat_dec_eq(x_280, x_281);
lean_dec(x_281);
lean_dec(x_280);
x_283 = l_coeDecidableEq(x_282);
if (x_283 == 0)
{
lean_dec(x_198);
x_199 = x_5;
goto block_279;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_7);
lean_dec(x_1);
x_284 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
x_285 = l_Lean_Elab_Term_throwError___rarg(x_3, x_284, x_198, x_5);
lean_dec(x_3);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_288 = x_285;
} else {
 lean_dec_ref(x_285);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
return x_289;
}
block_279:
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; uint8_t x_275; 
x_200 = lean_ctor_get(x_187, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_187, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_187, 2);
lean_inc(x_202);
x_203 = lean_ctor_get(x_187, 3);
lean_inc(x_203);
x_204 = lean_ctor_get(x_187, 4);
lean_inc(x_204);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 lean_ctor_release(x_187, 4);
 x_205 = x_187;
} else {
 lean_dec_ref(x_187);
 x_205 = lean_box(0);
}
x_206 = lean_nat_add(x_203, x_8);
lean_dec(x_203);
if (lean_is_scalar(x_205)) {
 x_207 = lean_alloc_ctor(0, 5, 0);
} else {
 x_207 = x_205;
}
lean_ctor_set(x_207, 0, x_200);
lean_ctor_set(x_207, 1, x_201);
lean_ctor_set(x_207, 2, x_202);
lean_ctor_set(x_207, 3, x_206);
lean_ctor_set(x_207, 4, x_204);
lean_inc(x_7);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_207);
x_208 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_188);
lean_ctor_set(x_208, 2, x_189);
lean_ctor_set(x_208, 3, x_190);
lean_ctor_set(x_208, 4, x_191);
lean_ctor_set(x_208, 5, x_192);
lean_ctor_set(x_208, 6, x_193);
lean_ctor_set(x_208, 7, x_194);
lean_ctor_set(x_208, 8, x_195);
lean_ctor_set(x_208, 9, x_7);
lean_ctor_set_uint8(x_208, sizeof(void*)*10, x_196);
lean_ctor_set_uint8(x_208, sizeof(void*)*10 + 1, x_197);
x_270 = l_Lean_Elab_Term_getOptions(x_208, x_199);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_273 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__3;
x_274 = l_Lean_checkTraceOption(x_271, x_273);
lean_dec(x_271);
x_275 = l_coeDecidableEq(x_274);
if (x_275 == 0)
{
x_209 = x_272;
goto block_269;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_inc(x_3);
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_3);
x_277 = l_Lean_Elab_Term_logTrace(x_273, x_3, x_276, x_208, x_272);
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
lean_dec(x_277);
x_209 = x_278;
goto block_269;
}
block_269:
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_210 = l_Lean_Elab_Term_termElabAttribute;
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_209, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
lean_dec(x_212);
x_214 = l_Lean_PersistentEnvExtension_getState___rarg(x_211, x_213);
lean_dec(x_213);
lean_dec(x_211);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
lean_inc(x_3);
x_216 = l_Lean_Syntax_getKind(x_3);
x_217 = l_Lean_SMap_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__1(x_215, x_216);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_229; lean_object* x_230; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_218 = l_Lean_Elab_Term_getEnv___rarg(x_209);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_221 = x_218;
} else {
 lean_dec_ref(x_218);
 x_221 = lean_box(0);
}
x_247 = l_Lean_Elab_Term_getCurrMacroScope(x_208, x_220);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = l_Lean_Elab_Term_getEnv___rarg(x_249);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_environment_main_module(x_251);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_248);
lean_inc(x_3);
x_255 = l_Lean_Elab_getMacros(x_219, x_3, x_254);
lean_dec(x_219);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; 
lean_dec(x_207);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_7);
lean_dec(x_1);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
lean_dec(x_255);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
lean_dec(x_256);
x_258 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_258, 0, x_257);
x_259 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_259, 0, x_258);
lean_inc(x_208);
x_260 = l_Lean_Elab_Term_throwError___rarg(x_3, x_259, x_208, x_252);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_229 = x_261;
x_230 = x_262;
goto block_246;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_252);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
x_229 = x_264;
x_230 = x_265;
goto block_246;
}
}
else
{
lean_object* x_266; 
lean_dec(x_221);
lean_dec(x_216);
lean_dec(x_208);
x_266 = lean_ctor_get(x_255, 0);
lean_inc(x_266);
lean_dec(x_255);
x_222 = x_266;
x_223 = x_252;
goto block_228;
}
block_228:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_inc(x_222);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_3);
lean_ctor_set(x_224, 1, x_222);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_195);
x_226 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_226, 0, x_207);
lean_ctor_set(x_226, 1, x_188);
lean_ctor_set(x_226, 2, x_189);
lean_ctor_set(x_226, 3, x_190);
lean_ctor_set(x_226, 4, x_191);
lean_ctor_set(x_226, 5, x_192);
lean_ctor_set(x_226, 6, x_193);
lean_ctor_set(x_226, 7, x_194);
lean_ctor_set(x_226, 8, x_225);
lean_ctor_set(x_226, 9, x_7);
lean_ctor_set_uint8(x_226, sizeof(void*)*10, x_196);
lean_ctor_set_uint8(x_226, sizeof(void*)*10 + 1, x_197);
x_3 = x_222;
x_4 = x_226;
x_5 = x_223;
goto _start;
}
block_246:
{
lean_object* x_231; 
x_231 = lean_ctor_get(x_229, 0);
lean_inc(x_231);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; 
lean_dec(x_231);
lean_dec(x_216);
lean_dec(x_208);
lean_dec(x_3);
if (lean_is_scalar(x_221)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_221;
 lean_ctor_set_tag(x_232, 1);
}
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_229);
lean_dec(x_221);
x_233 = l_Lean_Name_toString___closed__1;
x_234 = l_Lean_Name_toStringWithSep___main(x_233, x_216);
x_235 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_235, 0, x_234);
x_236 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_236, 0, x_235);
x_237 = l_Lean_Elab_Term_elabTermAux___main___closed__3;
x_238 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_236);
x_239 = l_Lean_Elab_Term_elabTermAux___main___closed__6;
x_240 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
x_241 = l_Lean_Elab_Term_throwError___rarg(x_3, x_240, x_208, x_230);
lean_dec(x_3);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_244 = x_241;
} else {
 lean_dec_ref(x_241);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
}
else
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_216);
lean_dec(x_207);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_7);
x_267 = lean_ctor_get(x_217, 0);
lean_inc(x_267);
lean_dec(x_217);
lean_inc(x_209);
x_268 = l___private_Init_Lean_Elab_Term_8__elabTermUsing___main(x_209, x_3, x_1, x_2, x_267, x_208, x_209);
return x_268;
}
}
}
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; uint8_t x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_393; lean_object* x_394; uint8_t x_395; uint8_t x_396; 
x_290 = lean_ctor_get(x_5, 0);
x_291 = lean_ctor_get(x_5, 1);
x_292 = lean_ctor_get(x_5, 2);
x_293 = lean_ctor_get(x_5, 3);
x_294 = lean_ctor_get(x_5, 4);
x_295 = lean_ctor_get(x_5, 5);
lean_inc(x_295);
lean_inc(x_294);
lean_inc(x_293);
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_5);
x_296 = lean_unsigned_to_nat(1u);
x_297 = lean_nat_add(x_295, x_296);
x_298 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_298, 0, x_290);
lean_ctor_set(x_298, 1, x_291);
lean_ctor_set(x_298, 2, x_292);
lean_ctor_set(x_298, 3, x_293);
lean_ctor_set(x_298, 4, x_294);
lean_ctor_set(x_298, 5, x_297);
x_299 = lean_ctor_get(x_4, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_4, 1);
lean_inc(x_300);
x_301 = lean_ctor_get(x_4, 2);
lean_inc(x_301);
x_302 = lean_ctor_get(x_4, 3);
lean_inc(x_302);
x_303 = lean_ctor_get(x_4, 4);
lean_inc(x_303);
x_304 = lean_ctor_get(x_4, 5);
lean_inc(x_304);
x_305 = lean_ctor_get(x_4, 6);
lean_inc(x_305);
x_306 = lean_ctor_get(x_4, 7);
lean_inc(x_306);
x_307 = lean_ctor_get(x_4, 8);
lean_inc(x_307);
x_308 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_309 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 lean_ctor_release(x_4, 8);
 lean_ctor_release(x_4, 9);
 x_310 = x_4;
} else {
 lean_dec_ref(x_4);
 x_310 = lean_box(0);
}
lean_inc(x_295);
lean_inc(x_307);
lean_inc(x_306);
lean_inc(x_305);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
if (lean_is_scalar(x_310)) {
 x_311 = lean_alloc_ctor(0, 10, 2);
} else {
 x_311 = x_310;
}
lean_ctor_set(x_311, 0, x_299);
lean_ctor_set(x_311, 1, x_300);
lean_ctor_set(x_311, 2, x_301);
lean_ctor_set(x_311, 3, x_302);
lean_ctor_set(x_311, 4, x_303);
lean_ctor_set(x_311, 5, x_304);
lean_ctor_set(x_311, 6, x_305);
lean_ctor_set(x_311, 7, x_306);
lean_ctor_set(x_311, 8, x_307);
lean_ctor_set(x_311, 9, x_295);
lean_ctor_set_uint8(x_311, sizeof(void*)*10, x_308);
lean_ctor_set_uint8(x_311, sizeof(void*)*10 + 1, x_309);
x_393 = lean_ctor_get(x_299, 3);
lean_inc(x_393);
x_394 = lean_ctor_get(x_299, 4);
lean_inc(x_394);
x_395 = lean_nat_dec_eq(x_393, x_394);
lean_dec(x_394);
lean_dec(x_393);
x_396 = l_coeDecidableEq(x_395);
if (x_396 == 0)
{
lean_dec(x_311);
x_312 = x_298;
goto block_392;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_295);
lean_dec(x_1);
x_397 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
x_398 = l_Lean_Elab_Term_throwError___rarg(x_3, x_397, x_311, x_298);
lean_dec(x_3);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_401 = x_398;
} else {
 lean_dec_ref(x_398);
 x_401 = lean_box(0);
}
if (lean_is_scalar(x_401)) {
 x_402 = lean_alloc_ctor(1, 2, 0);
} else {
 x_402 = x_401;
}
lean_ctor_set(x_402, 0, x_399);
lean_ctor_set(x_402, 1, x_400);
return x_402;
}
block_392:
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; uint8_t x_388; 
x_313 = lean_ctor_get(x_299, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_299, 1);
lean_inc(x_314);
x_315 = lean_ctor_get(x_299, 2);
lean_inc(x_315);
x_316 = lean_ctor_get(x_299, 3);
lean_inc(x_316);
x_317 = lean_ctor_get(x_299, 4);
lean_inc(x_317);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 lean_ctor_release(x_299, 2);
 lean_ctor_release(x_299, 3);
 lean_ctor_release(x_299, 4);
 x_318 = x_299;
} else {
 lean_dec_ref(x_299);
 x_318 = lean_box(0);
}
x_319 = lean_nat_add(x_316, x_296);
lean_dec(x_316);
if (lean_is_scalar(x_318)) {
 x_320 = lean_alloc_ctor(0, 5, 0);
} else {
 x_320 = x_318;
}
lean_ctor_set(x_320, 0, x_313);
lean_ctor_set(x_320, 1, x_314);
lean_ctor_set(x_320, 2, x_315);
lean_ctor_set(x_320, 3, x_319);
lean_ctor_set(x_320, 4, x_317);
lean_inc(x_295);
lean_inc(x_307);
lean_inc(x_306);
lean_inc(x_305);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_320);
x_321 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_300);
lean_ctor_set(x_321, 2, x_301);
lean_ctor_set(x_321, 3, x_302);
lean_ctor_set(x_321, 4, x_303);
lean_ctor_set(x_321, 5, x_304);
lean_ctor_set(x_321, 6, x_305);
lean_ctor_set(x_321, 7, x_306);
lean_ctor_set(x_321, 8, x_307);
lean_ctor_set(x_321, 9, x_295);
lean_ctor_set_uint8(x_321, sizeof(void*)*10, x_308);
lean_ctor_set_uint8(x_321, sizeof(void*)*10 + 1, x_309);
x_383 = l_Lean_Elab_Term_getOptions(x_321, x_312);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
lean_dec(x_383);
x_386 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__3;
x_387 = l_Lean_checkTraceOption(x_384, x_386);
lean_dec(x_384);
x_388 = l_coeDecidableEq(x_387);
if (x_388 == 0)
{
x_322 = x_385;
goto block_382;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_inc(x_3);
x_389 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_389, 0, x_3);
x_390 = l_Lean_Elab_Term_logTrace(x_386, x_3, x_389, x_321, x_385);
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
lean_dec(x_390);
x_322 = x_391;
goto block_382;
}
block_382:
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_323 = l_Lean_Elab_Term_termElabAttribute;
x_324 = lean_ctor_get(x_323, 1);
lean_inc(x_324);
x_325 = lean_ctor_get(x_322, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
lean_dec(x_325);
x_327 = l_Lean_PersistentEnvExtension_getState___rarg(x_324, x_326);
lean_dec(x_326);
lean_dec(x_324);
x_328 = lean_ctor_get(x_327, 1);
lean_inc(x_328);
lean_dec(x_327);
lean_inc(x_3);
x_329 = l_Lean_Syntax_getKind(x_3);
x_330 = l_Lean_SMap_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__1(x_328, x_329);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_342; lean_object* x_343; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_331 = l_Lean_Elab_Term_getEnv___rarg(x_322);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_334 = x_331;
} else {
 lean_dec_ref(x_331);
 x_334 = lean_box(0);
}
x_360 = l_Lean_Elab_Term_getCurrMacroScope(x_321, x_333);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = l_Lean_Elab_Term_getEnv___rarg(x_362);
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
lean_dec(x_363);
x_366 = lean_environment_main_module(x_364);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_361);
lean_inc(x_3);
x_368 = l_Lean_Elab_getMacros(x_332, x_3, x_367);
lean_dec(x_332);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; 
lean_dec(x_320);
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_295);
lean_dec(x_1);
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
lean_dec(x_368);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
lean_dec(x_369);
x_371 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_371, 0, x_370);
x_372 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_372, 0, x_371);
lean_inc(x_321);
x_373 = l_Lean_Elab_Term_throwError___rarg(x_3, x_372, x_321, x_365);
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
x_342 = x_374;
x_343 = x_375;
goto block_359;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_365);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec(x_376);
x_342 = x_377;
x_343 = x_378;
goto block_359;
}
}
else
{
lean_object* x_379; 
lean_dec(x_334);
lean_dec(x_329);
lean_dec(x_321);
x_379 = lean_ctor_get(x_368, 0);
lean_inc(x_379);
lean_dec(x_368);
x_335 = x_379;
x_336 = x_365;
goto block_341;
}
block_341:
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_inc(x_335);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_3);
lean_ctor_set(x_337, 1, x_335);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_307);
x_339 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_339, 0, x_320);
lean_ctor_set(x_339, 1, x_300);
lean_ctor_set(x_339, 2, x_301);
lean_ctor_set(x_339, 3, x_302);
lean_ctor_set(x_339, 4, x_303);
lean_ctor_set(x_339, 5, x_304);
lean_ctor_set(x_339, 6, x_305);
lean_ctor_set(x_339, 7, x_306);
lean_ctor_set(x_339, 8, x_338);
lean_ctor_set(x_339, 9, x_295);
lean_ctor_set_uint8(x_339, sizeof(void*)*10, x_308);
lean_ctor_set_uint8(x_339, sizeof(void*)*10 + 1, x_309);
x_3 = x_335;
x_4 = x_339;
x_5 = x_336;
goto _start;
}
block_359:
{
lean_object* x_344; 
x_344 = lean_ctor_get(x_342, 0);
lean_inc(x_344);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; 
lean_dec(x_344);
lean_dec(x_329);
lean_dec(x_321);
lean_dec(x_3);
if (lean_is_scalar(x_334)) {
 x_345 = lean_alloc_ctor(1, 2, 0);
} else {
 x_345 = x_334;
 lean_ctor_set_tag(x_345, 1);
}
lean_ctor_set(x_345, 0, x_342);
lean_ctor_set(x_345, 1, x_343);
return x_345;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_dec(x_342);
lean_dec(x_334);
x_346 = l_Lean_Name_toString___closed__1;
x_347 = l_Lean_Name_toStringWithSep___main(x_346, x_329);
x_348 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_348, 0, x_347);
x_349 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_349, 0, x_348);
x_350 = l_Lean_Elab_Term_elabTermAux___main___closed__3;
x_351 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_349);
x_352 = l_Lean_Elab_Term_elabTermAux___main___closed__6;
x_353 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
x_354 = l_Lean_Elab_Term_throwError___rarg(x_3, x_353, x_321, x_343);
lean_dec(x_3);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_357 = x_354;
} else {
 lean_dec_ref(x_354);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 2, 0);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_355);
lean_ctor_set(x_358, 1, x_356);
return x_358;
}
}
}
else
{
lean_object* x_380; lean_object* x_381; 
lean_dec(x_329);
lean_dec(x_320);
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_295);
x_380 = lean_ctor_get(x_330, 0);
lean_inc(x_380);
lean_dec(x_330);
lean_inc(x_322);
x_381 = l___private_Init_Lean_Elab_Term_8__elabTermUsing___main(x_322, x_3, x_1, x_2, x_380, x_321, x_322);
return x_381;
}
}
}
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabTermAux___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabTermAux___main___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTermAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTermAux___main___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_Term_elabTermAux___main___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Elab_Term_elabTermAux___main___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_Elab_Term_elabTermAux___main___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabTermAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_Term_elabTermAux___main(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabTermAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_elabTermAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_elabTermAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_Term_elabTermAux(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabTerm(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_3, x_1, x_4, x_5);
return x_6;
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
x_10 = lean_ctor_get(x_4, 8);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_7);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_4, 8, x_12);
x_13 = 1;
x_14 = l_Lean_Elab_Term_elabTermAux___main(x_3, x_13, x_7, x_4, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_4, 2);
x_18 = lean_ctor_get(x_4, 3);
x_19 = lean_ctor_get(x_4, 4);
x_20 = lean_ctor_get(x_4, 5);
x_21 = lean_ctor_get(x_4, 6);
x_22 = lean_ctor_get(x_4, 7);
x_23 = lean_ctor_get(x_4, 8);
x_24 = lean_ctor_get(x_4, 9);
x_25 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_26 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
lean_inc(x_24);
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
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
x_29 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_16);
lean_ctor_set(x_29, 2, x_17);
lean_ctor_set(x_29, 3, x_18);
lean_ctor_set(x_29, 4, x_19);
lean_ctor_set(x_29, 5, x_20);
lean_ctor_set(x_29, 6, x_21);
lean_ctor_set(x_29, 7, x_22);
lean_ctor_set(x_29, 8, x_28);
lean_ctor_set(x_29, 9, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*10, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*10 + 1, x_26);
x_30 = 1;
x_31 = l_Lean_Elab_Term_elabTermAux___main(x_3, x_30, x_7, x_29, x_8);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_6);
if (x_32 == 0)
{
return x_6;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_6, 0);
x_34 = lean_ctor_get(x_6, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_6);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_ensureType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toStr___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_ensureType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_ensureType___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_ensureType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Elab_Term_inferType(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
x_8 = l_Lean_Elab_Term_whnf(x_1, x_6, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Expr_isSort(x_10);
x_13 = l_coeDecidableEq(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_8);
lean_inc(x_3);
x_14 = l_Lean_Elab_Term_mkFreshLevelMVar(x_1, x_3, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_mkSort(x_15);
lean_inc(x_3);
x_18 = l_Lean_Elab_Term_isDefEq(x_1, x_10, x_17, x_3, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_Elab_Term_ensureType___closed__2;
x_23 = l_Lean_Elab_Term_throwError___rarg(x_1, x_22, x_3, x_21);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_18, 0);
lean_dec(x_25);
lean_ctor_set(x_18, 0, x_2);
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_dec(x_10);
lean_dec(x_3);
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
x_34 = l_Lean_Expr_isSort(x_32);
x_35 = l_coeDecidableEq(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc(x_3);
x_36 = l_Lean_Elab_Term_mkFreshLevelMVar(x_1, x_3, x_33);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_mkSort(x_37);
lean_inc(x_3);
x_40 = l_Lean_Elab_Term_isDefEq(x_1, x_32, x_39, x_3, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = l_Lean_Elab_Term_ensureType___closed__2;
x_45 = l_Lean_Elab_Term_throwError___rarg(x_1, x_44, x_3, x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_3);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_47 = x_40;
} else {
 lean_dec_ref(x_40);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_2);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; 
lean_dec(x_32);
lean_dec(x_3);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_2);
lean_ctor_set(x_53, 1, x_33);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_8);
if (x_54 == 0)
{
return x_8;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_8, 0);
x_56 = lean_ctor_get(x_8, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_8);
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
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_5);
if (x_58 == 0)
{
return x_5;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_5, 0);
x_60 = lean_ctor_get(x_5, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_5);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
lean_object* l_Lean_Elab_Term_ensureType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_ensureType(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Term_mkFreshLevelMVar(x_1, x_2, x_3);
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
x_10 = l_Lean_Elab_Term_elabTermAux___main(x_8, x_9, x_1, x_2, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_ensureType(x_1, x_11, x_2, x_12);
lean_dec(x_1);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_ctor_get(x_4, 3);
x_21 = lean_ctor_get(x_4, 4);
x_22 = lean_ctor_get(x_4, 5);
x_23 = lean_ctor_get(x_4, 6);
x_24 = lean_ctor_get(x_4, 7);
x_25 = lean_ctor_get(x_4, 8);
x_26 = lean_ctor_get(x_4, 9);
x_27 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_28 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
lean_inc(x_26);
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
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_17, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_17, 4);
lean_inc(x_31);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 x_32 = x_17;
} else {
 lean_dec_ref(x_17);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 5, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_1);
lean_ctor_set(x_33, 2, x_2);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set(x_33, 4, x_31);
x_34 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_18);
lean_ctor_set(x_34, 2, x_19);
lean_ctor_set(x_34, 3, x_20);
lean_ctor_set(x_34, 4, x_21);
lean_ctor_set(x_34, 5, x_22);
lean_ctor_set(x_34, 6, x_23);
lean_ctor_set(x_34, 7, x_24);
lean_ctor_set(x_34, 8, x_25);
lean_ctor_set(x_34, 9, x_26);
lean_ctor_set_uint8(x_34, sizeof(void*)*10, x_27);
lean_ctor_set_uint8(x_34, sizeof(void*)*10 + 1, x_28);
x_35 = lean_apply_2(x_3, x_34, x_5);
return x_35;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_2, 2, x_16);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_1);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 3);
x_22 = lean_ctor_get(x_2, 4);
x_23 = lean_ctor_get(x_2, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_26 = x_3;
} else {
 lean_dec_ref(x_3);
 x_26 = lean_box(0);
}
x_27 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 3, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_20);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_21);
lean_ctor_set(x_29, 4, x_22);
lean_ctor_set(x_29, 5, x_23);
lean_ctor_set(x_1, 0, x_29);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_1);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_32 = lean_ctor_get(x_1, 1);
x_33 = lean_ctor_get(x_1, 2);
x_34 = lean_ctor_get(x_1, 3);
x_35 = lean_ctor_get(x_1, 4);
x_36 = lean_ctor_get(x_1, 5);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 4);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 5);
lean_inc(x_41);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_42 = x_2;
} else {
 lean_dec_ref(x_2);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_45 = x_3;
} else {
 lean_dec_ref(x_3);
 x_45 = lean_box(0);
}
x_46 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 3, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_46);
if (lean_is_scalar(x_42)) {
 x_48 = lean_alloc_ctor(0, 6, 0);
} else {
 x_48 = x_42;
}
lean_ctor_set(x_48, 0, x_37);
lean_ctor_set(x_48, 1, x_38);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_39);
lean_ctor_set(x_48, 4, x_40);
lean_ctor_set(x_48, 5, x_41);
x_49 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_32);
lean_ctor_set(x_49, 2, x_33);
lean_ctor_set(x_49, 3, x_34);
lean_ctor_set(x_49, 4, x_35);
lean_ctor_set(x_49, 5, x_36);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_1, x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_9, 1);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_11, 2);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_12, 2);
lean_dec(x_20);
lean_ctor_set(x_12, 2, x_6);
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_6);
lean_ctor_set(x_11, 2, x_23);
return x_9;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get(x_11, 4);
x_28 = lean_ctor_get(x_11, 5);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_29 = lean_ctor_get(x_12, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_31 = x_12;
} else {
 lean_dec_ref(x_12);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 3, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_6);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_25);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_26);
lean_ctor_set(x_33, 4, x_27);
lean_ctor_set(x_33, 5, x_28);
lean_ctor_set(x_10, 0, x_33);
return x_9;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_34 = lean_ctor_get(x_10, 1);
x_35 = lean_ctor_get(x_10, 2);
x_36 = lean_ctor_get(x_10, 3);
x_37 = lean_ctor_get(x_10, 4);
x_38 = lean_ctor_get(x_10, 5);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_10);
x_39 = lean_ctor_get(x_11, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_11, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_11, 4);
lean_inc(x_42);
x_43 = lean_ctor_get(x_11, 5);
lean_inc(x_43);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_44 = x_11;
} else {
 lean_dec_ref(x_11);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_12, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_12, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_47 = x_12;
} else {
 lean_dec_ref(x_12);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 3, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_6);
if (lean_is_scalar(x_44)) {
 x_49 = lean_alloc_ctor(0, 6, 0);
} else {
 x_49 = x_44;
}
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_40);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_41);
lean_ctor_set(x_49, 4, x_42);
lean_ctor_set(x_49, 5, x_43);
x_50 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_34);
lean_ctor_set(x_50, 2, x_35);
lean_ctor_set(x_50, 3, x_36);
lean_ctor_set(x_50, 4, x_37);
lean_ctor_set(x_50, 5, x_38);
lean_ctor_set(x_9, 1, x_50);
return x_9;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_51 = lean_ctor_get(x_9, 0);
lean_inc(x_51);
lean_dec(x_9);
x_52 = lean_ctor_get(x_10, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_10, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_10, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_10, 4);
lean_inc(x_55);
x_56 = lean_ctor_get(x_10, 5);
lean_inc(x_56);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 lean_ctor_release(x_10, 5);
 x_57 = x_10;
} else {
 lean_dec_ref(x_10);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_11, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_11, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_11, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_11, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_11, 5);
lean_inc(x_62);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_63 = x_11;
} else {
 lean_dec_ref(x_11);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_12, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_12, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_66 = x_12;
} else {
 lean_dec_ref(x_12);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 3, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set(x_67, 2, x_6);
if (lean_is_scalar(x_63)) {
 x_68 = lean_alloc_ctor(0, 6, 0);
} else {
 x_68 = x_63;
}
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_59);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set(x_68, 3, x_60);
lean_ctor_set(x_68, 4, x_61);
lean_ctor_set(x_68, 5, x_62);
if (lean_is_scalar(x_57)) {
 x_69 = lean_alloc_ctor(0, 6, 0);
} else {
 x_69 = x_57;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_52);
lean_ctor_set(x_69, 2, x_53);
lean_ctor_set(x_69, 3, x_54);
lean_ctor_set(x_69, 4, x_55);
lean_ctor_set(x_69, 5, x_56);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_51);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_9, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 2);
lean_inc(x_73);
x_74 = !lean_is_exclusive(x_9);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_9, 1);
lean_dec(x_75);
x_76 = !lean_is_exclusive(x_71);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_71, 0);
lean_dec(x_77);
x_78 = !lean_is_exclusive(x_72);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_72, 2);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_73);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_73, 2);
lean_dec(x_81);
lean_ctor_set(x_73, 2, x_6);
return x_9;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_73, 0);
x_83 = lean_ctor_get(x_73, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_73);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_6);
lean_ctor_set(x_72, 2, x_84);
return x_9;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_85 = lean_ctor_get(x_72, 0);
x_86 = lean_ctor_get(x_72, 1);
x_87 = lean_ctor_get(x_72, 3);
x_88 = lean_ctor_get(x_72, 4);
x_89 = lean_ctor_get(x_72, 5);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_72);
x_90 = lean_ctor_get(x_73, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_73, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_92 = x_73;
} else {
 lean_dec_ref(x_73);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 3, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_93, 2, x_6);
x_94 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_94, 0, x_85);
lean_ctor_set(x_94, 1, x_86);
lean_ctor_set(x_94, 2, x_93);
lean_ctor_set(x_94, 3, x_87);
lean_ctor_set(x_94, 4, x_88);
lean_ctor_set(x_94, 5, x_89);
lean_ctor_set(x_71, 0, x_94);
return x_9;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_95 = lean_ctor_get(x_71, 1);
x_96 = lean_ctor_get(x_71, 2);
x_97 = lean_ctor_get(x_71, 3);
x_98 = lean_ctor_get(x_71, 4);
x_99 = lean_ctor_get(x_71, 5);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_71);
x_100 = lean_ctor_get(x_72, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_72, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_72, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_72, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_72, 5);
lean_inc(x_104);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 lean_ctor_release(x_72, 5);
 x_105 = x_72;
} else {
 lean_dec_ref(x_72);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_73, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_73, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_108 = x_73;
} else {
 lean_dec_ref(x_73);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 3, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
lean_ctor_set(x_109, 2, x_6);
if (lean_is_scalar(x_105)) {
 x_110 = lean_alloc_ctor(0, 6, 0);
} else {
 x_110 = x_105;
}
lean_ctor_set(x_110, 0, x_100);
lean_ctor_set(x_110, 1, x_101);
lean_ctor_set(x_110, 2, x_109);
lean_ctor_set(x_110, 3, x_102);
lean_ctor_set(x_110, 4, x_103);
lean_ctor_set(x_110, 5, x_104);
x_111 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_95);
lean_ctor_set(x_111, 2, x_96);
lean_ctor_set(x_111, 3, x_97);
lean_ctor_set(x_111, 4, x_98);
lean_ctor_set(x_111, 5, x_99);
lean_ctor_set(x_9, 1, x_111);
return x_9;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_112 = lean_ctor_get(x_9, 0);
lean_inc(x_112);
lean_dec(x_9);
x_113 = lean_ctor_get(x_71, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_71, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_71, 3);
lean_inc(x_115);
x_116 = lean_ctor_get(x_71, 4);
lean_inc(x_116);
x_117 = lean_ctor_get(x_71, 5);
lean_inc(x_117);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 lean_ctor_release(x_71, 5);
 x_118 = x_71;
} else {
 lean_dec_ref(x_71);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_72, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_72, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_72, 3);
lean_inc(x_121);
x_122 = lean_ctor_get(x_72, 4);
lean_inc(x_122);
x_123 = lean_ctor_get(x_72, 5);
lean_inc(x_123);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 lean_ctor_release(x_72, 5);
 x_124 = x_72;
} else {
 lean_dec_ref(x_72);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_73, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_73, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_127 = x_73;
} else {
 lean_dec_ref(x_73);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 3, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
lean_ctor_set(x_128, 2, x_6);
if (lean_is_scalar(x_124)) {
 x_129 = lean_alloc_ctor(0, 6, 0);
} else {
 x_129 = x_124;
}
lean_ctor_set(x_129, 0, x_119);
lean_ctor_set(x_129, 1, x_120);
lean_ctor_set(x_129, 2, x_128);
lean_ctor_set(x_129, 3, x_121);
lean_ctor_set(x_129, 4, x_122);
lean_ctor_set(x_129, 5, x_123);
if (lean_is_scalar(x_118)) {
 x_130 = lean_alloc_ctor(0, 6, 0);
} else {
 x_130 = x_118;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_113);
lean_ctor_set(x_130, 2, x_114);
lean_ctor_set(x_130, 3, x_115);
lean_ctor_set(x_130, 4, x_116);
lean_ctor_set(x_130, 5, x_117);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_112);
lean_ctor_set(x_131, 1, x_130);
return x_131;
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
uint8_t x_5; 
x_5 = l_coeDecidableEq(x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_apply_2(x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_2, x_3, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_12, 1);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_13, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_14, 2);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_15, 2);
lean_dec(x_23);
lean_ctor_set(x_15, 2, x_9);
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_9);
lean_ctor_set(x_14, 2, x_26);
return x_12;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
x_29 = lean_ctor_get(x_14, 3);
x_30 = lean_ctor_get(x_14, 4);
x_31 = lean_ctor_get(x_14, 5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_32 = lean_ctor_get(x_15, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_34 = x_15;
} else {
 lean_dec_ref(x_15);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 3, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_9);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_28);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_29);
lean_ctor_set(x_36, 4, x_30);
lean_ctor_set(x_36, 5, x_31);
lean_ctor_set(x_13, 0, x_36);
return x_12;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_37 = lean_ctor_get(x_13, 1);
x_38 = lean_ctor_get(x_13, 2);
x_39 = lean_ctor_get(x_13, 3);
x_40 = lean_ctor_get(x_13, 4);
x_41 = lean_ctor_get(x_13, 5);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_42 = lean_ctor_get(x_14, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_14, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_14, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_14, 5);
lean_inc(x_46);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 lean_ctor_release(x_14, 5);
 x_47 = x_14;
} else {
 lean_dec_ref(x_14);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_15, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_15, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_50 = x_15;
} else {
 lean_dec_ref(x_15);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 3, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_9);
if (lean_is_scalar(x_47)) {
 x_52 = lean_alloc_ctor(0, 6, 0);
} else {
 x_52 = x_47;
}
lean_ctor_set(x_52, 0, x_42);
lean_ctor_set(x_52, 1, x_43);
lean_ctor_set(x_52, 2, x_51);
lean_ctor_set(x_52, 3, x_44);
lean_ctor_set(x_52, 4, x_45);
lean_ctor_set(x_52, 5, x_46);
x_53 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_37);
lean_ctor_set(x_53, 2, x_38);
lean_ctor_set(x_53, 3, x_39);
lean_ctor_set(x_53, 4, x_40);
lean_ctor_set(x_53, 5, x_41);
lean_ctor_set(x_12, 1, x_53);
return x_12;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_54 = lean_ctor_get(x_12, 0);
lean_inc(x_54);
lean_dec(x_12);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_13, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_13, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_13, 4);
lean_inc(x_58);
x_59 = lean_ctor_get(x_13, 5);
lean_inc(x_59);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 x_60 = x_13;
} else {
 lean_dec_ref(x_13);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_14, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_14, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_14, 3);
lean_inc(x_63);
x_64 = lean_ctor_get(x_14, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_14, 5);
lean_inc(x_65);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 lean_ctor_release(x_14, 5);
 x_66 = x_14;
} else {
 lean_dec_ref(x_14);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_15, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_15, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_69 = x_15;
} else {
 lean_dec_ref(x_15);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 3, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set(x_70, 2, x_9);
if (lean_is_scalar(x_66)) {
 x_71 = lean_alloc_ctor(0, 6, 0);
} else {
 x_71 = x_66;
}
lean_ctor_set(x_71, 0, x_61);
lean_ctor_set(x_71, 1, x_62);
lean_ctor_set(x_71, 2, x_70);
lean_ctor_set(x_71, 3, x_63);
lean_ctor_set(x_71, 4, x_64);
lean_ctor_set(x_71, 5, x_65);
if (lean_is_scalar(x_60)) {
 x_72 = lean_alloc_ctor(0, 6, 0);
} else {
 x_72 = x_60;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_55);
lean_ctor_set(x_72, 2, x_56);
lean_ctor_set(x_72, 3, x_57);
lean_ctor_set(x_72, 4, x_58);
lean_ctor_set(x_72, 5, x_59);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_54);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_12, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 2);
lean_inc(x_76);
x_77 = !lean_is_exclusive(x_12);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_12, 1);
lean_dec(x_78);
x_79 = !lean_is_exclusive(x_74);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_74, 0);
lean_dec(x_80);
x_81 = !lean_is_exclusive(x_75);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_75, 2);
lean_dec(x_82);
x_83 = !lean_is_exclusive(x_76);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_76, 2);
lean_dec(x_84);
lean_ctor_set(x_76, 2, x_9);
return x_12;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_76, 0);
x_86 = lean_ctor_get(x_76, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_76);
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_9);
lean_ctor_set(x_75, 2, x_87);
return x_12;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_88 = lean_ctor_get(x_75, 0);
x_89 = lean_ctor_get(x_75, 1);
x_90 = lean_ctor_get(x_75, 3);
x_91 = lean_ctor_get(x_75, 4);
x_92 = lean_ctor_get(x_75, 5);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_75);
x_93 = lean_ctor_get(x_76, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_76, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 lean_ctor_release(x_76, 2);
 x_95 = x_76;
} else {
 lean_dec_ref(x_76);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 3, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
lean_ctor_set(x_96, 2, x_9);
x_97 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_97, 0, x_88);
lean_ctor_set(x_97, 1, x_89);
lean_ctor_set(x_97, 2, x_96);
lean_ctor_set(x_97, 3, x_90);
lean_ctor_set(x_97, 4, x_91);
lean_ctor_set(x_97, 5, x_92);
lean_ctor_set(x_74, 0, x_97);
return x_12;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_98 = lean_ctor_get(x_74, 1);
x_99 = lean_ctor_get(x_74, 2);
x_100 = lean_ctor_get(x_74, 3);
x_101 = lean_ctor_get(x_74, 4);
x_102 = lean_ctor_get(x_74, 5);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_74);
x_103 = lean_ctor_get(x_75, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_75, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_75, 3);
lean_inc(x_105);
x_106 = lean_ctor_get(x_75, 4);
lean_inc(x_106);
x_107 = lean_ctor_get(x_75, 5);
lean_inc(x_107);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 lean_ctor_release(x_75, 5);
 x_108 = x_75;
} else {
 lean_dec_ref(x_75);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_76, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_76, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 lean_ctor_release(x_76, 2);
 x_111 = x_76;
} else {
 lean_dec_ref(x_76);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 3, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
lean_ctor_set(x_112, 2, x_9);
if (lean_is_scalar(x_108)) {
 x_113 = lean_alloc_ctor(0, 6, 0);
} else {
 x_113 = x_108;
}
lean_ctor_set(x_113, 0, x_103);
lean_ctor_set(x_113, 1, x_104);
lean_ctor_set(x_113, 2, x_112);
lean_ctor_set(x_113, 3, x_105);
lean_ctor_set(x_113, 4, x_106);
lean_ctor_set(x_113, 5, x_107);
x_114 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_98);
lean_ctor_set(x_114, 2, x_99);
lean_ctor_set(x_114, 3, x_100);
lean_ctor_set(x_114, 4, x_101);
lean_ctor_set(x_114, 5, x_102);
lean_ctor_set(x_12, 1, x_114);
return x_12;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_115 = lean_ctor_get(x_12, 0);
lean_inc(x_115);
lean_dec(x_12);
x_116 = lean_ctor_get(x_74, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_74, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_74, 3);
lean_inc(x_118);
x_119 = lean_ctor_get(x_74, 4);
lean_inc(x_119);
x_120 = lean_ctor_get(x_74, 5);
lean_inc(x_120);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 lean_ctor_release(x_74, 4);
 lean_ctor_release(x_74, 5);
 x_121 = x_74;
} else {
 lean_dec_ref(x_74);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_75, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_75, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_75, 3);
lean_inc(x_124);
x_125 = lean_ctor_get(x_75, 4);
lean_inc(x_125);
x_126 = lean_ctor_get(x_75, 5);
lean_inc(x_126);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 lean_ctor_release(x_75, 5);
 x_127 = x_75;
} else {
 lean_dec_ref(x_75);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_76, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_76, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 lean_ctor_release(x_76, 2);
 x_130 = x_76;
} else {
 lean_dec_ref(x_76);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(0, 3, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
lean_ctor_set(x_131, 2, x_9);
if (lean_is_scalar(x_127)) {
 x_132 = lean_alloc_ctor(0, 6, 0);
} else {
 x_132 = x_127;
}
lean_ctor_set(x_132, 0, x_122);
lean_ctor_set(x_132, 1, x_123);
lean_ctor_set(x_132, 2, x_131);
lean_ctor_set(x_132, 3, x_124);
lean_ctor_set(x_132, 4, x_125);
lean_ctor_set(x_132, 5, x_126);
if (lean_is_scalar(x_121)) {
 x_133 = lean_alloc_ctor(0, 6, 0);
} else {
 x_133 = x_121;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_116);
lean_ctor_set(x_133, 2, x_117);
lean_ctor_set(x_133, 3, x_118);
lean_ctor_set(x_133, 4, x_119);
lean_ctor_set(x_133, 5, x_120);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_115);
lean_ctor_set(x_134, 1, x_133);
return x_134;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_5 = l_Lean_Elab_Term_getMVarDecl(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 7);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 8);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 9);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; 
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_21 = lean_ctor_get(x_6, 2);
x_22 = lean_ctor_get(x_6, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_7, 4);
lean_inc(x_24);
x_25 = lean_array_get_size(x_21);
x_26 = lean_array_get_size(x_24);
x_27 = lean_nat_dec_eq(x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
lean_inc(x_24);
lean_ctor_set(x_6, 2, x_24);
lean_ctor_set(x_6, 1, x_23);
x_28 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_9);
lean_ctor_set(x_28, 2, x_10);
lean_ctor_set(x_28, 3, x_11);
lean_ctor_set(x_28, 4, x_12);
lean_ctor_set(x_28, 5, x_13);
lean_ctor_set(x_28, 6, x_14);
lean_ctor_set(x_28, 7, x_15);
lean_ctor_set(x_28, 8, x_16);
lean_ctor_set(x_28, 9, x_17);
lean_ctor_set_uint8(x_28, sizeof(void*)*10, x_19);
lean_ctor_set_uint8(x_28, sizeof(void*)*10 + 1, x_20);
if (x_27 == 0)
{
uint8_t x_161; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_3);
x_161 = 0;
x_29 = x_161;
goto block_160;
}
else
{
lean_object* x_162; uint8_t x_163; 
x_162 = lean_unsigned_to_nat(0u);
x_163 = l_Array_isEqvAux___main___at_Lean_Elab_Term_withMVarContext___spec__1(x_3, x_7, lean_box(0), x_21, x_24, x_162);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_3);
x_29 = x_163;
goto block_160;
}
block_160:
{
uint8_t x_30; 
x_30 = l_coeDecidableEq(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_apply_2(x_2, x_28, x_8);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_8, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 2);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_8);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_apply_2(x_2, x_28, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 2);
lean_inc(x_40);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_37, 1);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_38, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_39, 2);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_40, 2);
lean_dec(x_48);
lean_ctor_set(x_40, 2, x_34);
return x_37;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_40);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_34);
lean_ctor_set(x_39, 2, x_51);
return x_37;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_39, 0);
x_53 = lean_ctor_get(x_39, 1);
x_54 = lean_ctor_get(x_39, 3);
x_55 = lean_ctor_get(x_39, 4);
x_56 = lean_ctor_get(x_39, 5);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_39);
x_57 = lean_ctor_get(x_40, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_40, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 x_59 = x_40;
} else {
 lean_dec_ref(x_40);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 3, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_34);
x_61 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_53);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_54);
lean_ctor_set(x_61, 4, x_55);
lean_ctor_set(x_61, 5, x_56);
lean_ctor_set(x_38, 0, x_61);
return x_37;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_62 = lean_ctor_get(x_38, 1);
x_63 = lean_ctor_get(x_38, 2);
x_64 = lean_ctor_get(x_38, 3);
x_65 = lean_ctor_get(x_38, 4);
x_66 = lean_ctor_get(x_38, 5);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_38);
x_67 = lean_ctor_get(x_39, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_39, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_39, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_39, 4);
lean_inc(x_70);
x_71 = lean_ctor_get(x_39, 5);
lean_inc(x_71);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 x_72 = x_39;
} else {
 lean_dec_ref(x_39);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_40, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_40, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 x_75 = x_40;
} else {
 lean_dec_ref(x_40);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 3, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_34);
if (lean_is_scalar(x_72)) {
 x_77 = lean_alloc_ctor(0, 6, 0);
} else {
 x_77 = x_72;
}
lean_ctor_set(x_77, 0, x_67);
lean_ctor_set(x_77, 1, x_68);
lean_ctor_set(x_77, 2, x_76);
lean_ctor_set(x_77, 3, x_69);
lean_ctor_set(x_77, 4, x_70);
lean_ctor_set(x_77, 5, x_71);
x_78 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_62);
lean_ctor_set(x_78, 2, x_63);
lean_ctor_set(x_78, 3, x_64);
lean_ctor_set(x_78, 4, x_65);
lean_ctor_set(x_78, 5, x_66);
lean_ctor_set(x_37, 1, x_78);
return x_37;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_79 = lean_ctor_get(x_37, 0);
lean_inc(x_79);
lean_dec(x_37);
x_80 = lean_ctor_get(x_38, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_38, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_38, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_38, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_38, 5);
lean_inc(x_84);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 x_85 = x_38;
} else {
 lean_dec_ref(x_38);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_39, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_39, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_39, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_39, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_39, 5);
lean_inc(x_90);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 x_91 = x_39;
} else {
 lean_dec_ref(x_39);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_40, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_40, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 x_94 = x_40;
} else {
 lean_dec_ref(x_40);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 3, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_34);
if (lean_is_scalar(x_91)) {
 x_96 = lean_alloc_ctor(0, 6, 0);
} else {
 x_96 = x_91;
}
lean_ctor_set(x_96, 0, x_86);
lean_ctor_set(x_96, 1, x_87);
lean_ctor_set(x_96, 2, x_95);
lean_ctor_set(x_96, 3, x_88);
lean_ctor_set(x_96, 4, x_89);
lean_ctor_set(x_96, 5, x_90);
if (lean_is_scalar(x_85)) {
 x_97 = lean_alloc_ctor(0, 6, 0);
} else {
 x_97 = x_85;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_80);
lean_ctor_set(x_97, 2, x_81);
lean_ctor_set(x_97, 3, x_82);
lean_ctor_set(x_97, 4, x_83);
lean_ctor_set(x_97, 5, x_84);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_79);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_99 = lean_ctor_get(x_37, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 2);
lean_inc(x_101);
x_102 = !lean_is_exclusive(x_37);
if (x_102 == 0)
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_ctor_get(x_37, 1);
lean_dec(x_103);
x_104 = !lean_is_exclusive(x_99);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_99, 0);
lean_dec(x_105);
x_106 = !lean_is_exclusive(x_100);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_100, 2);
lean_dec(x_107);
x_108 = !lean_is_exclusive(x_101);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_101, 2);
lean_dec(x_109);
lean_ctor_set(x_101, 2, x_34);
return x_37;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_101, 0);
x_111 = lean_ctor_get(x_101, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_101);
x_112 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_112, 2, x_34);
lean_ctor_set(x_100, 2, x_112);
return x_37;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_113 = lean_ctor_get(x_100, 0);
x_114 = lean_ctor_get(x_100, 1);
x_115 = lean_ctor_get(x_100, 3);
x_116 = lean_ctor_get(x_100, 4);
x_117 = lean_ctor_get(x_100, 5);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_100);
x_118 = lean_ctor_get(x_101, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_101, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 x_120 = x_101;
} else {
 lean_dec_ref(x_101);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 3, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
lean_ctor_set(x_121, 2, x_34);
x_122 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_122, 0, x_113);
lean_ctor_set(x_122, 1, x_114);
lean_ctor_set(x_122, 2, x_121);
lean_ctor_set(x_122, 3, x_115);
lean_ctor_set(x_122, 4, x_116);
lean_ctor_set(x_122, 5, x_117);
lean_ctor_set(x_99, 0, x_122);
return x_37;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_123 = lean_ctor_get(x_99, 1);
x_124 = lean_ctor_get(x_99, 2);
x_125 = lean_ctor_get(x_99, 3);
x_126 = lean_ctor_get(x_99, 4);
x_127 = lean_ctor_get(x_99, 5);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_99);
x_128 = lean_ctor_get(x_100, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_100, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_100, 3);
lean_inc(x_130);
x_131 = lean_ctor_get(x_100, 4);
lean_inc(x_131);
x_132 = lean_ctor_get(x_100, 5);
lean_inc(x_132);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 lean_ctor_release(x_100, 2);
 lean_ctor_release(x_100, 3);
 lean_ctor_release(x_100, 4);
 lean_ctor_release(x_100, 5);
 x_133 = x_100;
} else {
 lean_dec_ref(x_100);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_101, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_101, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 x_136 = x_101;
} else {
 lean_dec_ref(x_101);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 3, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
lean_ctor_set(x_137, 2, x_34);
if (lean_is_scalar(x_133)) {
 x_138 = lean_alloc_ctor(0, 6, 0);
} else {
 x_138 = x_133;
}
lean_ctor_set(x_138, 0, x_128);
lean_ctor_set(x_138, 1, x_129);
lean_ctor_set(x_138, 2, x_137);
lean_ctor_set(x_138, 3, x_130);
lean_ctor_set(x_138, 4, x_131);
lean_ctor_set(x_138, 5, x_132);
x_139 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_123);
lean_ctor_set(x_139, 2, x_124);
lean_ctor_set(x_139, 3, x_125);
lean_ctor_set(x_139, 4, x_126);
lean_ctor_set(x_139, 5, x_127);
lean_ctor_set(x_37, 1, x_139);
return x_37;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_140 = lean_ctor_get(x_37, 0);
lean_inc(x_140);
lean_dec(x_37);
x_141 = lean_ctor_get(x_99, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_99, 2);
lean_inc(x_142);
x_143 = lean_ctor_get(x_99, 3);
lean_inc(x_143);
x_144 = lean_ctor_get(x_99, 4);
lean_inc(x_144);
x_145 = lean_ctor_get(x_99, 5);
lean_inc(x_145);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 lean_ctor_release(x_99, 2);
 lean_ctor_release(x_99, 3);
 lean_ctor_release(x_99, 4);
 lean_ctor_release(x_99, 5);
 x_146 = x_99;
} else {
 lean_dec_ref(x_99);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_100, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_100, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_100, 3);
lean_inc(x_149);
x_150 = lean_ctor_get(x_100, 4);
lean_inc(x_150);
x_151 = lean_ctor_get(x_100, 5);
lean_inc(x_151);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 lean_ctor_release(x_100, 2);
 lean_ctor_release(x_100, 3);
 lean_ctor_release(x_100, 4);
 lean_ctor_release(x_100, 5);
 x_152 = x_100;
} else {
 lean_dec_ref(x_100);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_101, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_101, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 x_155 = x_101;
} else {
 lean_dec_ref(x_101);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 3, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
lean_ctor_set(x_156, 2, x_34);
if (lean_is_scalar(x_152)) {
 x_157 = lean_alloc_ctor(0, 6, 0);
} else {
 x_157 = x_152;
}
lean_ctor_set(x_157, 0, x_147);
lean_ctor_set(x_157, 1, x_148);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_157, 3, x_149);
lean_ctor_set(x_157, 4, x_150);
lean_ctor_set(x_157, 5, x_151);
if (lean_is_scalar(x_146)) {
 x_158 = lean_alloc_ctor(0, 6, 0);
} else {
 x_158 = x_146;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_141);
lean_ctor_set(x_158, 2, x_142);
lean_ctor_set(x_158, 3, x_143);
lean_ctor_set(x_158, 4, x_144);
lean_ctor_set(x_158, 5, x_145);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_140);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
}
}
else
{
uint8_t x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_164 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_165 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_166 = lean_ctor_get(x_6, 0);
x_167 = lean_ctor_get(x_6, 2);
x_168 = lean_ctor_get(x_6, 3);
x_169 = lean_ctor_get(x_6, 4);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_6);
x_170 = lean_ctor_get(x_7, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_7, 4);
lean_inc(x_171);
x_172 = lean_array_get_size(x_167);
x_173 = lean_array_get_size(x_171);
x_174 = lean_nat_dec_eq(x_172, x_173);
lean_dec(x_173);
lean_dec(x_172);
lean_inc(x_171);
x_175 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_175, 0, x_166);
lean_ctor_set(x_175, 1, x_170);
lean_ctor_set(x_175, 2, x_171);
lean_ctor_set(x_175, 3, x_168);
lean_ctor_set(x_175, 4, x_169);
x_176 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_9);
lean_ctor_set(x_176, 2, x_10);
lean_ctor_set(x_176, 3, x_11);
lean_ctor_set(x_176, 4, x_12);
lean_ctor_set(x_176, 5, x_13);
lean_ctor_set(x_176, 6, x_14);
lean_ctor_set(x_176, 7, x_15);
lean_ctor_set(x_176, 8, x_16);
lean_ctor_set(x_176, 9, x_17);
lean_ctor_set_uint8(x_176, sizeof(void*)*10, x_164);
lean_ctor_set_uint8(x_176, sizeof(void*)*10 + 1, x_165);
if (x_174 == 0)
{
uint8_t x_235; 
lean_dec(x_171);
lean_dec(x_167);
lean_dec(x_7);
lean_dec(x_3);
x_235 = 0;
x_177 = x_235;
goto block_234;
}
else
{
lean_object* x_236; uint8_t x_237; 
x_236 = lean_unsigned_to_nat(0u);
x_237 = l_Array_isEqvAux___main___at_Lean_Elab_Term_withMVarContext___spec__1(x_3, x_7, lean_box(0), x_167, x_171, x_236);
lean_dec(x_171);
lean_dec(x_167);
lean_dec(x_7);
lean_dec(x_3);
x_177 = x_237;
goto block_234;
}
block_234:
{
uint8_t x_178; 
x_178 = l_coeDecidableEq(x_177);
if (x_178 == 0)
{
lean_object* x_179; 
x_179 = lean_apply_2(x_2, x_176, x_8);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_180 = lean_ctor_get(x_8, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_180, 2);
lean_inc(x_181);
lean_dec(x_180);
x_182 = lean_ctor_get(x_181, 2);
lean_inc(x_182);
lean_dec(x_181);
x_183 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_8);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_apply_2(x_2, x_176, x_184);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_187, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_185, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_190 = x_185;
} else {
 lean_dec_ref(x_185);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_186, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_186, 2);
lean_inc(x_192);
x_193 = lean_ctor_get(x_186, 3);
lean_inc(x_193);
x_194 = lean_ctor_get(x_186, 4);
lean_inc(x_194);
x_195 = lean_ctor_get(x_186, 5);
lean_inc(x_195);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 lean_ctor_release(x_186, 2);
 lean_ctor_release(x_186, 3);
 lean_ctor_release(x_186, 4);
 lean_ctor_release(x_186, 5);
 x_196 = x_186;
} else {
 lean_dec_ref(x_186);
 x_196 = lean_box(0);
}
x_197 = lean_ctor_get(x_187, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_187, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_187, 3);
lean_inc(x_199);
x_200 = lean_ctor_get(x_187, 4);
lean_inc(x_200);
x_201 = lean_ctor_get(x_187, 5);
lean_inc(x_201);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 lean_ctor_release(x_187, 4);
 lean_ctor_release(x_187, 5);
 x_202 = x_187;
} else {
 lean_dec_ref(x_187);
 x_202 = lean_box(0);
}
x_203 = lean_ctor_get(x_188, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_188, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 x_205 = x_188;
} else {
 lean_dec_ref(x_188);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(0, 3, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_204);
lean_ctor_set(x_206, 2, x_182);
if (lean_is_scalar(x_202)) {
 x_207 = lean_alloc_ctor(0, 6, 0);
} else {
 x_207 = x_202;
}
lean_ctor_set(x_207, 0, x_197);
lean_ctor_set(x_207, 1, x_198);
lean_ctor_set(x_207, 2, x_206);
lean_ctor_set(x_207, 3, x_199);
lean_ctor_set(x_207, 4, x_200);
lean_ctor_set(x_207, 5, x_201);
if (lean_is_scalar(x_196)) {
 x_208 = lean_alloc_ctor(0, 6, 0);
} else {
 x_208 = x_196;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_191);
lean_ctor_set(x_208, 2, x_192);
lean_ctor_set(x_208, 3, x_193);
lean_ctor_set(x_208, 4, x_194);
lean_ctor_set(x_208, 5, x_195);
if (lean_is_scalar(x_190)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_190;
}
lean_ctor_set(x_209, 0, x_189);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_210 = lean_ctor_get(x_185, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_211, 2);
lean_inc(x_212);
x_213 = lean_ctor_get(x_185, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_214 = x_185;
} else {
 lean_dec_ref(x_185);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_210, 1);
lean_inc(x_215);
x_216 = lean_ctor_get(x_210, 2);
lean_inc(x_216);
x_217 = lean_ctor_get(x_210, 3);
lean_inc(x_217);
x_218 = lean_ctor_get(x_210, 4);
lean_inc(x_218);
x_219 = lean_ctor_get(x_210, 5);
lean_inc(x_219);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 lean_ctor_release(x_210, 4);
 lean_ctor_release(x_210, 5);
 x_220 = x_210;
} else {
 lean_dec_ref(x_210);
 x_220 = lean_box(0);
}
x_221 = lean_ctor_get(x_211, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_211, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_211, 3);
lean_inc(x_223);
x_224 = lean_ctor_get(x_211, 4);
lean_inc(x_224);
x_225 = lean_ctor_get(x_211, 5);
lean_inc(x_225);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 lean_ctor_release(x_211, 2);
 lean_ctor_release(x_211, 3);
 lean_ctor_release(x_211, 4);
 lean_ctor_release(x_211, 5);
 x_226 = x_211;
} else {
 lean_dec_ref(x_211);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_212, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_212, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 lean_ctor_release(x_212, 2);
 x_229 = x_212;
} else {
 lean_dec_ref(x_212);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(0, 3, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
lean_ctor_set(x_230, 2, x_182);
if (lean_is_scalar(x_226)) {
 x_231 = lean_alloc_ctor(0, 6, 0);
} else {
 x_231 = x_226;
}
lean_ctor_set(x_231, 0, x_221);
lean_ctor_set(x_231, 1, x_222);
lean_ctor_set(x_231, 2, x_230);
lean_ctor_set(x_231, 3, x_223);
lean_ctor_set(x_231, 4, x_224);
lean_ctor_set(x_231, 5, x_225);
if (lean_is_scalar(x_220)) {
 x_232 = lean_alloc_ctor(0, 6, 0);
} else {
 x_232 = x_220;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_215);
lean_ctor_set(x_232, 2, x_216);
lean_ctor_set(x_232, 3, x_217);
lean_ctor_set(x_232, 4, x_218);
lean_ctor_set(x_232, 5, x_219);
if (lean_is_scalar(x_214)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_214;
}
lean_ctor_set(x_233, 0, x_213);
lean_ctor_set(x_233, 1, x_232);
return x_233;
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
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Lean_Elab_Term_getMVarDecl(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_3);
x_9 = l_Lean_Elab_Term_instantiateMVars(x_1, x_8, x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_3);
lean_inc(x_10);
x_12 = l_Lean_Elab_Term_trySynthInstance(x_1, x_10, x_3, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
switch (lean_obj_tag(x_13)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_10);
x_16 = l_Lean_indentExpr(x_15);
x_17 = l_Lean_Elab_Term_synthesizeInstMVarCore___closed__3;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Elab_Term_throwError___rarg(x_1, x_18, x_3, x_14);
return x_19;
}
case 1:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_10);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
lean_inc(x_2);
x_22 = l_Lean_Elab_Term_isExprMVarAssigned(x_2, x_3, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Lean_Elab_Term_assignExprMVar(x_2, x_21, x_3, x_25);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = 1;
x_30 = lean_box(x_29);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = 1;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_dec(x_22);
x_36 = l_Lean_mkMVar(x_2);
lean_inc(x_3);
x_37 = l_Lean_Elab_Term_instantiateMVars(x_1, x_36, x_3, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_3);
lean_inc(x_21);
lean_inc(x_38);
x_40 = l_Lean_Elab_Term_isDefEq(x_1, x_38, x_21, x_3, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_21);
x_45 = l_Lean_indentExpr(x_44);
x_46 = l_Lean_Elab_Term_synthesizeInstMVarCore___closed__10;
x_47 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_MessageData_ofList___closed__3;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Elab_Term_synthesizeInstMVarCore___closed__13;
x_51 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_38);
x_53 = l_Lean_indentExpr(x_52);
x_54 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Elab_Term_throwError___rarg(x_1, x_54, x_3, x_43);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_55);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_38);
lean_dec(x_21);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_40);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_40, 0);
lean_dec(x_61);
x_62 = 1;
x_63 = lean_box(x_62);
lean_ctor_set(x_40, 0, x_63);
return x_40;
}
else
{
lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_40, 1);
lean_inc(x_64);
lean_dec(x_40);
x_65 = 1;
x_66 = lean_box(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_38);
lean_dec(x_21);
lean_dec(x_3);
x_68 = !lean_is_exclusive(x_40);
if (x_68 == 0)
{
return x_40;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_40, 0);
x_70 = lean_ctor_get(x_40, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_40);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
default: 
{
uint8_t x_72; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_12);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_12, 0);
lean_dec(x_73);
x_74 = 0;
x_75 = lean_box(x_74);
lean_ctor_set(x_12, 0, x_75);
return x_12;
}
else
{
lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_12, 1);
lean_inc(x_76);
lean_dec(x_12);
x_77 = 0;
x_78 = lean_box(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_12);
if (x_80 == 0)
{
return x_12;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_12, 0);
x_82 = lean_ctor_get(x_12, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_12);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_mkInstMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = 1;
x_7 = lean_box(0);
lean_inc(x_3);
x_8 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_5, x_6, x_7, x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_mvarId_x21(x_9);
lean_inc(x_3);
lean_inc(x_11);
x_12 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_1, x_11, x_3, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Term_registerSyntheticMVar(x_1, x_11, x_16, x_3, x_15);
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
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_12, 0);
lean_dec(x_23);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
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
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_30; 
x_30 = l_Lean_MessageData_Inhabited___closed__1;
x_9 = x_30;
goto block_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_5, 0);
lean_inc(x_31);
lean_dec(x_5);
x_32 = l_Lean_Elab_Term_getEnv___rarg(x_8);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Elab_Term_getMCtx___rarg(x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Term_getLCtx(x_7, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Elab_Term_getOptions(x_7, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_42);
x_45 = l_Lean_Meta_Exception_mkAppTypeMismatchMessage(x_31, x_4, x_44);
x_46 = l_Lean_MessageData_Inhabited___closed__1;
x_47 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Elab_Term_throwError___rarg(x_1, x_47, x_7, x_43);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_6, 0);
x_50 = l_Lean_MessageData_ofList___closed__3;
lean_inc(x_49);
x_51 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
if (lean_obj_tag(x_5) == 0)
{
x_9 = x_51;
goto block_29;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_ctor_get(x_5, 0);
lean_inc(x_52);
lean_dec(x_5);
x_53 = l_Lean_Elab_Term_getEnv___rarg(x_8);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Elab_Term_getMCtx___rarg(x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Elab_Term_getLCtx(x_7, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Elab_Term_getOptions(x_7, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_54);
lean_ctor_set(x_65, 1, x_57);
lean_ctor_set(x_65, 2, x_60);
lean_ctor_set(x_65, 3, x_63);
x_66 = l_Lean_Meta_Exception_mkAppTypeMismatchMessage(x_52, x_4, x_65);
x_67 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_51);
x_68 = l_Lean_Elab_Term_throwError___rarg(x_1, x_67, x_7, x_64);
return x_68;
}
}
block_29:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_11 = l_Lean_indentExpr(x_10);
x_12 = l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_MessageData_ofList___closed__3;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_Exception_mkAppTypeMismatchMessage___closed__8;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_3);
x_19 = l_Lean_indentExpr(x_18);
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
x_22 = l_Lean_KernelException_toMessageData___closed__12;
x_23 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_2);
x_25 = l_Lean_indentExpr(x_24);
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
x_28 = l_Lean_Elab_Term_throwError___rarg(x_1, x_27, x_7, x_8);
return x_28;
}
}
}
lean_object* l_Lean_Elab_Term_throwTypeMismatchError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwTypeMismatchError___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
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
lean_object* l_Lean_Elab_Term_tryCoe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_3);
x_8 = l_Lean_Elab_Term_getLevel(x_1, x_3, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_11 = l_Lean_Elab_Term_getLevel(x_1, x_2, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_Term_tryCoe___closed__2;
lean_inc(x_16);
x_18 = l_Lean_mkConst(x_17, x_16);
x_19 = l_Lean_Parser_declareBuiltinParser___closed__8;
lean_inc(x_3);
x_20 = lean_array_push(x_19, x_3);
lean_inc(x_4);
x_21 = lean_array_push(x_20, x_4);
lean_inc(x_2);
x_22 = lean_array_push(x_21, x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_22, x_22, x_23, x_18);
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = 1;
x_27 = lean_box(0);
lean_inc(x_6);
x_28 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_25, x_26, x_27, x_6, x_13);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Term_tryCoe___closed__4;
x_32 = l_Lean_mkConst(x_31, x_16);
x_33 = l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_inc(x_3);
x_34 = lean_array_push(x_33, x_3);
lean_inc(x_2);
x_35 = lean_array_push(x_34, x_2);
lean_inc(x_4);
x_36 = lean_array_push(x_35, x_4);
lean_inc(x_29);
x_37 = lean_array_push(x_36, x_29);
x_38 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_37, x_37, x_23, x_32);
lean_dec(x_37);
x_39 = l_Lean_Expr_mvarId_x21(x_29);
lean_dec(x_29);
lean_inc(x_6);
lean_inc(x_39);
x_40 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_1, x_39, x_6, x_30);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_3);
lean_ctor_set(x_44, 2, x_4);
lean_ctor_set(x_44, 3, x_5);
x_45 = l_Lean_Elab_Term_registerSyntheticMVar(x_1, x_39, x_44, x_6, x_43);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_38);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_39);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_40);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_40, 0);
lean_dec(x_51);
lean_ctor_set(x_40, 0, x_38);
return x_40;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
lean_dec(x_40);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_38);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_39);
lean_dec(x_38);
x_54 = lean_ctor_get(x_40, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec(x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_40, 1);
lean_inc(x_56);
lean_dec(x_40);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_57, 4);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_2, x_3, x_4, x_5, x_59, x_6, x_56);
lean_dec(x_59);
lean_dec(x_1);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_40, 1);
lean_inc(x_61);
lean_dec(x_40);
x_62 = lean_box(0);
x_63 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_2, x_3, x_4, x_5, x_62, x_6, x_61);
lean_dec(x_1);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_40, 1);
lean_inc(x_64);
lean_dec(x_40);
x_65 = lean_box(0);
x_66 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_2, x_3, x_4, x_5, x_65, x_6, x_64);
lean_dec(x_1);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_11);
if (x_67 == 0)
{
return x_11;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_11, 0);
x_69 = lean_ctor_get(x_11, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_11);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_8);
if (x_71 == 0)
{
return x_8;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_8, 0);
x_73 = lean_ctor_get(x_8, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_8);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
lean_object* l_Lean_Elab_Term_ensureHasTypeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_9);
lean_inc(x_3);
x_10 = l_Lean_Elab_Term_isDefEq(x_1, x_3, x_9, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Elab_Term_tryCoe(x_1, x_9, x_3, x_4, x_5, x_6, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_10, 0);
lean_dec(x_16);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Elab_Term_inferType(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = l_Lean_Elab_Term_ensureHasTypeAux(x_1, x_2, x_8, x_3, x_10, x_4, x_9);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabProp");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabProp___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_prop___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabSort___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_Term_elabSort(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSort___rarg), 1, 0);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabSort___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_elabSort(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabSort");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSort___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSort(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_sort___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_elabTypeStx___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelOne;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabTypeStx___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_elabTypeStx___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabTypeStx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTypeStx___rarg), 1, 0);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabTypeStx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_elabTypeStx(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabTypeStx");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTypeStx___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_type___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabHole(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = 0;
x_6 = lean_box(0);
x_7 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabHole___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabHole(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabHole");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabHole___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabHole(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_mkHole___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
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
x_8 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_2, x_7, x_6, x_3, x_4);
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabNamedHole");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNamedHole___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_namedHole___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
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
lean_object* l_Lean_Elab_Term_mkTacticMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = 2;
x_8 = l_Lean_Elab_Term_mkTacticMVar___closed__2;
lean_inc(x_4);
x_9 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_6, x_7, x_8, x_4, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_mvarId_x21(x_10);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_3);
x_14 = l_Lean_Elab_Term_registerSyntheticMVar(x_1, x_12, x_13, x_4, x_11);
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_10);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
return x_18;
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
x_6 = l_Lean_Elab_Term_throwError___rarg(x_1, x_5, x_3, x_4);
lean_dec(x_1);
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
x_10 = l_Lean_Elab_Term_mkTacticMVar(x_1, x_7, x_9, x_3, x_4);
return x_10;
}
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabTacticBlock");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTacticBlock), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Prod.mk");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Prod");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mk");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__5;
x_2 = l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Term_9__mkPairsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
lean_dec(x_2);
x_11 = l_Lean_Syntax_inhabited;
x_12 = lean_array_get(x_11, x_1, x_10);
x_13 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_getMainModule___rarg(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__7;
x_21 = l_Lean_addMacroScope(x_17, x_20, x_14);
x_22 = l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__3;
x_23 = l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__9;
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_23);
x_25 = l_Array_empty___closed__1;
x_26 = lean_array_push(x_25, x_24);
x_27 = l___private_Init_Lean_Elab_Term_5__expandCDot___closed__4;
x_28 = lean_array_push(x_26, x_27);
x_29 = l_Lean_mkTermIdFromIdent___closed__2;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_array_push(x_25, x_30);
x_32 = lean_array_push(x_25, x_12);
x_33 = lean_array_push(x_32, x_3);
x_34 = l_Lean_nullKind___closed__2;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_array_push(x_31, x_35);
x_37 = l_Lean_mkAppStx___closed__8;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_2 = x_10;
x_3 = x_38;
x_5 = x_18;
goto _start;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Term_9__mkPairsAux___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Term_9__mkPairsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Term_9__mkPairsAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Term_9__mkPairsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Term_9__mkPairsAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
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
x_7 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(x_1);
x_8 = l___private_Init_Lean_Elab_Term_9__mkPairsAux___main(x_1, x_6, x_7, x_2, x_3);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_mkPairs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_mkPairs(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Term_10__elabCDot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Elab_Term_expandCDot_x3f(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = 1;
x_9 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_8, x_1, x_3, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_3, 8);
lean_inc(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_3, 8, x_15);
x_16 = 1;
x_17 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_16, x_11, x_3, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 2);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_3, 4);
x_23 = lean_ctor_get(x_3, 5);
x_24 = lean_ctor_get(x_3, 6);
x_25 = lean_ctor_get(x_3, 7);
x_26 = lean_ctor_get(x_3, 8);
x_27 = lean_ctor_get(x_3, 9);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_29 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
lean_inc(x_11);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_11);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_19);
lean_ctor_set(x_32, 2, x_20);
lean_ctor_set(x_32, 3, x_21);
lean_ctor_set(x_32, 4, x_22);
lean_ctor_set(x_32, 5, x_23);
lean_ctor_set(x_32, 6, x_24);
lean_ctor_set(x_32, 7, x_25);
lean_ctor_set(x_32, 8, x_31);
lean_ctor_set(x_32, 9, x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*10, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*10 + 1, x_29);
x_33 = 1;
x_34 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_33, x_11, x_32, x_10);
return x_34;
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
lean_object* _init_l_Lean_Elab_Term_elabParen___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unit");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabParen___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareBuiltinParser___closed__5;
x_2 = l_Lean_Elab_Term_elabParen___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabParen___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabParen___closed__5;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabParen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_147; uint8_t x_148; 
x_147 = l___private_Init_Lean_Parser_Parser_13__antiquotNestedExpr___elambda__1___rarg___closed__2;
lean_inc(x_1);
x_148 = l_Lean_Syntax_isOfKind(x_1, x_147);
if (x_148 == 0)
{
uint8_t x_149; 
x_149 = 0;
x_5 = x_149;
goto block_146;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_150 = l_Lean_Syntax_getArgs(x_1);
x_151 = lean_array_get_size(x_150);
lean_dec(x_150);
x_152 = lean_unsigned_to_nat(3u);
x_153 = lean_nat_dec_eq(x_151, x_152);
lean_dec(x_151);
x_5 = x_153;
goto block_146;
}
block_146:
{
uint8_t x_6; 
x_6 = l_coeDecidableEq(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = l_Lean_Elab_Term_elabParen___closed__3;
x_8 = l_Lean_Elab_Term_throwError___rarg(x_1, x_7, x_3, x_4);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_131; uint8_t x_132; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_131 = l_Lean_nullKind___closed__2;
lean_inc(x_10);
x_132 = l_Lean_Syntax_isOfKind(x_10, x_131);
if (x_132 == 0)
{
uint8_t x_133; 
x_133 = l_String_posOfAux___main___closed__1;
if (x_133 == 0)
{
uint8_t x_134; 
x_134 = 0;
x_11 = x_134;
goto block_130;
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_135 = l_Lean_Elab_Term_elabParen___closed__6;
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_4);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_141; 
x_137 = l_Lean_Syntax_getArgs(x_10);
x_138 = lean_array_get_size(x_137);
lean_dec(x_137);
x_139 = lean_unsigned_to_nat(0u);
x_140 = lean_nat_dec_eq(x_138, x_139);
x_141 = l_coeDecidableEq(x_140);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_unsigned_to_nat(2u);
x_143 = lean_nat_dec_eq(x_138, x_142);
lean_dec(x_138);
x_11 = x_143;
goto block_130;
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_138);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_144 = l_Lean_Elab_Term_elabParen___closed__6;
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_4);
return x_145;
}
}
block_130:
{
uint8_t x_12; 
x_12 = l_coeDecidableEq(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_2);
x_13 = l_Lean_Elab_Term_elabParen___closed__3;
x_14 = l_Lean_Elab_Term_throwError___rarg(x_1, x_13, x_3, x_4);
lean_dec(x_1);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getArg(x_10, x_15);
x_17 = l_Lean_Syntax_getArg(x_10, x_9);
lean_dec(x_10);
x_18 = l_Lean_nullKind___closed__2;
lean_inc(x_17);
x_19 = l_Lean_Syntax_isOfKind(x_17, x_18);
if (x_19 == 0)
{
uint8_t x_126; 
x_126 = 0;
x_20 = x_126;
goto block_125;
}
else
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = l_Lean_Syntax_getArgs(x_17);
x_128 = lean_array_get_size(x_127);
lean_dec(x_127);
x_129 = lean_nat_dec_eq(x_128, x_9);
lean_dec(x_128);
x_20 = x_129;
goto block_125;
}
block_125:
{
uint8_t x_21; 
x_21 = l_coeDecidableEq(x_20);
if (x_21 == 0)
{
if (x_19 == 0)
{
uint8_t x_22; 
lean_dec(x_17);
x_22 = l_String_posOfAux___main___closed__1;
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_16);
lean_dec(x_2);
x_23 = l_Lean_Elab_Term_elabParen___closed__3;
x_24 = l_Lean_Elab_Term_throwError___rarg(x_1, x_23, x_3, x_4);
lean_dec(x_1);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = l___private_Init_Lean_Elab_Term_10__elabCDot(x_16, x_2, x_3, x_4);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; 
x_26 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_27 = lean_array_get_size(x_26);
lean_dec(x_26);
x_28 = lean_nat_dec_eq(x_27, x_15);
lean_dec(x_27);
x_29 = l_coeDecidableEq(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_16);
lean_dec(x_2);
x_30 = l_Lean_Elab_Term_elabParen___closed__3;
x_31 = l_Lean_Elab_Term_throwError___rarg(x_1, x_30, x_3, x_4);
lean_dec(x_1);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_1);
x_32 = l___private_Init_Lean_Elab_Term_10__elabCDot(x_16, x_2, x_3, x_4);
return x_32;
}
}
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_73; uint8_t x_74; 
x_33 = l_Lean_Syntax_getArg(x_17, x_15);
lean_dec(x_17);
x_73 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__2;
lean_inc(x_33);
x_74 = l_Lean_Syntax_isOfKind(x_33, x_73);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = l_String_posOfAux___main___closed__1;
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = l_Lean_Parser_Term_tupleTail___elambda__1___closed__2;
lean_inc(x_33);
x_77 = l_Lean_Syntax_isOfKind(x_33, x_76);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = 0;
x_34 = x_78;
goto block_72;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = l_Lean_Syntax_getArgs(x_33);
x_80 = lean_array_get_size(x_79);
lean_dec(x_79);
x_81 = lean_unsigned_to_nat(2u);
x_82 = lean_nat_dec_eq(x_80, x_81);
lean_dec(x_80);
x_34 = x_82;
goto block_72;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_2);
x_83 = l_Lean_Syntax_getArg(x_33, x_9);
lean_dec(x_33);
lean_inc(x_3);
x_84 = l_Lean_Elab_Term_elabType(x_83, x_3, x_4);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_85);
lean_inc(x_3);
lean_inc(x_87);
x_88 = l___private_Init_Lean_Elab_Term_10__elabCDot(x_16, x_87, x_3, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Elab_Term_ensureHasType(x_1, x_87, x_89, x_3, x_90);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec(x_87);
lean_dec(x_3);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
return x_88;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_88, 0);
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_88);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_84);
if (x_96 == 0)
{
return x_84;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_84, 0);
x_98 = lean_ctor_get(x_84, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_84);
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
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_104; 
x_100 = l_Lean_Syntax_getArgs(x_33);
x_101 = lean_array_get_size(x_100);
lean_dec(x_100);
x_102 = lean_unsigned_to_nat(2u);
x_103 = lean_nat_dec_eq(x_101, x_102);
lean_dec(x_101);
x_104 = l_coeDecidableEq(x_103);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = l_Lean_Parser_Term_tupleTail___elambda__1___closed__2;
lean_inc(x_33);
x_106 = l_Lean_Syntax_isOfKind(x_33, x_105);
if (x_106 == 0)
{
uint8_t x_107; 
x_107 = 0;
x_34 = x_107;
goto block_72;
}
else
{
x_34 = x_103;
goto block_72;
}
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_2);
x_108 = l_Lean_Syntax_getArg(x_33, x_9);
lean_dec(x_33);
lean_inc(x_3);
x_109 = l_Lean_Elab_Term_elabType(x_108, x_3, x_4);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_110);
lean_inc(x_3);
lean_inc(x_112);
x_113 = l___private_Init_Lean_Elab_Term_10__elabCDot(x_16, x_112, x_3, x_111);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_Elab_Term_ensureHasType(x_1, x_112, x_114, x_3, x_115);
return x_116;
}
else
{
uint8_t x_117; 
lean_dec(x_112);
lean_dec(x_3);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_113);
if (x_117 == 0)
{
return x_113;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_113, 0);
x_119 = lean_ctor_get(x_113, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_113);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_109);
if (x_121 == 0)
{
return x_109;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_109, 0);
x_123 = lean_ctor_get(x_109, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_109);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
block_72:
{
uint8_t x_35; 
x_35 = l_coeDecidableEq(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_33);
lean_dec(x_16);
lean_dec(x_2);
x_36 = l_Lean_Elab_Term_elabParen___closed__3;
x_37 = l_Lean_Elab_Term_throwError___rarg(x_1, x_36, x_3, x_4);
lean_dec(x_1);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_38 = l_Lean_Syntax_getArg(x_33, x_9);
lean_dec(x_33);
x_39 = l_Lean_Syntax_getArgs(x_38);
lean_dec(x_38);
x_40 = l_Lean_mkOptionalNode___closed__2;
x_41 = lean_array_push(x_40, x_16);
x_42 = lean_unsigned_to_nat(2u);
x_43 = l_Array_empty___closed__1;
x_44 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_42, x_39, x_15, x_43);
lean_dec(x_39);
x_45 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_44, x_44, x_15, x_41);
lean_dec(x_44);
x_46 = l_Lean_Elab_Term_mkPairs(x_45, x_3, x_4);
lean_dec(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = !lean_is_exclusive(x_3);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_3, 8);
lean_inc(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_47);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_3, 8, x_52);
x_53 = 1;
x_54 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_53, x_47, x_3, x_48);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_55 = lean_ctor_get(x_3, 0);
x_56 = lean_ctor_get(x_3, 1);
x_57 = lean_ctor_get(x_3, 2);
x_58 = lean_ctor_get(x_3, 3);
x_59 = lean_ctor_get(x_3, 4);
x_60 = lean_ctor_get(x_3, 5);
x_61 = lean_ctor_get(x_3, 6);
x_62 = lean_ctor_get(x_3, 7);
x_63 = lean_ctor_get(x_3, 8);
x_64 = lean_ctor_get(x_3, 9);
x_65 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_66 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_3);
lean_inc(x_47);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_47);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
x_69 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_69, 0, x_55);
lean_ctor_set(x_69, 1, x_56);
lean_ctor_set(x_69, 2, x_57);
lean_ctor_set(x_69, 3, x_58);
lean_ctor_set(x_69, 4, x_59);
lean_ctor_set(x_69, 5, x_60);
lean_ctor_set(x_69, 6, x_61);
lean_ctor_set(x_69, 7, x_62);
lean_ctor_set(x_69, 8, x_68);
lean_ctor_set(x_69, 9, x_64);
lean_ctor_set_uint8(x_69, sizeof(void*)*10, x_65);
lean_ctor_set_uint8(x_69, sizeof(void*)*10 + 1, x_66);
x_70 = 1;
x_71 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_70, x_47, x_69, x_48);
return x_71;
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabParen");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParen), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabParen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Init_Lean_Parser_Parser_13__antiquotNestedExpr___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabListLit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* _init_l_Lean_Elab_Term_elabListLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("List");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabListLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabListLit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabListLit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabListLit___closed__2;
x_2 = l_Lean_Parser_Term_cons___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabListLit___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nil");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabListLit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabListLit___closed__2;
x_2 = l_Lean_Elab_Term_elabListLit___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabListLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Elab_Term_elabListLit___closed__3;
x_12 = l_Lean_mkTermIdFrom(x_6, x_11);
lean_dec(x_6);
x_13 = l_Lean_Elab_Term_elabListLit___closed__5;
x_14 = l_Lean_mkTermIdFrom(x_10, x_13);
lean_dec(x_10);
x_15 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_16 = l_Array_empty___closed__1;
x_17 = l_Array_foldlStepMAux___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(x_9, x_15, x_5, x_16);
lean_dec(x_15);
x_18 = lean_array_get_size(x_17);
x_19 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabListLit___spec__1(x_1, x_12, x_17, x_18, lean_box(0), x_14);
lean_dec(x_17);
x_20 = 1;
x_21 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_20, x_19, x_3, x_4);
return x_21;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabListLit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabListLit___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabListLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabListLit(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabListLit");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabListLit___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabListLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_listLit___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrayLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected array literal syntax");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrayLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabArrayLit___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrayLit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabArrayLit___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrayLit___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("List.toArray");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrayLit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabArrayLit___closed__4;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrayLit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_elabArrayLit___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_elabArrayLit___closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrayLit___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("toArray");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrayLit___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabListLit___closed__2;
x_2 = l_Lean_Elab_Term_elabArrayLit___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrayLit___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabArrayLit___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrayLit___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabArrayLit___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrayLit___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_repr___rarg___closed__2;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrayLit___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_elabArrayLit___closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrayLit___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_repr___rarg___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabArrayLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_70; uint8_t x_71; 
x_70 = l_Lean_Parser_Term_arrayLit___elambda__1___closed__2;
lean_inc(x_1);
x_71 = l_Lean_Syntax_isOfKind(x_1, x_70);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = 0;
x_5 = x_72;
goto block_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = l_Lean_Syntax_getArgs(x_1);
x_74 = lean_array_get_size(x_73);
lean_dec(x_73);
x_75 = lean_unsigned_to_nat(3u);
x_76 = lean_nat_dec_eq(x_74, x_75);
lean_dec(x_74);
x_5 = x_76;
goto block_69;
}
block_69:
{
uint8_t x_6; 
x_6 = l_coeDecidableEq(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = l_Lean_Elab_Term_elabArrayLit___closed__3;
x_8 = l_Lean_Elab_Term_throwError___rarg(x_1, x_7, x_3, x_4);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_12 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Term_getMainModule___rarg(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = l_Lean_Elab_Term_elabArrayLit___closed__8;
x_20 = l_Lean_addMacroScope(x_16, x_19, x_13);
x_21 = l_Lean_Elab_Term_elabArrayLit___closed__6;
x_22 = l_Lean_Elab_Term_elabArrayLit___closed__10;
x_23 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_22);
x_24 = l_Array_empty___closed__1;
x_25 = lean_array_push(x_24, x_23);
x_26 = l___private_Init_Lean_Elab_Term_5__expandCDot___closed__4;
x_27 = lean_array_push(x_25, x_26);
x_28 = l_Lean_mkTermIdFromIdent___closed__2;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_array_push(x_24, x_29);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_11, x_11, x_31, x_24);
lean_dec(x_11);
x_33 = l_Lean_nullKind___closed__2;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Elab_Term_elabArrayLit___closed__12;
x_36 = lean_array_push(x_35, x_34);
x_37 = l_Lean_Elab_Term_elabArrayLit___closed__13;
x_38 = lean_array_push(x_36, x_37);
x_39 = l_Lean_Parser_Term_listLit___elambda__1___closed__2;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_array_push(x_24, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_array_push(x_30, x_42);
x_44 = l_Lean_mkAppStx___closed__8;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = !lean_is_exclusive(x_3);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_3, 8);
lean_inc(x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_3, 8, x_49);
x_50 = 1;
x_51 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_50, x_45, x_3, x_17);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_52 = lean_ctor_get(x_3, 0);
x_53 = lean_ctor_get(x_3, 1);
x_54 = lean_ctor_get(x_3, 2);
x_55 = lean_ctor_get(x_3, 3);
x_56 = lean_ctor_get(x_3, 4);
x_57 = lean_ctor_get(x_3, 5);
x_58 = lean_ctor_get(x_3, 6);
x_59 = lean_ctor_get(x_3, 7);
x_60 = lean_ctor_get(x_3, 8);
x_61 = lean_ctor_get(x_3, 9);
x_62 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_63 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_3);
lean_inc(x_45);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_45);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
x_66 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_66, 0, x_52);
lean_ctor_set(x_66, 1, x_53);
lean_ctor_set(x_66, 2, x_54);
lean_ctor_set(x_66, 3, x_55);
lean_ctor_set(x_66, 4, x_56);
lean_ctor_set(x_66, 5, x_57);
lean_ctor_set(x_66, 6, x_58);
lean_ctor_set(x_66, 7, x_59);
lean_ctor_set(x_66, 8, x_65);
lean_ctor_set(x_66, 9, x_61);
lean_ctor_set_uint8(x_66, sizeof(void*)*10, x_62);
lean_ctor_set_uint8(x_66, sizeof(void*)*10 + 1, x_63);
x_67 = 1;
x_68 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_67, x_45, x_66, x_17);
return x_68;
}
}
}
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabArrayLit");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabArrayLit), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_arrayLit___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_Term_11__resolveLocalNameAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Init_Lean_Elab_Term_11__resolveLocalNameAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Term_11__resolveLocalNameAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Term_12__resolveLocalName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l___private_Init_Lean_Elab_Term_11__resolveLocalNameAux___main(x_6, x_1, x_7);
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
x_12 = l___private_Init_Lean_Elab_Term_11__resolveLocalNameAux___main(x_9, x_1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_12__resolveLocalName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Term_12__resolveLocalName(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Term_13__mkFreshLevelMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
lean_inc(x_5);
x_11 = l_Lean_Elab_Term_mkFreshLevelMVar(x_1, x_5, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_4);
x_3 = x_10;
x_4 = x_14;
x_6 = x_13;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_13__mkFreshLevelMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
lean_inc(x_2);
x_6 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Term_13__mkFreshLevelMVars___spec__1(x_1, x_2, x_2, x_5, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Term_13__mkFreshLevelMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Term_13__mkFreshLevelMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_Term_13__mkFreshLevelMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_Term_13__mkFreshLevelMVars(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkConst___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkConst___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkConst___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many explicit universe levels");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_mkConst___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkConst___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkConst___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_mkConst___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_mkConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_Term_getEnv___rarg(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_2);
x_9 = lean_environment_find(x_7, x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = l_Lean_Elab_Term_mkConst___closed__2;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Elab_Term_mkConst___closed__4;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Elab_Term_throwError___rarg(x_1, x_14, x_4, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = l_Lean_ConstantInfo_lparams(x_16);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_List_lengthAux___main___rarg(x_17, x_18);
lean_dec(x_17);
x_20 = l_List_lengthAux___main___rarg(x_3, x_18);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_nat_sub(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
x_23 = l___private_Init_Lean_Elab_Term_13__mkFreshLevelMVars(x_1, x_22, x_4, x_8);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_List_append___rarg(x_3, x_25);
x_27 = l_Lean_mkConst(x_2, x_26);
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
x_30 = l_List_append___rarg(x_3, x_28);
x_31 = l_Lean_mkConst(x_2, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
x_33 = l_Lean_Elab_Term_mkConst___closed__7;
x_34 = l_Lean_Elab_Term_throwError___rarg(x_1, x_33, x_4, x_8);
return x_34;
}
}
}
}
lean_object* l_Lean_Elab_Term_mkConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_mkConst(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_14__mkConsts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_5);
lean_inc(x_2);
x_14 = l_Lean_Elab_Term_mkConst(x_1, x_12, x_2, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_ctor_set(x_9, 0, x_15);
lean_ctor_set(x_4, 1, x_3);
x_3 = x_4;
x_4 = x_11;
x_6 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_free_object(x_9);
lean_dec(x_13);
lean_free_object(x_4);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
lean_inc(x_5);
lean_inc(x_2);
x_25 = l_Lean_Elab_Term_mkConst(x_1, x_23, x_2, x_5, x_6);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_28);
x_3 = x_4;
x_4 = x_22;
x_6 = x_27;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
lean_free_object(x_4);
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_32 = x_25;
} else {
 lean_dec_ref(x_25);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_4, 0);
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_4);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_38 = x_34;
} else {
 lean_dec_ref(x_34);
 x_38 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_2);
x_39 = l_Lean_Elab_Term_mkConst(x_1, x_36, x_2, x_5, x_6);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
if (lean_is_scalar(x_38)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_38;
}
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_37);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_3);
x_3 = x_43;
x_4 = x_35;
x_6 = x_41;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_14__mkConsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_Term_getEnv___rarg(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = l_List_foldlM___main___at___private_Init_Lean_Elab_Term_14__mkConsts___spec__1(x_1, x_3, x_8, x_2, x_4, x_7);
return x_9;
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_14__mkConsts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_foldlM___main___at___private_Init_Lean_Elab_Term_14__mkConsts___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_Term_14__mkConsts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Term_14__mkConsts(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
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
lean_object* l_Lean_Elab_Term_resolveName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_7 = l___private_Init_Lean_Elab_Term_12__resolveLocalName(x_2, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_List_isEmpty___rarg(x_3);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = l___private_Init_Lean_Elab_Term_14__mkConsts(x_1, x_3, x_4, x_5, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; 
lean_dec(x_3);
x_13 = l_Lean_Elab_Term_getEnv___rarg(x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_getCurrNamespace(x_5, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_getOpenDecls(x_5, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_2);
x_22 = l_Lean_Elab_resolveGlobalName(x_14, x_17, x_20, x_2);
lean_dec(x_17);
x_23 = l_List_isEmpty___rarg(x_22);
x_24 = l_coeDecidableEq(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_2);
x_25 = l___private_Init_Lean_Elab_Term_14__mkConsts(x_1, x_22, x_4, x_5, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_22);
lean_dec(x_4);
x_26 = l_Lean_Elab_Term_getMainModule___rarg(x_21);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_extractMacroScopes(x_2);
x_30 = l_Lean_MacroScopesView_format(x_29, x_27);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_Elab_Term_resolveName___closed__3;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Elab_Term_mkConst___closed__4;
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Elab_Term_throwError___rarg(x_1, x_35, x_5, x_28);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_41; uint8_t x_42; 
lean_dec(x_3);
lean_dec(x_2);
x_41 = lean_ctor_get(x_8, 0);
lean_inc(x_41);
lean_dec(x_8);
x_42 = !lean_is_exclusive(x_7);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_7, 1);
x_44 = lean_ctor_get(x_7, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
x_46 = l_List_isEmpty___rarg(x_4);
lean_dec(x_4);
x_47 = l_coeDecidableEq(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_free_object(x_7);
lean_dec(x_41);
x_48 = l_Lean_Expr_fvarId_x21(x_45);
lean_dec(x_45);
x_49 = l_Lean_Name_toString___closed__1;
x_50 = l_Lean_Name_toStringWithSep___main(x_49, x_48);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_Elab_Term_resolveName___closed__6;
x_54 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Lean_Elab_Term_resolveName___closed__9;
x_56 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Elab_Term_throwError___rarg(x_1, x_56, x_5, x_43);
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
lean_object* x_62; lean_object* x_63; 
lean_dec(x_45);
lean_dec(x_5);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_41);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_7, 0, x_63);
return x_7;
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_7, 1);
lean_inc(x_64);
lean_dec(x_7);
x_65 = lean_ctor_get(x_41, 0);
lean_inc(x_65);
x_66 = l_List_isEmpty___rarg(x_4);
lean_dec(x_4);
x_67 = l_coeDecidableEq(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_41);
x_68 = l_Lean_Expr_fvarId_x21(x_65);
lean_dec(x_65);
x_69 = l_Lean_Name_toString___closed__1;
x_70 = l_Lean_Name_toStringWithSep___main(x_69, x_68);
x_71 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l_Lean_Elab_Term_resolveName___closed__6;
x_74 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_Elab_Term_resolveName___closed__9;
x_76 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Elab_Term_throwError___rarg(x_1, x_76, x_5, x_64);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
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
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_65);
lean_dec(x_5);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_41);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_64);
return x_84;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_resolveName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_resolveName(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Term_elabBadCDot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabBadCDot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabBadCDot___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabBadCDot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabBadCDot___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabBadCDot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_Term_elabBadCDot___closed__3;
x_6 = l_Lean_Elab_Term_throwError___rarg(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_elabBadCDot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabBadCDot(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabBadCDot");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBadCDot___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_cdot___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
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
x_7 = l_Lean_Elab_Term_throwError___rarg(x_1, x_6, x_3, x_4);
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabRawStrLit");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabRawStrLit___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_strLitKind___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabStr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabStr");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabStr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabStr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabStr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabStr___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabStr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_str___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabStr___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabStr___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
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
x_65 = l_Lean_Elab_Term_throwError___rarg(x_1, x_64, x_3, x_4);
lean_dec(x_1);
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
x_9 = l_Lean_Elab_Term_mkFreshTypeMVar(x_1, x_7, x_8, x_3, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_mvarId_x21(x_10);
x_13 = lean_box(0);
x_50 = l_Lean_Elab_Term_elabRawNumLit___closed__1;
lean_inc(x_1);
x_51 = l_Lean_Elab_Term_registerSyntheticMVar(x_1, x_12, x_50, x_3, x_11);
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
x_55 = l_Lean_Elab_Term_isDefEq(x_1, x_54, x_10, x_3, x_53);
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
lean_dec(x_1);
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
x_15 = l_Lean_Elab_Term_getLevel(x_1, x_10, x_3, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
x_18 = l_Lean_Elab_Term_decLevel(x_1, x_16, x_3, x_17);
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
x_22 = l_Lean_Meta_evalNat___main___closed__3;
lean_inc(x_21);
x_23 = l_Lean_mkConst(x_22, x_21);
lean_inc(x_10);
x_24 = l_Lean_mkApp(x_23, x_10);
x_25 = l_Lean_Elab_Term_mkInstMVar(x_1, x_24, x_3, x_20);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = l_Lean_Meta_evalNat___main___closed__5;
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
x_33 = l_Lean_Meta_evalNat___main___closed__5;
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabRawNumLit");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabRawNumLit), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_numLitKind___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabNum___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabNum");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabNum___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabNum___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabNum___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNum___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabNum(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_num___elambda__1___closed__1;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabNum___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabNum___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_elabRawCharLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Char");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabRawCharLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabRawCharLit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabRawCharLit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabRawCharLit___closed__2;
x_2 = l_Lean_Meta_evalNat___main___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabRawCharLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabRawCharLit___closed__3;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
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
x_7 = l_Lean_Elab_Term_throwError___rarg(x_1, x_6, x_3, x_4);
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
x_12 = l_Lean_Elab_Term_elabRawCharLit___closed__4;
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabRawCharLit");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabRawCharLit___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_charLitKind___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabChar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabChar");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabChar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabChar___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabChar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabChar___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_char___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabChar___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabChar___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
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
x_9 = l_Lean_Elab_Term_throwError___rarg(x_1, x_8, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_nameToExprAux___main(x_10);
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabQuotedName");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabQuotedName___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_quotedName___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_Term_15__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elab_Term_7__postponeElabTerm___closed__2;
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
lean_object* initialize_Init_Lean_Util_Sorry(lean_object*);
lean_object* initialize_Init_Lean_Structure(lean_object*);
lean_object* initialize_Init_Lean_Meta(lean_object*);
lean_object* initialize_Init_Lean_Hygiene(lean_object*);
lean_object* initialize_Init_Lean_Util_RecDepth(lean_object*);
lean_object* initialize_Init_Lean_Elab_Log(lean_object*);
lean_object* initialize_Init_Lean_Elab_Alias(lean_object*);
lean_object* initialize_Init_Lean_Elab_ResolveName(lean_object*);
lean_object* initialize_Init_Lean_Elab_Level(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Term(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Util_Sorry(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Structure(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Hygiene(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_RecDepth(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Log(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Alias(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_ResolveName(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Level(lean_io_mk_world());
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
l_Lean_Elab_Term_withIncRecDepth___rarg___closed__1 = _init_l_Lean_Elab_Term_withIncRecDepth___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_withIncRecDepth___rarg___closed__1);
l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2 = _init_l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2);
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
l_PersistentHashMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__3 = _init_l_PersistentHashMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__3();
lean_mark_persistent(l_PersistentHashMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__3);
l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__1 = _init_l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__1);
l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__2 = _init_l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__2();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__2);
l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1 = _init_l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1);
res = l_Lean_Elab_Term_mkBuiltinTermElabTable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_builtinTermElabTable = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_builtinTermElabTable);
lean_dec_ref(res);
l_Lean_Elab_Term_addBuiltinTermElab___closed__1 = _init_l_Lean_Elab_Term_addBuiltinTermElab___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_addBuiltinTermElab___closed__1);
l_Lean_Elab_Term_declareBuiltinTermElab___closed__1 = _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_declareBuiltinTermElab___closed__1);
l_Lean_Elab_Term_declareBuiltinTermElab___closed__2 = _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_declareBuiltinTermElab___closed__2);
l_Lean_Elab_Term_declareBuiltinTermElab___closed__3 = _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_declareBuiltinTermElab___closed__3);
l_Lean_Elab_Term_declareBuiltinTermElab___closed__4 = _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_declareBuiltinTermElab___closed__4);
l_Lean_Elab_Term_declareBuiltinTermElab___closed__5 = _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_declareBuiltinTermElab___closed__5);
l_Lean_Elab_Term_declareBuiltinTermElab___closed__6 = _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_declareBuiltinTermElab___closed__6);
l_Lean_Elab_Term_declareBuiltinTermElab___closed__7 = _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_declareBuiltinTermElab___closed__7);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__1 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__1);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__2 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__2);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__3 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__3);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__4 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__4);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__5 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__5);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__1 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__1);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__2 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__2);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__3 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__3);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__4 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__4);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__5 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__5);
res = l_Lean_Elab_Term_registerBuiltinTermElabAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_mkTermElabAttribute___closed__1 = _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkTermElabAttribute___closed__1);
l_Lean_Elab_Term_mkTermElabAttribute___closed__2 = _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkTermElabAttribute___closed__2);
l_Lean_Elab_Term_mkTermElabAttribute___closed__3 = _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_mkTermElabAttribute___closed__3);
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
l_Lean_Elab_Term_decLevel___closed__1 = _init_l_Lean_Elab_Term_decLevel___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_decLevel___closed__1);
l_Lean_Elab_Term_decLevel___closed__2 = _init_l_Lean_Elab_Term_decLevel___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_decLevel___closed__2);
l_Lean_Elab_Term_decLevel___closed__3 = _init_l_Lean_Elab_Term_decLevel___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_decLevel___closed__3);
l_Lean_Elab_Term_decLevel___closed__4 = _init_l_Lean_Elab_Term_decLevel___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_decLevel___closed__4);
l_Lean_Elab_Term_decLevel___closed__5 = _init_l_Lean_Elab_Term_decLevel___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_decLevel___closed__5);
l_Lean_Elab_Term_decLevel___closed__6 = _init_l_Lean_Elab_Term_decLevel___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_decLevel___closed__6);
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
l_Lean_Elab_Term_levelMVarToParam___closed__1 = _init_l_Lean_Elab_Term_levelMVarToParam___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_levelMVarToParam___closed__1);
l_Lean_Elab_Term_levelMVarToParam___closed__2 = _init_l_Lean_Elab_Term_levelMVarToParam___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_levelMVarToParam___closed__2);
l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__1 = _init_l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__1);
l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__2 = _init_l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkFreshAnonymousName___rarg___closed__2);
l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__1 = _init_l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__1);
l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__2 = _init_l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkFreshInstanceName___rarg___closed__2);
l___private_Init_Lean_Elab_Term_4__isCDot___closed__1 = _init_l___private_Init_Lean_Elab_Term_4__isCDot___closed__1();
l___private_Init_Lean_Elab_Term_5__expandCDot___closed__1 = _init_l___private_Init_Lean_Elab_Term_5__expandCDot___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_5__expandCDot___closed__1);
l___private_Init_Lean_Elab_Term_5__expandCDot___closed__2 = _init_l___private_Init_Lean_Elab_Term_5__expandCDot___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_5__expandCDot___closed__2);
l___private_Init_Lean_Elab_Term_5__expandCDot___closed__3 = _init_l___private_Init_Lean_Elab_Term_5__expandCDot___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_5__expandCDot___closed__3);
l___private_Init_Lean_Elab_Term_5__expandCDot___closed__4 = _init_l___private_Init_Lean_Elab_Term_5__expandCDot___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_5__expandCDot___closed__4);
l_Lean_Elab_Term_expandCDot_x3f___closed__1 = _init_l_Lean_Elab_Term_expandCDot_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandCDot_x3f___closed__1);
l_Lean_Elab_Term_expandCDot_x3f___closed__2 = _init_l_Lean_Elab_Term_expandCDot_x3f___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandCDot_x3f___closed__2);
l_Lean_Elab_Term_expandCDot_x3f___closed__3 = _init_l_Lean_Elab_Term_expandCDot_x3f___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandCDot_x3f___closed__3);
l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__1 = _init_l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__1);
l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__2 = _init_l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__2);
l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__3 = _init_l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_6__exceptionToSorry___closed__3);
l___private_Init_Lean_Elab_Term_7__postponeElabTerm___closed__1 = _init_l___private_Init_Lean_Elab_Term_7__postponeElabTerm___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_7__postponeElabTerm___closed__1);
l___private_Init_Lean_Elab_Term_7__postponeElabTerm___closed__2 = _init_l___private_Init_Lean_Elab_Term_7__postponeElabTerm___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_7__postponeElabTerm___closed__2);
l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__1 = _init_l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__1);
l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__2 = _init_l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__2);
l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__3 = _init_l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__3);
l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__1 = _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__1);
l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__2 = _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__2);
l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__3 = _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__3);
l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__4 = _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter___closed__4);
l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter = _init_l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_MonadMacroAdapter);
l_Lean_Elab_Term_elabTermAux___main___closed__1 = _init_l_Lean_Elab_Term_elabTermAux___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabTermAux___main___closed__1);
l_Lean_Elab_Term_elabTermAux___main___closed__2 = _init_l_Lean_Elab_Term_elabTermAux___main___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabTermAux___main___closed__2);
l_Lean_Elab_Term_elabTermAux___main___closed__3 = _init_l_Lean_Elab_Term_elabTermAux___main___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabTermAux___main___closed__3);
l_Lean_Elab_Term_elabTermAux___main___closed__4 = _init_l_Lean_Elab_Term_elabTermAux___main___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabTermAux___main___closed__4);
l_Lean_Elab_Term_elabTermAux___main___closed__5 = _init_l_Lean_Elab_Term_elabTermAux___main___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabTermAux___main___closed__5);
l_Lean_Elab_Term_elabTermAux___main___closed__6 = _init_l_Lean_Elab_Term_elabTermAux___main___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabTermAux___main___closed__6);
l_Lean_Elab_Term_ensureType___closed__1 = _init_l_Lean_Elab_Term_ensureType___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_ensureType___closed__1);
l_Lean_Elab_Term_ensureType___closed__2 = _init_l_Lean_Elab_Term_ensureType___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_ensureType___closed__2);
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
l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__1 = _init_l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__1);
l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__2 = _init_l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__2);
l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__3 = _init_l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_throwTypeMismatchError___rarg___closed__3);
l_Lean_Elab_Term_tryCoe___closed__1 = _init_l_Lean_Elab_Term_tryCoe___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_tryCoe___closed__1);
l_Lean_Elab_Term_tryCoe___closed__2 = _init_l_Lean_Elab_Term_tryCoe___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_tryCoe___closed__2);
l_Lean_Elab_Term_tryCoe___closed__3 = _init_l_Lean_Elab_Term_tryCoe___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_tryCoe___closed__3);
l_Lean_Elab_Term_tryCoe___closed__4 = _init_l_Lean_Elab_Term_tryCoe___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_tryCoe___closed__4);
l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabProp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabSort(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabTypeStx___rarg___closed__1 = _init_l_Lean_Elab_Term_elabTypeStx___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabTypeStx___rarg___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabHole(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabNamedHole(lean_io_mk_world());
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
l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabTacticBlock(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__1 = _init_l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__1);
l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__2 = _init_l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__2);
l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__3 = _init_l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__3);
l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__4 = _init_l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__4);
l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__5 = _init_l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__5);
l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__6 = _init_l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__6);
l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__7 = _init_l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__7);
l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__8 = _init_l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__8();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__8);
l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__9 = _init_l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__9();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_9__mkPairsAux___main___closed__9);
l_Lean_Elab_Term_elabParen___closed__1 = _init_l_Lean_Elab_Term_elabParen___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__1);
l_Lean_Elab_Term_elabParen___closed__2 = _init_l_Lean_Elab_Term_elabParen___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__2);
l_Lean_Elab_Term_elabParen___closed__3 = _init_l_Lean_Elab_Term_elabParen___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__3);
l_Lean_Elab_Term_elabParen___closed__4 = _init_l_Lean_Elab_Term_elabParen___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__4);
l_Lean_Elab_Term_elabParen___closed__5 = _init_l_Lean_Elab_Term_elabParen___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__5);
l_Lean_Elab_Term_elabParen___closed__6 = _init_l_Lean_Elab_Term_elabParen___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__6);
l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabParen(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabListLit___closed__1 = _init_l_Lean_Elab_Term_elabListLit___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabListLit___closed__1);
l_Lean_Elab_Term_elabListLit___closed__2 = _init_l_Lean_Elab_Term_elabListLit___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabListLit___closed__2);
l_Lean_Elab_Term_elabListLit___closed__3 = _init_l_Lean_Elab_Term_elabListLit___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabListLit___closed__3);
l_Lean_Elab_Term_elabListLit___closed__4 = _init_l_Lean_Elab_Term_elabListLit___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabListLit___closed__4);
l_Lean_Elab_Term_elabListLit___closed__5 = _init_l_Lean_Elab_Term_elabListLit___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabListLit___closed__5);
l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabListLit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabArrayLit___closed__1 = _init_l_Lean_Elab_Term_elabArrayLit___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabArrayLit___closed__1);
l_Lean_Elab_Term_elabArrayLit___closed__2 = _init_l_Lean_Elab_Term_elabArrayLit___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabArrayLit___closed__2);
l_Lean_Elab_Term_elabArrayLit___closed__3 = _init_l_Lean_Elab_Term_elabArrayLit___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabArrayLit___closed__3);
l_Lean_Elab_Term_elabArrayLit___closed__4 = _init_l_Lean_Elab_Term_elabArrayLit___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabArrayLit___closed__4);
l_Lean_Elab_Term_elabArrayLit___closed__5 = _init_l_Lean_Elab_Term_elabArrayLit___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabArrayLit___closed__5);
l_Lean_Elab_Term_elabArrayLit___closed__6 = _init_l_Lean_Elab_Term_elabArrayLit___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabArrayLit___closed__6);
l_Lean_Elab_Term_elabArrayLit___closed__7 = _init_l_Lean_Elab_Term_elabArrayLit___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_elabArrayLit___closed__7);
l_Lean_Elab_Term_elabArrayLit___closed__8 = _init_l_Lean_Elab_Term_elabArrayLit___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_elabArrayLit___closed__8);
l_Lean_Elab_Term_elabArrayLit___closed__9 = _init_l_Lean_Elab_Term_elabArrayLit___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_elabArrayLit___closed__9);
l_Lean_Elab_Term_elabArrayLit___closed__10 = _init_l_Lean_Elab_Term_elabArrayLit___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_elabArrayLit___closed__10);
l_Lean_Elab_Term_elabArrayLit___closed__11 = _init_l_Lean_Elab_Term_elabArrayLit___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_elabArrayLit___closed__11);
l_Lean_Elab_Term_elabArrayLit___closed__12 = _init_l_Lean_Elab_Term_elabArrayLit___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_elabArrayLit___closed__12);
l_Lean_Elab_Term_elabArrayLit___closed__13 = _init_l_Lean_Elab_Term_elabArrayLit___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_elabArrayLit___closed__13);
l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabArrayLit(lean_io_mk_world());
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
l_Lean_Elab_Term_mkConst___closed__6 = _init_l_Lean_Elab_Term_mkConst___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_mkConst___closed__6);
l_Lean_Elab_Term_mkConst___closed__7 = _init_l_Lean_Elab_Term_mkConst___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_mkConst___closed__7);
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
l_Lean_Elab_Term_elabBadCDot___closed__1 = _init_l_Lean_Elab_Term_elabBadCDot___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabBadCDot___closed__1);
l_Lean_Elab_Term_elabBadCDot___closed__2 = _init_l_Lean_Elab_Term_elabBadCDot___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabBadCDot___closed__2);
l_Lean_Elab_Term_elabBadCDot___closed__3 = _init_l_Lean_Elab_Term_elabBadCDot___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabBadCDot___closed__3);
l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabBadCDot(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabRawStrLit___closed__1 = _init_l_Lean_Elab_Term_elabRawStrLit___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabRawStrLit___closed__1);
l_Lean_Elab_Term_elabRawStrLit___closed__2 = _init_l_Lean_Elab_Term_elabRawStrLit___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabRawStrLit___closed__2);
l_Lean_Elab_Term_elabRawStrLit___closed__3 = _init_l_Lean_Elab_Term_elabRawStrLit___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabRawStrLit___closed__3);
l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabRawStrLit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabStr___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabStr___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabStr___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabStr___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabStr___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabStr___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabStr___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabStr___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabStr___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabStr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabRawNumLit___closed__1 = _init_l_Lean_Elab_Term_elabRawNumLit___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabRawNumLit___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabRawNumLit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabNum___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabNum___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabNum___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabNum___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabNum___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabNum___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabNum___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabNum___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabNum___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabNum(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabRawCharLit___closed__1 = _init_l_Lean_Elab_Term_elabRawCharLit___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabRawCharLit___closed__1);
l_Lean_Elab_Term_elabRawCharLit___closed__2 = _init_l_Lean_Elab_Term_elabRawCharLit___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabRawCharLit___closed__2);
l_Lean_Elab_Term_elabRawCharLit___closed__3 = _init_l_Lean_Elab_Term_elabRawCharLit___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabRawCharLit___closed__3);
l_Lean_Elab_Term_elabRawCharLit___closed__4 = _init_l_Lean_Elab_Term_elabRawCharLit___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabRawCharLit___closed__4);
l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabRawCharLit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabChar___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabChar___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabChar___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabChar___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabChar___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabChar___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabChar___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabChar___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabChar___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabChar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabQuotedName(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Init_Lean_Elab_Term_15__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
