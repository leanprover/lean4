// Lean compiler output
// Module: Lean.Elab.Tactic.Basic
// Imports: Init Lean.Util.CollectMVars Lean.Meta.Tactic.Assumption Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Clear Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Subst Lean.Elab.Util Lean.Elab.Term
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
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalTraceState___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withIncRecDepth___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_getConstInfo___closed__5;
lean_object* l_Lean_Elab_Tactic_monadLog;
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_EStateM_MonadStateOf___closed__2;
lean_object* l_Lean_Elab_Tactic_getLocalInsts___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__7;
lean_object* l_Lean_Elab_Tactic_evalTactic___main___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainMVarContext___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__3;
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_clear___elambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadQuotation;
lean_object* l_Lean_Elab_Tactic_withMainMVarContext(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_goalsToMessageData___spec__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSkip___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMCtx___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_monadQuotation___closed__4;
lean_object* l_Lean_Meta_introN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__1;
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_assignExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalChoiceAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getEnv(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSkip(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focus___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalClear(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_lift___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_subst___elambda__1___closed__1;
lean_object* l_Lean_Elab_Tactic_trace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_appendGoals___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focus(lean_object*);
lean_object* l_Lean_Elab_Tactic_getLCtx___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadQuotation___closed__2;
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__6;
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_resolveGlobalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCase___closed__1;
lean_object* l_Lean_Elab_Tactic_done(lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen(lean_object*);
lean_object* l_Lean_Elab_Tactic_monadQuotation___closed__1;
lean_object* l_Lean_Elab_Tactic_forEachVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_restore(lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__1___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_clear___lambda__1___closed__6;
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_goalsToMessageData___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__1;
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCase___closed__3;
lean_object* l_Lean_Meta_assumption___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__11;
lean_object* l_Lean_Elab_Tactic_getMCtx___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_getGoals___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_withRef___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Elab_Term_logTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_withFreshMacroScope(lean_object*);
lean_object* l_Lean_MetavarContext_renameMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__3;
lean_object* l_Lean_Elab_Tactic_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__4;
extern lean_object* l_Lean_Parser_Tactic_failIfSuccess___elambda__1___closed__2;
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getLocalInsts(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTraceState___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__1;
lean_object* l_Lean_Elab_Tactic_monadLog___closed__10;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__1;
lean_object* l_Lean_Elab_Tactic_withRef___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_restore___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain(lean_object*);
lean_object* l_Lean_Elab_Term_trace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Tactic_evalTraceState___spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__2;
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_clear___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_collectMVars___closed__1;
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_whnfCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__3;
lean_object* l_Lean_Elab_Tactic_getMainGoal___closed__2;
lean_object* l_Lean_Elab_Term_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__3;
extern lean_object* l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalClear(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__1;
lean_object* l_Std_PersistentHashMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__3;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l_Lean_Meta_intro(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalNestedTacticBlock___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAssumption(lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
lean_object* l_List_findM_x3f___main___at_Lean_Elab_Tactic_evalCase___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_dbgTrace___rarg___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSeq(lean_object*);
lean_object* l_List_findM_x3f___main___at_Lean_Elab_Tactic_evalCase___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Basic_4__regTraceClasses(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__1;
lean_object* l_Lean_Elab_Tactic_evalCase(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__1;
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlockCurly(lean_object*);
lean_object* l_Lean_Elab_Term_throwErrorAt___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
extern lean_object* l_Lean_Core_checkRecDepth___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTraceState(lean_object*);
extern lean_object* l_Lean_Meta_Exception_toMessageData___closed__48;
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalChoice(lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focus___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind___closed__2;
lean_object* l_Lean_Elab_Tactic_monadLog___closed__5;
lean_object* l_Lean_Elab_Term_isExprMVarAssigned___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__1___closed__2;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
lean_object* l_Lean_Elab_Tactic_dbgTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSeq___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess(lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_addContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalClear___closed__1;
lean_object* l_Lean_Elab_Tactic_evalSeq___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_EStateM_Backtrackable;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSkip(lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftTermElabM(lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__5;
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getGoals___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__2;
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock___closed__1;
extern lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__1;
lean_object* l_ReaderT_lift___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1(lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___closed__1;
extern lean_object* l_Lean_Elab_Term_State_inhabited___closed__2;
extern lean_object* l_Lean_Elab_Term_elabUsingElabFns___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__1;
lean_object* l_Lean_Elab_Tactic_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_resetSynthInstanceCache(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__1;
lean_object* l_Lean_Elab_Tactic_monadLog___closed__7;
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__12;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Syntax_prettyPrint(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__4;
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalChoice___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___rarg(lean_object*, lean_object*, lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Lean_Elab_Tactic_State_inhabited___closed__1;
lean_object* l_Lean_collectMVars(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalParen___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSubst(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__8;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2;
extern lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__4;
lean_object* l_Lean_Elab_Tactic_getMainModule___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_3__getIntrosSize___main___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalChoice(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withLCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntros(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTraceState(lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__8;
lean_object* l_ReaderT_read___at_Lean_Elab_Tactic_monadLog___spec__1(lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__1;
lean_object* l_Lean_Meta_subst___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__9;
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__2;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withRef(lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__1;
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_save___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Basic_3__getIntrosSize___boxed(lean_object*);
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalOrelse___closed__1;
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__4;
lean_object* l_Lean_Elab_Tactic_whnf(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l_Lean_Elab_Tactic_liftMetaM(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalNestedTacticBlock(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_MessageData_joinSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_State_inhabited;
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_3__getIntrosSize___main(lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Elab_Tactic_tacticElabAttribute___spec__2(lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_evalOrelse(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_evalAssumption___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_forEachVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashSet_Inhabited___closed__1;
lean_object* l_Lean_Elab_Tactic_evalRevert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_throwErrorAt(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_appendGoals(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__1;
lean_object* l_Lean_Elab_Tactic_throwUnsupportedSyntax(lean_object*);
lean_object* l_Lean_Elab_Tactic_withLCtx(lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTraceState___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_goalsToMessageData(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_isAnonymousMVar(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__5;
lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess___closed__1;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Exception_inhabited;
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__3;
lean_object* l_Lean_Elab_Tactic_liftTermElabM___rarg___closed__1;
lean_object* l_Lean_Elab_Tactic_isExprMVarAssigned(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_modifyMCtx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalParen(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__10;
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Elab_Tactic_liftMetaTactic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock(lean_object*);
lean_object* l_Lean_Elab_Term_traceAtCmdPos(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__1;
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2;
lean_object* l_Lean_Elab_Tactic_evalNestedTacticBlockCurly(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focusAux(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__6;
lean_object* l_Lean_Elab_Tactic_evalSeq(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1;
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCache(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalAssumption(lean_object*);
lean_object* l_Lean_Elab_Tactic_save(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCase___closed__2;
lean_object* l_Lean_Elab_Tactic_monadLog___closed__2;
lean_object* l_Lean_Elab_Tactic_evalChoiceAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_modifyMCtx(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_whnfCore(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
lean_object* l_Lean_Elab_Tactic_getOptions___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveGlobalName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMVarContext___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isSuffixOf___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_logTrace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalChoiceAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_throwError(lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__1;
lean_object* l_Lean_Elab_Tactic_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRevert(lean_object*);
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalIntros___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getOptions(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__5;
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux(lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__6;
lean_object* l_Lean_Elab_Tactic_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focusAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_3__getIntrosSize(lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTraceState___spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getEnv___rarg(lean_object*);
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__2;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__1;
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTraceState___boxed(lean_object*);
lean_object* l_Lean_Syntax_getTailWithPos___main(lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntro(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalRevert___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSubst___closed__1;
lean_object* l_Lean_Elab_Tactic_evalIntros(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___closed__3;
lean_object* l_Lean_Elab_Tactic_getMainGoal___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Tactic_evalTraceState___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__1;
lean_object* l_Lean_Elab_Tactic_monadLog___closed__11;
lean_object* l_ReaderT_lift___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalTraceState___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSubst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_collectMVars(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalInstance_beq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalChoiceAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMVarContext(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMacroExpansion(lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter;
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalOrelse(lean_object*);
lean_object* l_Lean_Elab_Tactic_dbgTrace(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_4__regTraceClasses___closed__1;
lean_object* l_Lean_Elab_Tactic_focus___rarg___closed__1;
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__3;
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_Lean_Elab_mkMacroAttribute___closed__2;
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_getFVarIds___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainModule(lean_object*);
lean_object* l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_revert___elambda__1___closed__2;
lean_object* l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainModule___boxed(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_monadQuotation___closed__3;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCase(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__2;
lean_object* l_Lean_Elab_Tactic_getGoals(lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__2;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
lean_object* l_Lean_Elab_Tactic_traceAtCmdPos(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalNestedTacticBlockCurly___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getLCtx(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandTacticMacro(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getEnv___boxed(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Tactic_evalTraceState___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalParen(lean_object*);
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Tactic_evalTraceState___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftMetaM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__4;
lean_object* l_Lean_Elab_Tactic_getMCtx(lean_object*);
lean_object* l_Lean_Elab_Tactic_throwError___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__9;
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSkip___rarg(lean_object*);
lean_object* l_Lean_Elab_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withIncRecDepth(lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_goalsToMessageData___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___main___at_Lean_Elab_goalsToMessageData___spec__1(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___main___at_Lean_Elab_goalsToMessageData___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* _init_l_Lean_Elab_goalsToMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_ofList___closed__3;
x_2 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_goalsToMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_List_map___main___at_Lean_Elab_goalsToMessageData___spec__1(x_1);
x_3 = l_Lean_Elab_goalsToMessageData___closed__1;
x_4 = l_Lean_MessageData_joinSep___main(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unsolved goals");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__3;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 9);
lean_inc(x_4);
lean_inc(x_4);
x_5 = l_Lean_Syntax_getTailWithPos___main(x_4);
x_6 = l_Lean_Elab_goalsToMessageData(x_1);
x_7 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__4;
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_throwErrorAt___rarg(x_4, x_8, x_2, x_3);
lean_dec(x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Lean_Elab_Term_throwErrorAt___rarg(x_10, x_8, x_2, x_3);
lean_dec(x_10);
return x_11;
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_State_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_State_inhabited___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_State_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_State_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_save(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Tactic_save___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_save(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_restore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_3, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_4, 0);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_ctor_set(x_4, 1, x_7);
lean_ctor_set(x_4, 0, x_6);
lean_inc(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_ctor_get(x_4, 3);
x_16 = lean_ctor_get(x_4, 4);
x_17 = lean_ctor_get(x_4, 5);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
lean_inc(x_7);
lean_inc(x_6);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_7);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_16);
lean_ctor_set(x_18, 5, x_17);
lean_ctor_set(x_3, 0, x_18);
lean_inc(x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get(x_3, 3);
x_26 = lean_ctor_get(x_3, 4);
x_27 = lean_ctor_get(x_3, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_28 = lean_ctor_get(x_4, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_4, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_4, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_4, 5);
lean_inc(x_31);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_32 = x_4;
} else {
 lean_dec_ref(x_4);
 x_32 = lean_box(0);
}
lean_inc(x_21);
lean_inc(x_20);
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 6, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_29);
lean_ctor_set(x_33, 4, x_30);
lean_ctor_set(x_33, 5, x_31);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_34, 2, x_24);
lean_ctor_set(x_34, 3, x_25);
lean_ctor_set(x_34, 4, x_26);
lean_ctor_set(x_34, 5, x_27);
lean_inc(x_22);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_22);
return x_35;
}
}
}
lean_object* l_Lean_Elab_Tactic_restore___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_restore(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_save___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_restore___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__1;
x_2 = l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_EStateM_Backtrackable() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__3;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_liftTermElabM___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Exception_inhabited;
x_2 = l_Lean_Elab_Tactic_State_inhabited;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_liftTermElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_apply_2(x_1, x_4, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 1);
lean_ctor_set(x_3, 0, x_10);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_8);
lean_ctor_set(x_3, 0, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_16);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
lean_free_object(x_3);
lean_dec(x_7);
x_22 = l_Lean_Elab_Tactic_liftTermElabM___rarg___closed__1;
x_23 = l_unreachable_x21___rarg(x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_26 = lean_apply_2(x_1, x_4, x_24);
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
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_25);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
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
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_25);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_26);
lean_dec(x_25);
x_38 = l_Lean_Elab_Tactic_liftTermElabM___rarg___closed__1;
x_39 = l_unreachable_x21___rarg(x_38);
return x_39;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_liftTermElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftTermElabM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_liftMetaM___rarg), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_withRef___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = lean_ctor_get(x_6, 9);
x_9 = l_Lean_Elab_replaceRef(x_1, x_8);
lean_dec(x_8);
lean_ctor_set(x_6, 9, x_9);
x_10 = lean_apply_2(x_2, x_3, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
x_13 = lean_ctor_get(x_6, 2);
x_14 = lean_ctor_get(x_6, 3);
x_15 = lean_ctor_get(x_6, 4);
x_16 = lean_ctor_get(x_6, 5);
x_17 = lean_ctor_get(x_6, 6);
x_18 = lean_ctor_get(x_6, 7);
x_19 = lean_ctor_get(x_6, 8);
x_20 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_21 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
x_22 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 2);
x_23 = lean_ctor_get(x_6, 9);
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
lean_dec(x_6);
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
lean_ctor_set(x_3, 0, x_25);
x_26 = lean_apply_2(x_2, x_3, x_4);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_3);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_27, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_27, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 5);
lean_inc(x_34);
x_35 = lean_ctor_get(x_27, 6);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 7);
lean_inc(x_36);
x_37 = lean_ctor_get(x_27, 8);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_27, sizeof(void*)*10);
x_39 = lean_ctor_get_uint8(x_27, sizeof(void*)*10 + 1);
x_40 = lean_ctor_get_uint8(x_27, sizeof(void*)*10 + 2);
x_41 = lean_ctor_get(x_27, 9);
lean_inc(x_41);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 lean_ctor_release(x_27, 3);
 lean_ctor_release(x_27, 4);
 lean_ctor_release(x_27, 5);
 lean_ctor_release(x_27, 6);
 lean_ctor_release(x_27, 7);
 lean_ctor_release(x_27, 8);
 lean_ctor_release(x_27, 9);
 x_42 = x_27;
} else {
 lean_dec_ref(x_27);
 x_42 = lean_box(0);
}
x_43 = l_Lean_Elab_replaceRef(x_1, x_41);
lean_dec(x_41);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 10, 3);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_29);
lean_ctor_set(x_44, 1, x_30);
lean_ctor_set(x_44, 2, x_31);
lean_ctor_set(x_44, 3, x_32);
lean_ctor_set(x_44, 4, x_33);
lean_ctor_set(x_44, 5, x_34);
lean_ctor_set(x_44, 6, x_35);
lean_ctor_set(x_44, 7, x_36);
lean_ctor_set(x_44, 8, x_37);
lean_ctor_set(x_44, 9, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*10, x_38);
lean_ctor_set_uint8(x_44, sizeof(void*)*10 + 1, x_39);
lean_ctor_set_uint8(x_44, sizeof(void*)*10 + 2, x_40);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_28);
x_46 = lean_apply_2(x_2, x_45, x_4);
return x_46;
}
}
}
lean_object* l_Lean_Elab_Tactic_withRef(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withRef___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_withRef___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_withRef___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_getEnv___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_getEnv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getEnv___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getEnv___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_getEnv(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getMCtx___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_getMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getMCtx___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getMCtx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_getMCtx(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_modifyMCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_3, 0);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_apply_1(x_1, x_11);
lean_ctor_set(x_5, 1, x_12);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 3);
x_19 = lean_ctor_get(x_5, 4);
x_20 = lean_ctor_get(x_5, 5);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_21 = lean_apply_1(x_1, x_16);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_18);
lean_ctor_set(x_22, 4, x_19);
lean_ctor_set(x_22, 5, x_20);
lean_ctor_set(x_4, 0, x_22);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_25 = lean_ctor_get(x_4, 1);
x_26 = lean_ctor_get(x_4, 2);
x_27 = lean_ctor_get(x_4, 3);
x_28 = lean_ctor_get(x_4, 4);
x_29 = lean_ctor_get(x_4, 5);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_4);
x_30 = lean_ctor_get(x_5, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_5, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_5, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_5, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 5);
lean_inc(x_35);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 x_36 = x_5;
} else {
 lean_dec_ref(x_5);
 x_36 = lean_box(0);
}
x_37 = lean_apply_1(x_1, x_31);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 6, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_32);
lean_ctor_set(x_38, 3, x_33);
lean_ctor_set(x_38, 4, x_34);
lean_ctor_set(x_38, 5, x_35);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_25);
lean_ctor_set(x_39, 2, x_26);
lean_ctor_set(x_39, 3, x_27);
lean_ctor_set(x_39, 4, x_28);
lean_ctor_set(x_39, 5, x_29);
lean_ctor_set(x_3, 0, x_39);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_3);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_42 = lean_ctor_get(x_3, 1);
lean_inc(x_42);
lean_dec(x_3);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_4, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_4, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_4, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_4, 5);
lean_inc(x_47);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_48 = x_4;
} else {
 lean_dec_ref(x_4);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_5, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_5, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_5, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_5, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_5, 4);
lean_inc(x_53);
x_54 = lean_ctor_get(x_5, 5);
lean_inc(x_54);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 x_55 = x_5;
} else {
 lean_dec_ref(x_5);
 x_55 = lean_box(0);
}
x_56 = lean_apply_1(x_1, x_50);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 6, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_51);
lean_ctor_set(x_57, 3, x_52);
lean_ctor_set(x_57, 4, x_53);
lean_ctor_set(x_57, 5, x_54);
if (lean_is_scalar(x_48)) {
 x_58 = lean_alloc_ctor(0, 6, 0);
} else {
 x_58 = x_48;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_43);
lean_ctor_set(x_58, 2, x_44);
lean_ctor_set(x_58, 3, x_45);
lean_ctor_set(x_58, 4, x_46);
lean_ctor_set(x_58, 5, x_47);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_42);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
lean_object* l_Lean_Elab_Tactic_modifyMCtx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_modifyMCtx(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_getLCtx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_getLCtx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_getLCtx(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_getLocalInsts(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_getLocalInsts___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_getLocalInsts(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_getOptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
lean_object* l_Lean_Elab_Tactic_getOptions___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_getOptions(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_getMVarDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Tactic_getMCtx___rarg(x_3);
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
lean_object* l_Lean_Elab_Tactic_getMVarDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_getMVarDecl(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_instantiateMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_instantiateMVars), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_addContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_addContext___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_isExprMVarAssigned(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_isExprMVarAssigned___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_assignExprMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_assignExprMVar___boxed), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_ensureHasType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ensureHasType), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_reportUnsolvedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportUnsolvedGoals), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_inferType), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_whnf(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_whnf), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_whnfCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_whnfCore), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_unfoldDefinition_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_unfoldDefinition_x3f), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_resolveGlobalName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_resolveGlobalName___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Tactic_collectMVars___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_HashSet_Inhabited___closed__1;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_collectMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_instantiateMVars(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_Elab_Tactic_collectMVars___closed__1;
x_8 = l_Lean_collectMVars(x_7, x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Array_toList___rarg(x_9);
lean_dec(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = l_Lean_Elab_Tactic_collectMVars___closed__1;
x_14 = l_Lean_collectMVars(x_13, x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Array_toList___rarg(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
return x_4;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_4);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_ReaderT_read___at_Lean_Elab_Tactic_monadLog___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 9);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = lean_ctor_get(x_5, 2);
x_8 = l_Std_PersistentArray_push___rarg(x_7, x_1);
lean_ctor_set(x_5, 2, x_8);
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
x_17 = l_Std_PersistentArray_push___rarg(x_13, x_1);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_17);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_21, 4);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 5);
lean_inc(x_28);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 lean_ctor_release(x_21, 5);
 x_29 = x_21;
} else {
 lean_dec_ref(x_21);
 x_29 = lean_box(0);
}
x_30 = l_Std_PersistentArray_push___rarg(x_25, x_1);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 6, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_26);
lean_ctor_set(x_31, 4, x_27);
lean_ctor_set(x_31, 5, x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_22);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Elab_Tactic_monadLog___spec__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_monadLog___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_monadLog___closed__1;
x_2 = l_Lean_Elab_Tactic_monadLog___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_monadLog___lambda__2___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_monadLog___closed__1;
x_2 = l_Lean_Elab_Tactic_monadLog___closed__4;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_monadLog___lambda__3___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_monadLog___closed__1;
x_2 = l_Lean_Elab_Tactic_monadLog___closed__6;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_addContext), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_monadLog___closed__3;
x_2 = l_Lean_Elab_Tactic_monadLog___closed__5;
x_3 = l_Lean_Elab_Tactic_monadLog___closed__7;
x_4 = l_Lean_Elab_Tactic_monadLog___closed__8;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_monadLog___lambda__4___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_monadLog___closed__9;
x_2 = l_Lean_Elab_Tactic_monadLog___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_monadLog___closed__11;
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_monadLog___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_monadLog___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_monadLog___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_monadLog___lambda__4(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_throwErrorAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwErrorAt___rarg___boxed), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_throwErrorAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_throwErrorAt___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_throwError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwError___rarg), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_throwError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_throwError___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwUnsupportedSyntax___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg___closed__1;
x_4 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_throwUnsupportedSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_withIncRecDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_2, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_ctor_get(x_76, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 4);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_nat_dec_eq(x_77, x_78);
lean_dec(x_78);
lean_dec(x_77);
if (x_79 == 0)
{
x_4 = x_3;
goto block_74;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_Lean_Core_checkRecDepth___closed__2;
lean_inc(x_2);
x_81 = l_Lean_Elab_Tactic_throwError___rarg(x_80, x_2, x_3);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_4 = x_82;
goto block_74;
}
else
{
uint8_t x_83; 
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
return x_81;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_81, 0);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_81);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
block_74:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_6, 3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_12, x_13);
lean_dec(x_12);
lean_ctor_set(x_6, 3, x_14);
x_15 = lean_apply_2(x_1, x_2, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 2);
x_19 = lean_ctor_get(x_6, 3);
x_20 = lean_ctor_get(x_6, 4);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_19, x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set(x_5, 0, x_23);
x_24 = lean_apply_2(x_1, x_2, x_4);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_25 = lean_ctor_get(x_5, 1);
x_26 = lean_ctor_get(x_5, 2);
x_27 = lean_ctor_get(x_5, 3);
x_28 = lean_ctor_get(x_5, 4);
x_29 = lean_ctor_get(x_5, 5);
x_30 = lean_ctor_get(x_5, 6);
x_31 = lean_ctor_get(x_5, 7);
x_32 = lean_ctor_get(x_5, 8);
x_33 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_34 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_35 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_36 = lean_ctor_get(x_5, 9);
lean_inc(x_36);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_37 = lean_ctor_get(x_6, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_6, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_6, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_6, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_6, 4);
lean_inc(x_41);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_42 = x_6;
} else {
 lean_dec_ref(x_6);
 x_42 = lean_box(0);
}
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_40, x_43);
lean_dec(x_40);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 5, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_38);
lean_ctor_set(x_45, 2, x_39);
lean_ctor_set(x_45, 3, x_44);
lean_ctor_set(x_45, 4, x_41);
x_46 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_25);
lean_ctor_set(x_46, 2, x_26);
lean_ctor_set(x_46, 3, x_27);
lean_ctor_set(x_46, 4, x_28);
lean_ctor_set(x_46, 5, x_29);
lean_ctor_set(x_46, 6, x_30);
lean_ctor_set(x_46, 7, x_31);
lean_ctor_set(x_46, 8, x_32);
lean_ctor_set(x_46, 9, x_36);
lean_ctor_set_uint8(x_46, sizeof(void*)*10, x_33);
lean_ctor_set_uint8(x_46, sizeof(void*)*10 + 1, x_34);
lean_ctor_set_uint8(x_46, sizeof(void*)*10 + 2, x_35);
lean_ctor_set(x_2, 0, x_46);
x_47 = lean_apply_2(x_1, x_2, x_4);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
lean_dec(x_2);
x_49 = lean_ctor_get(x_5, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_5, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_5, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_5, 4);
lean_inc(x_52);
x_53 = lean_ctor_get(x_5, 5);
lean_inc(x_53);
x_54 = lean_ctor_get(x_5, 6);
lean_inc(x_54);
x_55 = lean_ctor_get(x_5, 7);
lean_inc(x_55);
x_56 = lean_ctor_get(x_5, 8);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_58 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_59 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_60 = lean_ctor_get(x_5, 9);
lean_inc(x_60);
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
 x_61 = x_5;
} else {
 lean_dec_ref(x_5);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_6, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_6, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_6, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_6, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_6, 4);
lean_inc(x_66);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_67 = x_6;
} else {
 lean_dec_ref(x_6);
 x_67 = lean_box(0);
}
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_add(x_65, x_68);
lean_dec(x_65);
if (lean_is_scalar(x_67)) {
 x_70 = lean_alloc_ctor(0, 5, 0);
} else {
 x_70 = x_67;
}
lean_ctor_set(x_70, 0, x_62);
lean_ctor_set(x_70, 1, x_63);
lean_ctor_set(x_70, 2, x_64);
lean_ctor_set(x_70, 3, x_69);
lean_ctor_set(x_70, 4, x_66);
if (lean_is_scalar(x_61)) {
 x_71 = lean_alloc_ctor(0, 10, 3);
} else {
 x_71 = x_61;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_49);
lean_ctor_set(x_71, 2, x_50);
lean_ctor_set(x_71, 3, x_51);
lean_ctor_set(x_71, 4, x_52);
lean_ctor_set(x_71, 5, x_53);
lean_ctor_set(x_71, 6, x_54);
lean_ctor_set(x_71, 7, x_55);
lean_ctor_set(x_71, 8, x_56);
lean_ctor_set(x_71, 9, x_60);
lean_ctor_set_uint8(x_71, sizeof(void*)*10, x_57);
lean_ctor_set_uint8(x_71, sizeof(void*)*10 + 1, x_58);
lean_ctor_set_uint8(x_71, sizeof(void*)*10 + 2, x_59);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_48);
x_73 = lean_apply_2(x_1, x_72, x_4);
return x_73;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_withIncRecDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withIncRecDepth___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 8);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_getCurrMacroScope(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_getMainModule___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Elab_Tactic_getEnv___rarg(x_1);
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
lean_object* l_Lean_Elab_Tactic_getMainModule(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getMainModule___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getMainModule___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_getMainModule(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_withFreshMacroScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_ctor_set(x_5, 5, x_9);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 8);
lean_dec(x_13);
lean_ctor_set(x_11, 8, x_7);
x_14 = lean_apply_2(x_1, x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
x_20 = lean_ctor_get(x_11, 5);
x_21 = lean_ctor_get(x_11, 6);
x_22 = lean_ctor_get(x_11, 7);
x_23 = lean_ctor_get_uint8(x_11, sizeof(void*)*10);
x_24 = lean_ctor_get_uint8(x_11, sizeof(void*)*10 + 1);
x_25 = lean_ctor_get_uint8(x_11, sizeof(void*)*10 + 2);
x_26 = lean_ctor_get(x_11, 9);
lean_inc(x_26);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_27 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_16);
lean_ctor_set(x_27, 2, x_17);
lean_ctor_set(x_27, 3, x_18);
lean_ctor_set(x_27, 4, x_19);
lean_ctor_set(x_27, 5, x_20);
lean_ctor_set(x_27, 6, x_21);
lean_ctor_set(x_27, 7, x_22);
lean_ctor_set(x_27, 8, x_7);
lean_ctor_set(x_27, 9, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*10, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*10 + 1, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*10 + 2, x_25);
lean_ctor_set(x_2, 0, x_27);
x_28 = lean_apply_2(x_1, x_2, x_3);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_2);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_29, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 5);
lean_inc(x_36);
x_37 = lean_ctor_get(x_29, 6);
lean_inc(x_37);
x_38 = lean_ctor_get(x_29, 7);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_29, sizeof(void*)*10);
x_40 = lean_ctor_get_uint8(x_29, sizeof(void*)*10 + 1);
x_41 = lean_ctor_get_uint8(x_29, sizeof(void*)*10 + 2);
x_42 = lean_ctor_get(x_29, 9);
lean_inc(x_42);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 lean_ctor_release(x_29, 3);
 lean_ctor_release(x_29, 4);
 lean_ctor_release(x_29, 5);
 lean_ctor_release(x_29, 6);
 lean_ctor_release(x_29, 7);
 lean_ctor_release(x_29, 8);
 lean_ctor_release(x_29, 9);
 x_43 = x_29;
} else {
 lean_dec_ref(x_29);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 10, 3);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_31);
lean_ctor_set(x_44, 1, x_32);
lean_ctor_set(x_44, 2, x_33);
lean_ctor_set(x_44, 3, x_34);
lean_ctor_set(x_44, 4, x_35);
lean_ctor_set(x_44, 5, x_36);
lean_ctor_set(x_44, 6, x_37);
lean_ctor_set(x_44, 7, x_38);
lean_ctor_set(x_44, 8, x_7);
lean_ctor_set(x_44, 9, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*10, x_39);
lean_ctor_set_uint8(x_44, sizeof(void*)*10 + 1, x_40);
lean_ctor_set_uint8(x_44, sizeof(void*)*10 + 2, x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_30);
x_46 = lean_apply_2(x_1, x_45, x_3);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_47 = lean_ctor_get(x_5, 0);
x_48 = lean_ctor_get(x_5, 1);
x_49 = lean_ctor_get(x_5, 2);
x_50 = lean_ctor_get(x_5, 3);
x_51 = lean_ctor_get(x_5, 4);
x_52 = lean_ctor_get(x_5, 5);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_5);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_52, x_53);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_48);
lean_ctor_set(x_55, 2, x_49);
lean_ctor_set(x_55, 3, x_50);
lean_ctor_set(x_55, 4, x_51);
lean_ctor_set(x_55, 5, x_54);
lean_ctor_set(x_3, 0, x_55);
x_56 = lean_ctor_get(x_2, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_58 = x_2;
} else {
 lean_dec_ref(x_2);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_56, 5);
lean_inc(x_64);
x_65 = lean_ctor_get(x_56, 6);
lean_inc(x_65);
x_66 = lean_ctor_get(x_56, 7);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_56, sizeof(void*)*10);
x_68 = lean_ctor_get_uint8(x_56, sizeof(void*)*10 + 1);
x_69 = lean_ctor_get_uint8(x_56, sizeof(void*)*10 + 2);
x_70 = lean_ctor_get(x_56, 9);
lean_inc(x_70);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 lean_ctor_release(x_56, 4);
 lean_ctor_release(x_56, 5);
 lean_ctor_release(x_56, 6);
 lean_ctor_release(x_56, 7);
 lean_ctor_release(x_56, 8);
 lean_ctor_release(x_56, 9);
 x_71 = x_56;
} else {
 lean_dec_ref(x_56);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 10, 3);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_59);
lean_ctor_set(x_72, 1, x_60);
lean_ctor_set(x_72, 2, x_61);
lean_ctor_set(x_72, 3, x_62);
lean_ctor_set(x_72, 4, x_63);
lean_ctor_set(x_72, 5, x_64);
lean_ctor_set(x_72, 6, x_65);
lean_ctor_set(x_72, 7, x_66);
lean_ctor_set(x_72, 8, x_52);
lean_ctor_set(x_72, 9, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*10, x_67);
lean_ctor_set_uint8(x_72, sizeof(void*)*10 + 1, x_68);
lean_ctor_set_uint8(x_72, sizeof(void*)*10 + 2, x_69);
if (lean_is_scalar(x_58)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_58;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_57);
x_74 = lean_apply_2(x_1, x_73, x_3);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_75 = lean_ctor_get(x_3, 0);
x_76 = lean_ctor_get(x_3, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_3);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_75, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 4);
lean_inc(x_81);
x_82 = lean_ctor_get(x_75, 5);
lean_inc(x_82);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 lean_ctor_release(x_75, 5);
 x_83 = x_75;
} else {
 lean_dec_ref(x_75);
 x_83 = lean_box(0);
}
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_add(x_82, x_84);
if (lean_is_scalar(x_83)) {
 x_86 = lean_alloc_ctor(0, 6, 0);
} else {
 x_86 = x_83;
}
lean_ctor_set(x_86, 0, x_77);
lean_ctor_set(x_86, 1, x_78);
lean_ctor_set(x_86, 2, x_79);
lean_ctor_set(x_86, 3, x_80);
lean_ctor_set(x_86, 4, x_81);
lean_ctor_set(x_86, 5, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_76);
x_88 = lean_ctor_get(x_2, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_2, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_90 = x_2;
} else {
 lean_dec_ref(x_2);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_88, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_88, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_88, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_88, 4);
lean_inc(x_95);
x_96 = lean_ctor_get(x_88, 5);
lean_inc(x_96);
x_97 = lean_ctor_get(x_88, 6);
lean_inc(x_97);
x_98 = lean_ctor_get(x_88, 7);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_88, sizeof(void*)*10);
x_100 = lean_ctor_get_uint8(x_88, sizeof(void*)*10 + 1);
x_101 = lean_ctor_get_uint8(x_88, sizeof(void*)*10 + 2);
x_102 = lean_ctor_get(x_88, 9);
lean_inc(x_102);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 lean_ctor_release(x_88, 4);
 lean_ctor_release(x_88, 5);
 lean_ctor_release(x_88, 6);
 lean_ctor_release(x_88, 7);
 lean_ctor_release(x_88, 8);
 lean_ctor_release(x_88, 9);
 x_103 = x_88;
} else {
 lean_dec_ref(x_88);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 10, 3);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_91);
lean_ctor_set(x_104, 1, x_92);
lean_ctor_set(x_104, 2, x_93);
lean_ctor_set(x_104, 3, x_94);
lean_ctor_set(x_104, 4, x_95);
lean_ctor_set(x_104, 5, x_96);
lean_ctor_set(x_104, 6, x_97);
lean_ctor_set(x_104, 7, x_98);
lean_ctor_set(x_104, 8, x_82);
lean_ctor_set(x_104, 9, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*10, x_99);
lean_ctor_set_uint8(x_104, sizeof(void*)*10 + 1, x_100);
lean_ctor_set_uint8(x_104, sizeof(void*)*10 + 2, x_101);
if (lean_is_scalar(x_90)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_90;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_89);
x_106 = lean_apply_2(x_1, x_105, x_87);
return x_106;
}
}
}
lean_object* l_Lean_Elab_Tactic_withFreshMacroScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withFreshMacroScope___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadQuotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getCurrMacroScope___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadQuotation___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getMainModule___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadQuotation___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withFreshMacroScope), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadQuotation___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_monadQuotation___closed__1;
x_2 = l_Lean_Elab_Tactic_monadQuotation___closed__2;
x_3 = l_Lean_Elab_Tactic_monadQuotation___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadQuotation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_monadQuotation___closed__4;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_mkMacroAttribute___closed__2;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticElabAttribute");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__1;
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinTactic");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__3;
x_3 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_4 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__2;
x_5 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__2;
x_6 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__6;
x_7 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1;
x_8 = l_Lean_Elab_mkElabAttribute___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_1);
return x_8;
}
}
lean_object* l_Std_mkHashMap___at_Lean_Elab_Tactic_tacticElabAttribute___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__1___closed__1;
x_3 = l_Std_PersistentHashMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__1___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__3;
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
lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_logTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_logTrace___boxed), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_trace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_traceAtCmdPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_traceAtCmdPos), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_dbgTrace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Elab_Tactic_dbgTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dbgTrace___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
lean_inc(x_2);
x_6 = l_Lean_Syntax_prettyPrint(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_MessageData_ofList___closed__3;
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Lean_Elab_Term_11__elabUsingElabFnsAux___main___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_2, x_13, x_4, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
x_17 = l_Lean_Elab_Tactic_save(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_18 = lean_apply_3(x_15, x_2, x_4, x_5);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_20; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = l_Lean_Elab_Tactic_restore(x_21, x_17);
lean_dec(x_17);
lean_ctor_set(x_18, 1, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = l_Lean_Elab_Tactic_restore(x_24, x_17);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_inc(x_1);
{
lean_object* _tmp_2 = x_16;
lean_object* _tmp_4 = x_1;
x_3 = _tmp_2;
x_5 = _tmp_4;
}
goto _start;
}
}
else
{
lean_dec(x_18);
lean_dec(x_17);
lean_inc(x_1);
{
lean_object* _tmp_2 = x_16;
lean_object* _tmp_4 = x_1;
x_3 = _tmp_2;
x_5 = _tmp_4;
}
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_withMacroExpansion___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_2);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_7, 7, x_11);
x_12 = lean_apply_2(x_3, x_4, x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_ctor_get(x_7, 2);
x_16 = lean_ctor_get(x_7, 3);
x_17 = lean_ctor_get(x_7, 4);
x_18 = lean_ctor_get(x_7, 5);
x_19 = lean_ctor_get(x_7, 6);
x_20 = lean_ctor_get(x_7, 7);
x_21 = lean_ctor_get(x_7, 8);
x_22 = lean_ctor_get_uint8(x_7, sizeof(void*)*10);
x_23 = lean_ctor_get_uint8(x_7, sizeof(void*)*10 + 1);
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*10 + 2);
x_25 = lean_ctor_get(x_7, 9);
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
lean_dec(x_7);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_2);
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
lean_ctor_set(x_4, 0, x_28);
x_29 = lean_apply_2(x_3, x_4, x_5);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_4);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_30, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 4);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 5);
lean_inc(x_37);
x_38 = lean_ctor_get(x_30, 6);
lean_inc(x_38);
x_39 = lean_ctor_get(x_30, 7);
lean_inc(x_39);
x_40 = lean_ctor_get(x_30, 8);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_30, sizeof(void*)*10);
x_42 = lean_ctor_get_uint8(x_30, sizeof(void*)*10 + 1);
x_43 = lean_ctor_get_uint8(x_30, sizeof(void*)*10 + 2);
x_44 = lean_ctor_get(x_30, 9);
lean_inc(x_44);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 lean_ctor_release(x_30, 3);
 lean_ctor_release(x_30, 4);
 lean_ctor_release(x_30, 5);
 lean_ctor_release(x_30, 6);
 lean_ctor_release(x_30, 7);
 lean_ctor_release(x_30, 8);
 lean_ctor_release(x_30, 9);
 x_45 = x_30;
} else {
 lean_dec_ref(x_30);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_2);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_39);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 10, 3);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_32);
lean_ctor_set(x_48, 1, x_33);
lean_ctor_set(x_48, 2, x_34);
lean_ctor_set(x_48, 3, x_35);
lean_ctor_set(x_48, 4, x_36);
lean_ctor_set(x_48, 5, x_37);
lean_ctor_set(x_48, 6, x_38);
lean_ctor_set(x_48, 7, x_47);
lean_ctor_set(x_48, 8, x_40);
lean_ctor_set(x_48, 9, x_44);
lean_ctor_set_uint8(x_48, sizeof(void*)*10, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*10 + 1, x_42);
lean_ctor_set_uint8(x_48, sizeof(void*)*10 + 2, x_43);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_31);
x_50 = lean_apply_2(x_3, x_49, x_5);
return x_50;
}
}
}
lean_object* l_Lean_Elab_Tactic_withMacroExpansion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMacroExpansion___rarg), 5, 0);
return x_2;
}
}
lean_object* l_ReaderT_lift___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
lean_object* l_ReaderT_lift___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 5);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = lean_ctor_get(x_5, 5);
lean_dec(x_7);
lean_ctor_set(x_5, 5, x_1);
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
x_14 = lean_ctor_get(x_5, 4);
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
lean_ctor_set(x_15, 4, x_14);
lean_ctor_set(x_15, 5, x_1);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_18, 4);
lean_inc(x_24);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 x_25 = x_18;
} else {
 lean_dec_ref(x_18);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(0, 6, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set(x_26, 4, x_24);
lean_ctor_set(x_26, 5, x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_EStateM_MonadStateOf___closed__2;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__1;
x_2 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__3___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_monadLog___closed__1;
x_2 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__4;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__4___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_monadLog___closed__1;
x_2 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__6;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getEnv___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__2___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_throwErrorAt), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_throwUnsupportedSyntax), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__8;
x_2 = l_Lean_Elab_Tactic_monadQuotation___closed__1;
x_3 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__3;
x_4 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__9;
x_5 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__5;
x_6 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__7;
x_7 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__10;
x_8 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__11;
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
lean_object* _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__12;
return x_1;
}
}
lean_object* l_ReaderT_lift___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_lift___at_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___lambda__4(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
lean_inc(x_2);
x_6 = l_Lean_Syntax_getKind(x_2);
x_7 = l_Lean_Name_toString___closed__1;
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_6);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_Meta_Exception_toMessageData___closed__48;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Elab_Term_elabUsingElabFns___closed__6;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_2, x_14, x_4, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_dec(x_3);
x_18 = l_Lean_Elab_Tactic_getCurrMacroScope(x_4, x_5);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Elab_Tactic_save(x_19);
x_35 = l_Lean_Elab_Tactic_getCurrMacroScope(x_4, x_19);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Tactic_getEnv___rarg(x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
x_46 = lean_ctor_get(x_40, 2);
x_47 = lean_ctor_get(x_40, 3);
x_48 = lean_ctor_get(x_40, 4);
x_49 = lean_ctor_get(x_40, 5);
x_50 = lean_ctor_get(x_4, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_ctor_get(x_51, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 4);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_environment_main_module(x_41);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_36);
lean_ctor_set(x_55, 2, x_52);
lean_ctor_set(x_55, 3, x_53);
lean_inc(x_2);
x_56 = lean_apply_3(x_16, x_2, x_55, x_49);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_39);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_39, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_39, 0);
lean_dec(x_59);
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_dec(x_56);
lean_ctor_set(x_40, 5, x_61);
x_21 = x_60;
x_22 = x_39;
goto block_34;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_39);
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_dec(x_56);
lean_ctor_set(x_40, 5, x_63);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_40);
lean_ctor_set(x_64, 1, x_42);
x_21 = x_62;
x_22 = x_64;
goto block_34;
}
}
else
{
lean_object* x_65; 
lean_free_object(x_40);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_42);
x_65 = lean_ctor_get(x_56, 0);
lean_inc(x_65);
lean_dec(x_56);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_inc(x_4);
x_70 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_66, x_69, x_4, x_39);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_21 = x_71;
x_22 = x_72;
goto block_34;
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_ctor_get(x_70, 1);
x_76 = l_Lean_Elab_Tactic_restore(x_75, x_20);
lean_dec(x_20);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_70, 1, x_76);
return x_70;
}
else
{
lean_free_object(x_70);
lean_dec(x_74);
x_3 = x_17;
x_5 = x_76;
goto _start;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_70, 0);
x_79 = lean_ctor_get(x_70, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_70);
x_80 = l_Lean_Elab_Tactic_restore(x_79, x_20);
lean_dec(x_20);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_81; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
else
{
lean_dec(x_78);
x_3 = x_17;
x_5 = x_80;
goto _start;
}
}
}
}
else
{
lean_object* x_83; 
lean_inc(x_4);
x_83 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_4, x_39);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_21 = x_84;
x_22 = x_85;
goto block_34;
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_83, 0);
x_88 = lean_ctor_get(x_83, 1);
x_89 = l_Lean_Elab_Tactic_restore(x_88, x_20);
lean_dec(x_20);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_83, 1, x_89);
return x_83;
}
else
{
lean_free_object(x_83);
lean_dec(x_87);
x_3 = x_17;
x_5 = x_89;
goto _start;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_83, 0);
x_92 = lean_ctor_get(x_83, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_83);
x_93 = l_Lean_Elab_Tactic_restore(x_92, x_20);
lean_dec(x_20);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_94; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
else
{
lean_dec(x_91);
x_3 = x_17;
x_5 = x_93;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_96 = lean_ctor_get(x_40, 0);
x_97 = lean_ctor_get(x_40, 1);
x_98 = lean_ctor_get(x_40, 2);
x_99 = lean_ctor_get(x_40, 3);
x_100 = lean_ctor_get(x_40, 4);
x_101 = lean_ctor_get(x_40, 5);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_40);
x_102 = lean_ctor_get(x_4, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_ctor_get(x_103, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 4);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_environment_main_module(x_41);
x_107 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_36);
lean_ctor_set(x_107, 2, x_104);
lean_ctor_set(x_107, 3, x_105);
lean_inc(x_2);
x_108 = lean_apply_3(x_16, x_2, x_107, x_101);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_109 = x_39;
} else {
 lean_dec_ref(x_39);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_112, 0, x_96);
lean_ctor_set(x_112, 1, x_97);
lean_ctor_set(x_112, 2, x_98);
lean_ctor_set(x_112, 3, x_99);
lean_ctor_set(x_112, 4, x_100);
lean_ctor_set(x_112, 5, x_111);
if (lean_is_scalar(x_109)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_109;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_42);
x_21 = x_110;
x_22 = x_113;
goto block_34;
}
else
{
lean_object* x_114; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_42);
x_114 = lean_ctor_get(x_108, 0);
lean_inc(x_114);
lean_dec(x_108);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_117);
lean_inc(x_4);
x_119 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_115, x_118, x_4, x_39);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_21 = x_120;
x_22 = x_121;
goto block_34;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_119, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_124 = x_119;
} else {
 lean_dec_ref(x_119);
 x_124 = lean_box(0);
}
x_125 = l_Lean_Elab_Tactic_restore(x_123, x_20);
lean_dec(x_20);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_126; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
else
{
lean_dec(x_124);
lean_dec(x_122);
x_3 = x_17;
x_5 = x_125;
goto _start;
}
}
}
else
{
lean_object* x_128; 
lean_inc(x_4);
x_128 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_4, x_39);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_21 = x_129;
x_22 = x_130;
goto block_34;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_133 = x_128;
} else {
 lean_dec_ref(x_128);
 x_133 = lean_box(0);
}
x_134 = l_Lean_Elab_Tactic_restore(x_132, x_20);
lean_dec(x_20);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_135; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_133)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_133;
}
lean_ctor_set(x_135, 0, x_131);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
else
{
lean_dec(x_133);
lean_dec(x_131);
x_3 = x_17;
x_5 = x_134;
goto _start;
}
}
}
}
}
block_34:
{
lean_object* x_23; 
lean_inc(x_1);
lean_inc(x_4);
x_23 = lean_apply_3(x_1, x_21, x_4, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = l_Lean_Elab_Tactic_restore(x_26, x_20);
lean_dec(x_20);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_23, 1, x_27);
return x_23;
}
else
{
lean_free_object(x_23);
lean_dec(x_25);
x_3 = x_17;
x_5 = x_27;
goto _start;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = l_Lean_Elab_Tactic_restore(x_30, x_20);
lean_dec(x_20);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_32; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
else
{
lean_dec(x_29);
x_3 = x_17;
x_5 = x_31;
goto _start;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_expandTacticMacro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Lean_Elab_Tactic_getEnv___rarg(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_2);
x_8 = l_Lean_Syntax_getKind(x_2);
x_9 = l_Lean_Elab_macroAttribute;
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = l_Lean_PersistentEnvExtension_getState___rarg(x_10, x_6);
lean_dec(x_6);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_12, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main(x_1, x_2, x_14, x_3, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main(x_1, x_2, x_16, x_3, x_7);
return x_17;
}
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_23 = l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5(x_4, x_2);
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
x_9 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5(x_8, x_2);
lean_dec(x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_5 = l_Lean_Syntax_getKind(x_1);
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_5);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_Meta_Exception_toMessageData___closed__48;
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Elab_Term_elabUsingElabFns___closed__6;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_1, x_13, x_3, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lean_Elab_Tactic_getCurrMacroScope(x_3, x_4);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Elab_Tactic_save(x_18);
x_34 = l_Lean_Elab_Tactic_getCurrMacroScope(x_3, x_18);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Tactic_getEnv___rarg(x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
x_45 = lean_ctor_get(x_39, 2);
x_46 = lean_ctor_get(x_39, 3);
x_47 = lean_ctor_get(x_39, 4);
x_48 = lean_ctor_get(x_39, 5);
x_49 = lean_ctor_get(x_3, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get(x_50, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 4);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_environment_main_module(x_40);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_35);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_52);
lean_inc(x_1);
x_55 = lean_apply_3(x_15, x_1, x_54, x_48);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_38);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_38, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_38, 0);
lean_dec(x_58);
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_dec(x_55);
lean_ctor_set(x_39, 5, x_60);
x_20 = x_59;
x_21 = x_38;
goto block_33;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_38);
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_dec(x_55);
lean_ctor_set(x_39, 5, x_62);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_39);
lean_ctor_set(x_63, 1, x_41);
x_20 = x_61;
x_21 = x_63;
goto block_33;
}
}
else
{
lean_object* x_64; 
lean_free_object(x_39);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_41);
x_64 = lean_ctor_get(x_55, 0);
lean_inc(x_64);
lean_dec(x_55);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
lean_inc(x_3);
x_69 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_65, x_68, x_3, x_38);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_20 = x_70;
x_21 = x_71;
goto block_33;
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_69);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 0);
x_74 = lean_ctor_get(x_69, 1);
x_75 = l_Lean_Elab_Tactic_restore(x_74, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_69, 1, x_75);
return x_69;
}
else
{
lean_free_object(x_69);
lean_dec(x_73);
x_2 = x_16;
x_4 = x_75;
goto _start;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_69, 0);
x_78 = lean_ctor_get(x_69, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_69);
x_79 = l_Lean_Elab_Tactic_restore(x_78, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_80; 
lean_dec(x_3);
lean_dec(x_1);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
else
{
lean_dec(x_77);
x_2 = x_16;
x_4 = x_79;
goto _start;
}
}
}
}
else
{
lean_object* x_82; 
lean_inc(x_3);
x_82 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_3, x_38);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_20 = x_83;
x_21 = x_84;
goto block_33;
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_82);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_82, 0);
x_87 = lean_ctor_get(x_82, 1);
x_88 = l_Lean_Elab_Tactic_restore(x_87, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_82, 1, x_88);
return x_82;
}
else
{
lean_free_object(x_82);
lean_dec(x_86);
x_2 = x_16;
x_4 = x_88;
goto _start;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_82, 0);
x_91 = lean_ctor_get(x_82, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_82);
x_92 = l_Lean_Elab_Tactic_restore(x_91, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_93; 
lean_dec(x_3);
lean_dec(x_1);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
else
{
lean_dec(x_90);
x_2 = x_16;
x_4 = x_92;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_95 = lean_ctor_get(x_39, 0);
x_96 = lean_ctor_get(x_39, 1);
x_97 = lean_ctor_get(x_39, 2);
x_98 = lean_ctor_get(x_39, 3);
x_99 = lean_ctor_get(x_39, 4);
x_100 = lean_ctor_get(x_39, 5);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_39);
x_101 = lean_ctor_get(x_3, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_ctor_get(x_102, 3);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 4);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_environment_main_module(x_40);
x_106 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_35);
lean_ctor_set(x_106, 2, x_103);
lean_ctor_set(x_106, 3, x_104);
lean_inc(x_1);
x_107 = lean_apply_3(x_15, x_1, x_106, x_100);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_108 = x_38;
} else {
 lean_dec_ref(x_38);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec(x_107);
x_111 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_111, 0, x_95);
lean_ctor_set(x_111, 1, x_96);
lean_ctor_set(x_111, 2, x_97);
lean_ctor_set(x_111, 3, x_98);
lean_ctor_set(x_111, 4, x_99);
lean_ctor_set(x_111, 5, x_110);
if (lean_is_scalar(x_108)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_108;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_41);
x_20 = x_109;
x_21 = x_112;
goto block_33;
}
else
{
lean_object* x_113; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_41);
x_113 = lean_ctor_get(x_107, 0);
lean_inc(x_113);
lean_dec(x_107);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
lean_inc(x_3);
x_118 = l_Lean_Elab_Tactic_throwErrorAt___rarg(x_114, x_117, x_3, x_38);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_20 = x_119;
x_21 = x_120;
goto block_33;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_123 = x_118;
} else {
 lean_dec_ref(x_118);
 x_123 = lean_box(0);
}
x_124 = l_Lean_Elab_Tactic_restore(x_122, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_125; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
else
{
lean_dec(x_123);
lean_dec(x_121);
x_2 = x_16;
x_4 = x_124;
goto _start;
}
}
}
else
{
lean_object* x_127; 
lean_inc(x_3);
x_127 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_3, x_38);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_20 = x_128;
x_21 = x_129;
goto block_33;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_132 = x_127;
} else {
 lean_dec_ref(x_127);
 x_132 = lean_box(0);
}
x_133 = l_Lean_Elab_Tactic_restore(x_131, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_134; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_130);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
else
{
lean_dec(x_132);
lean_dec(x_130);
x_2 = x_16;
x_4 = x_133;
goto _start;
}
}
}
}
}
block_33:
{
lean_object* x_22; 
lean_inc(x_3);
x_22 = l_Lean_Elab_Tactic_evalTactic___main(x_20, x_3, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_1);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = l_Lean_Elab_Tactic_restore(x_25, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_22, 1, x_26);
return x_22;
}
else
{
lean_free_object(x_22);
lean_dec(x_24);
x_2 = x_16;
x_4 = x_26;
goto _start;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = l_Lean_Elab_Tactic_restore(x_29, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_31; 
lean_dec(x_3);
lean_dec(x_1);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_dec(x_28);
x_2 = x_16;
x_4 = x_30;
goto _start;
}
}
}
}
}
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_array_fget(x_2, x_3);
lean_inc(x_5);
x_11 = l_Lean_Elab_Tactic_evalTactic___main(x_10, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_12;
x_6 = x_13;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_3);
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
}
lean_object* l_Lean_Elab_Tactic_evalTactic___main___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalTactic___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected command");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalTactic___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalTactic___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalTactic___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalTactic___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalTactic___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 2);
x_11 = lean_ctor_get(x_5, 3);
x_12 = lean_ctor_get(x_5, 4);
x_13 = lean_ctor_get(x_5, 5);
x_14 = lean_ctor_get(x_5, 6);
x_15 = lean_ctor_get(x_5, 7);
x_16 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_18 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_19 = lean_ctor_get(x_5, 9);
x_20 = l_Lean_Elab_replaceRef(x_1, x_19);
lean_dec(x_19);
lean_inc(x_20);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_ctor_set(x_5, 9, x_20);
lean_inc(x_7);
x_249 = lean_ctor_get(x_8, 3);
lean_inc(x_249);
x_250 = lean_ctor_get(x_8, 4);
lean_inc(x_250);
x_251 = lean_nat_dec_eq(x_249, x_250);
lean_dec(x_250);
lean_dec(x_249);
if (x_251 == 0)
{
lean_dec(x_2);
x_21 = x_3;
goto block_248;
}
else
{
lean_object* x_252; lean_object* x_253; 
x_252 = l_Lean_Core_checkRecDepth___closed__2;
x_253 = l_Lean_Elab_Tactic_throwError___rarg(x_252, x_2, x_3);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; 
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
lean_dec(x_253);
x_21 = x_254;
goto block_248;
}
else
{
uint8_t x_255; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_255 = !lean_is_exclusive(x_253);
if (x_255 == 0)
{
return x_253;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_253, 0);
x_257 = lean_ctor_get(x_253, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_253);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
block_248:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_8);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_8, 3);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_23, x_24);
lean_dec(x_23);
lean_ctor_set(x_8, 3, x_25);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_27, 5);
x_30 = lean_nat_add(x_29, x_24);
lean_ctor_set(x_27, 5, x_30);
x_31 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_9);
lean_ctor_set(x_31, 2, x_10);
lean_ctor_set(x_31, 3, x_11);
lean_ctor_set(x_31, 4, x_12);
lean_ctor_set(x_31, 5, x_13);
lean_ctor_set(x_31, 6, x_14);
lean_ctor_set(x_31, 7, x_15);
lean_ctor_set(x_31, 8, x_29);
lean_ctor_set(x_31, 9, x_20);
lean_ctor_set_uint8(x_31, sizeof(void*)*10, x_16);
lean_ctor_set_uint8(x_31, sizeof(void*)*10 + 1, x_17);
lean_ctor_set_uint8(x_31, sizeof(void*)*10 + 2, x_18);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_7);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = l_Lean_nullKind;
x_35 = lean_name_eq(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_inc(x_1);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_36, 0, x_1);
x_37 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__2;
x_38 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 4, 2);
lean_closure_set(x_38, 0, x_37);
lean_closure_set(x_38, 1, x_36);
lean_inc(x_32);
x_39 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_38, x_32, x_21);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_PersistentEnvExtension_getState___rarg(x_42, x_45);
lean_dec(x_45);
lean_dec(x_42);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
lean_inc(x_1);
x_48 = l_Lean_Syntax_getKind(x_1);
x_49 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_47, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = l_Lean_Elab_Tactic_getEnv___rarg(x_40);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Elab_macroAttribute;
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
x_55 = l_Lean_PersistentEnvExtension_getState___rarg(x_54, x_51);
lean_dec(x_51);
lean_dec(x_54);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_56, x_48);
lean_dec(x_48);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_box(0);
x_59 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_58, x_32, x_52);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
lean_dec(x_57);
x_61 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_60, x_32, x_52);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_48);
x_62 = lean_ctor_get(x_49, 0);
lean_inc(x_62);
lean_dec(x_49);
lean_inc(x_40);
x_63 = l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_40, x_1, x_62, x_32, x_40);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_32);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_39);
if (x_64 == 0)
{
return x_39;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_39, 0);
x_66 = lean_ctor_get(x_39, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_39);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_69 = lean_unsigned_to_nat(2u);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_box(0);
x_72 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_69, x_68, x_70, x_71, x_32, x_21);
lean_dec(x_68);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_1);
x_73 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_74 = l_Lean_Elab_Tactic_throwError___rarg(x_73, x_32, x_21);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_75 = lean_ctor_get(x_27, 0);
x_76 = lean_ctor_get(x_27, 1);
x_77 = lean_ctor_get(x_27, 2);
x_78 = lean_ctor_get(x_27, 3);
x_79 = lean_ctor_get(x_27, 4);
x_80 = lean_ctor_get(x_27, 5);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_27);
x_81 = lean_nat_add(x_80, x_24);
x_82 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_79);
lean_ctor_set(x_82, 5, x_81);
lean_ctor_set(x_21, 0, x_82);
x_83 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_83, 0, x_8);
lean_ctor_set(x_83, 1, x_9);
lean_ctor_set(x_83, 2, x_10);
lean_ctor_set(x_83, 3, x_11);
lean_ctor_set(x_83, 4, x_12);
lean_ctor_set(x_83, 5, x_13);
lean_ctor_set(x_83, 6, x_14);
lean_ctor_set(x_83, 7, x_15);
lean_ctor_set(x_83, 8, x_80);
lean_ctor_set(x_83, 9, x_20);
lean_ctor_set_uint8(x_83, sizeof(void*)*10, x_16);
lean_ctor_set_uint8(x_83, sizeof(void*)*10 + 1, x_17);
lean_ctor_set_uint8(x_83, sizeof(void*)*10 + 2, x_18);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_7);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_1, 0);
lean_inc(x_85);
x_86 = l_Lean_nullKind;
x_87 = lean_name_eq(x_85, x_86);
lean_dec(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_inc(x_1);
x_88 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_88, 0, x_1);
x_89 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__2;
x_90 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 4, 2);
lean_closure_set(x_90, 0, x_89);
lean_closure_set(x_90, 1, x_88);
lean_inc(x_84);
x_91 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_90, x_84, x_21);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_93 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l_Lean_PersistentEnvExtension_getState___rarg(x_94, x_97);
lean_dec(x_97);
lean_dec(x_94);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
lean_inc(x_1);
x_100 = l_Lean_Syntax_getKind(x_1);
x_101 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_99, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = l_Lean_Elab_Tactic_getEnv___rarg(x_92);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Lean_Elab_macroAttribute;
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
x_107 = l_Lean_PersistentEnvExtension_getState___rarg(x_106, x_103);
lean_dec(x_103);
lean_dec(x_106);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_108, x_100);
lean_dec(x_100);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_box(0);
x_111 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_110, x_84, x_104);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
lean_dec(x_109);
x_113 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_112, x_84, x_104);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_100);
x_114 = lean_ctor_get(x_101, 0);
lean_inc(x_114);
lean_dec(x_101);
lean_inc(x_92);
x_115 = l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_92, x_1, x_114, x_84, x_92);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_84);
lean_dec(x_1);
x_116 = lean_ctor_get(x_91, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_91, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_118 = x_91;
} else {
 lean_dec_ref(x_91);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_121 = lean_unsigned_to_nat(2u);
x_122 = lean_unsigned_to_nat(0u);
x_123 = lean_box(0);
x_124 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_121, x_120, x_122, x_123, x_84, x_21);
lean_dec(x_120);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_1);
x_125 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_126 = l_Lean_Elab_Tactic_throwError___rarg(x_125, x_84, x_21);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_127 = lean_ctor_get(x_21, 0);
x_128 = lean_ctor_get(x_21, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_21);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_127, 2);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_127, 4);
lean_inc(x_133);
x_134 = lean_ctor_get(x_127, 5);
lean_inc(x_134);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 lean_ctor_release(x_127, 4);
 lean_ctor_release(x_127, 5);
 x_135 = x_127;
} else {
 lean_dec_ref(x_127);
 x_135 = lean_box(0);
}
x_136 = lean_nat_add(x_134, x_24);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(0, 6, 0);
} else {
 x_137 = x_135;
}
lean_ctor_set(x_137, 0, x_129);
lean_ctor_set(x_137, 1, x_130);
lean_ctor_set(x_137, 2, x_131);
lean_ctor_set(x_137, 3, x_132);
lean_ctor_set(x_137, 4, x_133);
lean_ctor_set(x_137, 5, x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_128);
x_139 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_139, 0, x_8);
lean_ctor_set(x_139, 1, x_9);
lean_ctor_set(x_139, 2, x_10);
lean_ctor_set(x_139, 3, x_11);
lean_ctor_set(x_139, 4, x_12);
lean_ctor_set(x_139, 5, x_13);
lean_ctor_set(x_139, 6, x_14);
lean_ctor_set(x_139, 7, x_15);
lean_ctor_set(x_139, 8, x_134);
lean_ctor_set(x_139, 9, x_20);
lean_ctor_set_uint8(x_139, sizeof(void*)*10, x_16);
lean_ctor_set_uint8(x_139, sizeof(void*)*10 + 1, x_17);
lean_ctor_set_uint8(x_139, sizeof(void*)*10 + 2, x_18);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_7);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_1, 0);
lean_inc(x_141);
x_142 = l_Lean_nullKind;
x_143 = lean_name_eq(x_141, x_142);
lean_dec(x_141);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_inc(x_1);
x_144 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_144, 0, x_1);
x_145 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__2;
x_146 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 4, 2);
lean_closure_set(x_146, 0, x_145);
lean_closure_set(x_146, 1, x_144);
lean_inc(x_140);
x_147 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_146, x_140, x_138);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_149 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_148, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec(x_151);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec(x_152);
x_154 = l_Lean_PersistentEnvExtension_getState___rarg(x_150, x_153);
lean_dec(x_153);
lean_dec(x_150);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
lean_inc(x_1);
x_156 = l_Lean_Syntax_getKind(x_1);
x_157 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_155, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_158 = l_Lean_Elab_Tactic_getEnv___rarg(x_148);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Lean_Elab_macroAttribute;
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
x_163 = l_Lean_PersistentEnvExtension_getState___rarg(x_162, x_159);
lean_dec(x_159);
lean_dec(x_162);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_165 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_164, x_156);
lean_dec(x_156);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_box(0);
x_167 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_166, x_140, x_160);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_165, 0);
lean_inc(x_168);
lean_dec(x_165);
x_169 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_168, x_140, x_160);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_156);
x_170 = lean_ctor_get(x_157, 0);
lean_inc(x_170);
lean_dec(x_157);
lean_inc(x_148);
x_171 = l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_148, x_1, x_170, x_140, x_148);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_140);
lean_dec(x_1);
x_172 = lean_ctor_get(x_147, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_147, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_174 = x_147;
} else {
 lean_dec_ref(x_147);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_177 = lean_unsigned_to_nat(2u);
x_178 = lean_unsigned_to_nat(0u);
x_179 = lean_box(0);
x_180 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_177, x_176, x_178, x_179, x_140, x_138);
lean_dec(x_176);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_1);
x_181 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_182 = l_Lean_Elab_Tactic_throwError___rarg(x_181, x_140, x_138);
return x_182;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_183 = lean_ctor_get(x_8, 0);
x_184 = lean_ctor_get(x_8, 1);
x_185 = lean_ctor_get(x_8, 2);
x_186 = lean_ctor_get(x_8, 3);
x_187 = lean_ctor_get(x_8, 4);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_8);
x_188 = lean_unsigned_to_nat(1u);
x_189 = lean_nat_add(x_186, x_188);
lean_dec(x_186);
x_190 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_190, 0, x_183);
lean_ctor_set(x_190, 1, x_184);
lean_ctor_set(x_190, 2, x_185);
lean_ctor_set(x_190, 3, x_189);
lean_ctor_set(x_190, 4, x_187);
x_191 = lean_ctor_get(x_21, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_21, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_193 = x_21;
} else {
 lean_dec_ref(x_21);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_191, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_191, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_191, 2);
lean_inc(x_196);
x_197 = lean_ctor_get(x_191, 3);
lean_inc(x_197);
x_198 = lean_ctor_get(x_191, 4);
lean_inc(x_198);
x_199 = lean_ctor_get(x_191, 5);
lean_inc(x_199);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 lean_ctor_release(x_191, 2);
 lean_ctor_release(x_191, 3);
 lean_ctor_release(x_191, 4);
 lean_ctor_release(x_191, 5);
 x_200 = x_191;
} else {
 lean_dec_ref(x_191);
 x_200 = lean_box(0);
}
x_201 = lean_nat_add(x_199, x_188);
if (lean_is_scalar(x_200)) {
 x_202 = lean_alloc_ctor(0, 6, 0);
} else {
 x_202 = x_200;
}
lean_ctor_set(x_202, 0, x_194);
lean_ctor_set(x_202, 1, x_195);
lean_ctor_set(x_202, 2, x_196);
lean_ctor_set(x_202, 3, x_197);
lean_ctor_set(x_202, 4, x_198);
lean_ctor_set(x_202, 5, x_201);
if (lean_is_scalar(x_193)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_193;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_192);
x_204 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_204, 0, x_190);
lean_ctor_set(x_204, 1, x_9);
lean_ctor_set(x_204, 2, x_10);
lean_ctor_set(x_204, 3, x_11);
lean_ctor_set(x_204, 4, x_12);
lean_ctor_set(x_204, 5, x_13);
lean_ctor_set(x_204, 6, x_14);
lean_ctor_set(x_204, 7, x_15);
lean_ctor_set(x_204, 8, x_199);
lean_ctor_set(x_204, 9, x_20);
lean_ctor_set_uint8(x_204, sizeof(void*)*10, x_16);
lean_ctor_set_uint8(x_204, sizeof(void*)*10 + 1, x_17);
lean_ctor_set_uint8(x_204, sizeof(void*)*10 + 2, x_18);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_7);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_206 = lean_ctor_get(x_1, 0);
lean_inc(x_206);
x_207 = l_Lean_nullKind;
x_208 = lean_name_eq(x_206, x_207);
lean_dec(x_206);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_inc(x_1);
x_209 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_209, 0, x_1);
x_210 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__2;
x_211 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 4, 2);
lean_closure_set(x_211, 0, x_210);
lean_closure_set(x_211, 1, x_209);
lean_inc(x_205);
x_212 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_211, x_205, x_203);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
x_214 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
x_216 = lean_ctor_get(x_213, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
lean_dec(x_216);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
lean_dec(x_217);
x_219 = l_Lean_PersistentEnvExtension_getState___rarg(x_215, x_218);
lean_dec(x_218);
lean_dec(x_215);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec(x_219);
lean_inc(x_1);
x_221 = l_Lean_Syntax_getKind(x_1);
x_222 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_220, x_221);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_223 = l_Lean_Elab_Tactic_getEnv___rarg(x_213);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = l_Lean_Elab_macroAttribute;
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
x_228 = l_Lean_PersistentEnvExtension_getState___rarg(x_227, x_224);
lean_dec(x_224);
lean_dec(x_227);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
lean_dec(x_228);
x_230 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_229, x_221);
lean_dec(x_221);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_box(0);
x_232 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_231, x_205, x_225);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_230, 0);
lean_inc(x_233);
lean_dec(x_230);
x_234 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_233, x_205, x_225);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; 
lean_dec(x_221);
x_235 = lean_ctor_get(x_222, 0);
lean_inc(x_235);
lean_dec(x_222);
lean_inc(x_213);
x_236 = l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_213, x_1, x_235, x_205, x_213);
return x_236;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_205);
lean_dec(x_1);
x_237 = lean_ctor_get(x_212, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_212, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_239 = x_212;
} else {
 lean_dec_ref(x_212);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_241 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_242 = lean_unsigned_to_nat(2u);
x_243 = lean_unsigned_to_nat(0u);
x_244 = lean_box(0);
x_245 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_242, x_241, x_243, x_244, x_205, x_203);
lean_dec(x_241);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_1);
x_246 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_247 = l_Lean_Elab_Tactic_throwError___rarg(x_246, x_205, x_203);
return x_247;
}
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; uint8_t x_270; uint8_t x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_343; lean_object* x_344; uint8_t x_345; 
x_259 = lean_ctor_get(x_2, 1);
x_260 = lean_ctor_get(x_5, 0);
x_261 = lean_ctor_get(x_5, 1);
x_262 = lean_ctor_get(x_5, 2);
x_263 = lean_ctor_get(x_5, 3);
x_264 = lean_ctor_get(x_5, 4);
x_265 = lean_ctor_get(x_5, 5);
x_266 = lean_ctor_get(x_5, 6);
x_267 = lean_ctor_get(x_5, 7);
x_268 = lean_ctor_get(x_5, 8);
x_269 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_270 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_271 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_272 = lean_ctor_get(x_5, 9);
lean_inc(x_272);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_5);
x_273 = l_Lean_Elab_replaceRef(x_1, x_272);
lean_dec(x_272);
lean_inc(x_273);
lean_inc(x_267);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
x_274 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_274, 0, x_260);
lean_ctor_set(x_274, 1, x_261);
lean_ctor_set(x_274, 2, x_262);
lean_ctor_set(x_274, 3, x_263);
lean_ctor_set(x_274, 4, x_264);
lean_ctor_set(x_274, 5, x_265);
lean_ctor_set(x_274, 6, x_266);
lean_ctor_set(x_274, 7, x_267);
lean_ctor_set(x_274, 8, x_268);
lean_ctor_set(x_274, 9, x_273);
lean_ctor_set_uint8(x_274, sizeof(void*)*10, x_269);
lean_ctor_set_uint8(x_274, sizeof(void*)*10 + 1, x_270);
lean_ctor_set_uint8(x_274, sizeof(void*)*10 + 2, x_271);
lean_inc(x_259);
lean_ctor_set(x_2, 0, x_274);
x_343 = lean_ctor_get(x_260, 3);
lean_inc(x_343);
x_344 = lean_ctor_get(x_260, 4);
lean_inc(x_344);
x_345 = lean_nat_dec_eq(x_343, x_344);
lean_dec(x_344);
lean_dec(x_343);
if (x_345 == 0)
{
lean_dec(x_2);
x_275 = x_3;
goto block_342;
}
else
{
lean_object* x_346; lean_object* x_347; 
x_346 = l_Lean_Core_checkRecDepth___closed__2;
x_347 = l_Lean_Elab_Tactic_throwError___rarg(x_346, x_2, x_3);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; 
x_348 = lean_ctor_get(x_347, 1);
lean_inc(x_348);
lean_dec(x_347);
x_275 = x_348;
goto block_342;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_273);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_1);
x_349 = lean_ctor_get(x_347, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_347, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_351 = x_347;
} else {
 lean_dec_ref(x_347);
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
block_342:
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_276 = lean_ctor_get(x_260, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_260, 1);
lean_inc(x_277);
x_278 = lean_ctor_get(x_260, 2);
lean_inc(x_278);
x_279 = lean_ctor_get(x_260, 3);
lean_inc(x_279);
x_280 = lean_ctor_get(x_260, 4);
lean_inc(x_280);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 lean_ctor_release(x_260, 2);
 lean_ctor_release(x_260, 3);
 lean_ctor_release(x_260, 4);
 x_281 = x_260;
} else {
 lean_dec_ref(x_260);
 x_281 = lean_box(0);
}
x_282 = lean_unsigned_to_nat(1u);
x_283 = lean_nat_add(x_279, x_282);
lean_dec(x_279);
if (lean_is_scalar(x_281)) {
 x_284 = lean_alloc_ctor(0, 5, 0);
} else {
 x_284 = x_281;
}
lean_ctor_set(x_284, 0, x_276);
lean_ctor_set(x_284, 1, x_277);
lean_ctor_set(x_284, 2, x_278);
lean_ctor_set(x_284, 3, x_283);
lean_ctor_set(x_284, 4, x_280);
x_285 = lean_ctor_get(x_275, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_275, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_287 = x_275;
} else {
 lean_dec_ref(x_275);
 x_287 = lean_box(0);
}
x_288 = lean_ctor_get(x_285, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_285, 1);
lean_inc(x_289);
x_290 = lean_ctor_get(x_285, 2);
lean_inc(x_290);
x_291 = lean_ctor_get(x_285, 3);
lean_inc(x_291);
x_292 = lean_ctor_get(x_285, 4);
lean_inc(x_292);
x_293 = lean_ctor_get(x_285, 5);
lean_inc(x_293);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 lean_ctor_release(x_285, 2);
 lean_ctor_release(x_285, 3);
 lean_ctor_release(x_285, 4);
 lean_ctor_release(x_285, 5);
 x_294 = x_285;
} else {
 lean_dec_ref(x_285);
 x_294 = lean_box(0);
}
x_295 = lean_nat_add(x_293, x_282);
if (lean_is_scalar(x_294)) {
 x_296 = lean_alloc_ctor(0, 6, 0);
} else {
 x_296 = x_294;
}
lean_ctor_set(x_296, 0, x_288);
lean_ctor_set(x_296, 1, x_289);
lean_ctor_set(x_296, 2, x_290);
lean_ctor_set(x_296, 3, x_291);
lean_ctor_set(x_296, 4, x_292);
lean_ctor_set(x_296, 5, x_295);
if (lean_is_scalar(x_287)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_287;
}
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_286);
x_298 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_298, 0, x_284);
lean_ctor_set(x_298, 1, x_261);
lean_ctor_set(x_298, 2, x_262);
lean_ctor_set(x_298, 3, x_263);
lean_ctor_set(x_298, 4, x_264);
lean_ctor_set(x_298, 5, x_265);
lean_ctor_set(x_298, 6, x_266);
lean_ctor_set(x_298, 7, x_267);
lean_ctor_set(x_298, 8, x_293);
lean_ctor_set(x_298, 9, x_273);
lean_ctor_set_uint8(x_298, sizeof(void*)*10, x_269);
lean_ctor_set_uint8(x_298, sizeof(void*)*10 + 1, x_270);
lean_ctor_set_uint8(x_298, sizeof(void*)*10 + 2, x_271);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_259);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_300 = lean_ctor_get(x_1, 0);
lean_inc(x_300);
x_301 = l_Lean_nullKind;
x_302 = lean_name_eq(x_300, x_301);
lean_dec(x_300);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_inc(x_1);
x_303 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_303, 0, x_1);
x_304 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__2;
x_305 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 4, 2);
lean_closure_set(x_305, 0, x_304);
lean_closure_set(x_305, 1, x_303);
lean_inc(x_299);
x_306 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_305, x_299, x_297);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_307 = lean_ctor_get(x_306, 1);
lean_inc(x_307);
lean_dec(x_306);
x_308 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_309 = lean_ctor_get(x_308, 1);
lean_inc(x_309);
x_310 = lean_ctor_get(x_307, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
lean_dec(x_310);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
lean_dec(x_311);
x_313 = l_Lean_PersistentEnvExtension_getState___rarg(x_309, x_312);
lean_dec(x_312);
lean_dec(x_309);
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
lean_dec(x_313);
lean_inc(x_1);
x_315 = l_Lean_Syntax_getKind(x_1);
x_316 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_314, x_315);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_317 = l_Lean_Elab_Tactic_getEnv___rarg(x_307);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_320 = l_Lean_Elab_macroAttribute;
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
x_322 = l_Lean_PersistentEnvExtension_getState___rarg(x_321, x_318);
lean_dec(x_318);
lean_dec(x_321);
x_323 = lean_ctor_get(x_322, 1);
lean_inc(x_323);
lean_dec(x_322);
x_324 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_323, x_315);
lean_dec(x_315);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; 
x_325 = lean_box(0);
x_326 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_325, x_299, x_319);
return x_326;
}
else
{
lean_object* x_327; lean_object* x_328; 
x_327 = lean_ctor_get(x_324, 0);
lean_inc(x_327);
lean_dec(x_324);
x_328 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_327, x_299, x_319);
return x_328;
}
}
else
{
lean_object* x_329; lean_object* x_330; 
lean_dec(x_315);
x_329 = lean_ctor_get(x_316, 0);
lean_inc(x_329);
lean_dec(x_316);
lean_inc(x_307);
x_330 = l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_307, x_1, x_329, x_299, x_307);
return x_330;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_299);
lean_dec(x_1);
x_331 = lean_ctor_get(x_306, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_306, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_333 = x_306;
} else {
 lean_dec_ref(x_306);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_335 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_336 = lean_unsigned_to_nat(2u);
x_337 = lean_unsigned_to_nat(0u);
x_338 = lean_box(0);
x_339 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_336, x_335, x_337, x_338, x_299, x_297);
lean_dec(x_335);
return x_339;
}
}
else
{
lean_object* x_340; lean_object* x_341; 
lean_dec(x_1);
x_340 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_341 = l_Lean_Elab_Tactic_throwError___rarg(x_340, x_299, x_297);
return x_341;
}
}
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; uint8_t x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_440; lean_object* x_441; uint8_t x_442; 
x_353 = lean_ctor_get(x_2, 0);
x_354 = lean_ctor_get(x_2, 1);
lean_inc(x_354);
lean_inc(x_353);
lean_dec(x_2);
x_355 = lean_ctor_get(x_353, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_353, 1);
lean_inc(x_356);
x_357 = lean_ctor_get(x_353, 2);
lean_inc(x_357);
x_358 = lean_ctor_get(x_353, 3);
lean_inc(x_358);
x_359 = lean_ctor_get(x_353, 4);
lean_inc(x_359);
x_360 = lean_ctor_get(x_353, 5);
lean_inc(x_360);
x_361 = lean_ctor_get(x_353, 6);
lean_inc(x_361);
x_362 = lean_ctor_get(x_353, 7);
lean_inc(x_362);
x_363 = lean_ctor_get(x_353, 8);
lean_inc(x_363);
x_364 = lean_ctor_get_uint8(x_353, sizeof(void*)*10);
x_365 = lean_ctor_get_uint8(x_353, sizeof(void*)*10 + 1);
x_366 = lean_ctor_get_uint8(x_353, sizeof(void*)*10 + 2);
x_367 = lean_ctor_get(x_353, 9);
lean_inc(x_367);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 lean_ctor_release(x_353, 4);
 lean_ctor_release(x_353, 5);
 lean_ctor_release(x_353, 6);
 lean_ctor_release(x_353, 7);
 lean_ctor_release(x_353, 8);
 lean_ctor_release(x_353, 9);
 x_368 = x_353;
} else {
 lean_dec_ref(x_353);
 x_368 = lean_box(0);
}
x_369 = l_Lean_Elab_replaceRef(x_1, x_367);
lean_dec(x_367);
lean_inc(x_369);
lean_inc(x_362);
lean_inc(x_361);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
lean_inc(x_355);
if (lean_is_scalar(x_368)) {
 x_370 = lean_alloc_ctor(0, 10, 3);
} else {
 x_370 = x_368;
}
lean_ctor_set(x_370, 0, x_355);
lean_ctor_set(x_370, 1, x_356);
lean_ctor_set(x_370, 2, x_357);
lean_ctor_set(x_370, 3, x_358);
lean_ctor_set(x_370, 4, x_359);
lean_ctor_set(x_370, 5, x_360);
lean_ctor_set(x_370, 6, x_361);
lean_ctor_set(x_370, 7, x_362);
lean_ctor_set(x_370, 8, x_363);
lean_ctor_set(x_370, 9, x_369);
lean_ctor_set_uint8(x_370, sizeof(void*)*10, x_364);
lean_ctor_set_uint8(x_370, sizeof(void*)*10 + 1, x_365);
lean_ctor_set_uint8(x_370, sizeof(void*)*10 + 2, x_366);
lean_inc(x_354);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_354);
x_440 = lean_ctor_get(x_355, 3);
lean_inc(x_440);
x_441 = lean_ctor_get(x_355, 4);
lean_inc(x_441);
x_442 = lean_nat_dec_eq(x_440, x_441);
lean_dec(x_441);
lean_dec(x_440);
if (x_442 == 0)
{
lean_dec(x_371);
x_372 = x_3;
goto block_439;
}
else
{
lean_object* x_443; lean_object* x_444; 
x_443 = l_Lean_Core_checkRecDepth___closed__2;
x_444 = l_Lean_Elab_Tactic_throwError___rarg(x_443, x_371, x_3);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; 
x_445 = lean_ctor_get(x_444, 1);
lean_inc(x_445);
lean_dec(x_444);
x_372 = x_445;
goto block_439;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_369);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_1);
x_446 = lean_ctor_get(x_444, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_444, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_448 = x_444;
} else {
 lean_dec_ref(x_444);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_446);
lean_ctor_set(x_449, 1, x_447);
return x_449;
}
}
block_439:
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_373 = lean_ctor_get(x_355, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_355, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_355, 2);
lean_inc(x_375);
x_376 = lean_ctor_get(x_355, 3);
lean_inc(x_376);
x_377 = lean_ctor_get(x_355, 4);
lean_inc(x_377);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 lean_ctor_release(x_355, 2);
 lean_ctor_release(x_355, 3);
 lean_ctor_release(x_355, 4);
 x_378 = x_355;
} else {
 lean_dec_ref(x_355);
 x_378 = lean_box(0);
}
x_379 = lean_unsigned_to_nat(1u);
x_380 = lean_nat_add(x_376, x_379);
lean_dec(x_376);
if (lean_is_scalar(x_378)) {
 x_381 = lean_alloc_ctor(0, 5, 0);
} else {
 x_381 = x_378;
}
lean_ctor_set(x_381, 0, x_373);
lean_ctor_set(x_381, 1, x_374);
lean_ctor_set(x_381, 2, x_375);
lean_ctor_set(x_381, 3, x_380);
lean_ctor_set(x_381, 4, x_377);
x_382 = lean_ctor_get(x_372, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_372, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_384 = x_372;
} else {
 lean_dec_ref(x_372);
 x_384 = lean_box(0);
}
x_385 = lean_ctor_get(x_382, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_382, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_382, 2);
lean_inc(x_387);
x_388 = lean_ctor_get(x_382, 3);
lean_inc(x_388);
x_389 = lean_ctor_get(x_382, 4);
lean_inc(x_389);
x_390 = lean_ctor_get(x_382, 5);
lean_inc(x_390);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 lean_ctor_release(x_382, 2);
 lean_ctor_release(x_382, 3);
 lean_ctor_release(x_382, 4);
 lean_ctor_release(x_382, 5);
 x_391 = x_382;
} else {
 lean_dec_ref(x_382);
 x_391 = lean_box(0);
}
x_392 = lean_nat_add(x_390, x_379);
if (lean_is_scalar(x_391)) {
 x_393 = lean_alloc_ctor(0, 6, 0);
} else {
 x_393 = x_391;
}
lean_ctor_set(x_393, 0, x_385);
lean_ctor_set(x_393, 1, x_386);
lean_ctor_set(x_393, 2, x_387);
lean_ctor_set(x_393, 3, x_388);
lean_ctor_set(x_393, 4, x_389);
lean_ctor_set(x_393, 5, x_392);
if (lean_is_scalar(x_384)) {
 x_394 = lean_alloc_ctor(0, 2, 0);
} else {
 x_394 = x_384;
}
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_383);
x_395 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_395, 0, x_381);
lean_ctor_set(x_395, 1, x_356);
lean_ctor_set(x_395, 2, x_357);
lean_ctor_set(x_395, 3, x_358);
lean_ctor_set(x_395, 4, x_359);
lean_ctor_set(x_395, 5, x_360);
lean_ctor_set(x_395, 6, x_361);
lean_ctor_set(x_395, 7, x_362);
lean_ctor_set(x_395, 8, x_390);
lean_ctor_set(x_395, 9, x_369);
lean_ctor_set_uint8(x_395, sizeof(void*)*10, x_364);
lean_ctor_set_uint8(x_395, sizeof(void*)*10 + 1, x_365);
lean_ctor_set_uint8(x_395, sizeof(void*)*10 + 2, x_366);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_354);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_397; lean_object* x_398; uint8_t x_399; 
x_397 = lean_ctor_get(x_1, 0);
lean_inc(x_397);
x_398 = l_Lean_nullKind;
x_399 = lean_name_eq(x_397, x_398);
lean_dec(x_397);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_inc(x_1);
x_400 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_400, 0, x_1);
x_401 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__2;
x_402 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 4, 2);
lean_closure_set(x_402, 0, x_401);
lean_closure_set(x_402, 1, x_400);
lean_inc(x_396);
x_403 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_402, x_396, x_394);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
lean_dec(x_403);
x_405 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_406 = lean_ctor_get(x_405, 1);
lean_inc(x_406);
x_407 = lean_ctor_get(x_404, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
lean_dec(x_407);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
lean_dec(x_408);
x_410 = l_Lean_PersistentEnvExtension_getState___rarg(x_406, x_409);
lean_dec(x_409);
lean_dec(x_406);
x_411 = lean_ctor_get(x_410, 1);
lean_inc(x_411);
lean_dec(x_410);
lean_inc(x_1);
x_412 = l_Lean_Syntax_getKind(x_1);
x_413 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_411, x_412);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_414 = l_Lean_Elab_Tactic_getEnv___rarg(x_404);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_417 = l_Lean_Elab_macroAttribute;
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
x_419 = l_Lean_PersistentEnvExtension_getState___rarg(x_418, x_415);
lean_dec(x_415);
lean_dec(x_418);
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
lean_dec(x_419);
x_421 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_420, x_412);
lean_dec(x_412);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; 
x_422 = lean_box(0);
x_423 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_422, x_396, x_416);
return x_423;
}
else
{
lean_object* x_424; lean_object* x_425; 
x_424 = lean_ctor_get(x_421, 0);
lean_inc(x_424);
lean_dec(x_421);
x_425 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_424, x_396, x_416);
return x_425;
}
}
else
{
lean_object* x_426; lean_object* x_427; 
lean_dec(x_412);
x_426 = lean_ctor_get(x_413, 0);
lean_inc(x_426);
lean_dec(x_413);
lean_inc(x_404);
x_427 = l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_404, x_1, x_426, x_396, x_404);
return x_427;
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_396);
lean_dec(x_1);
x_428 = lean_ctor_get(x_403, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_403, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 x_430 = x_403;
} else {
 lean_dec_ref(x_403);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 2, 0);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_428);
lean_ctor_set(x_431, 1, x_429);
return x_431;
}
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_432 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_433 = lean_unsigned_to_nat(2u);
x_434 = lean_unsigned_to_nat(0u);
x_435 = lean_box(0);
x_436 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_433, x_432, x_434, x_435, x_396, x_394);
lean_dec(x_432);
return x_436;
}
}
else
{
lean_object* x_437; lean_object* x_438; 
lean_dec(x_1);
x_437 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_438 = l_Lean_Elab_Tactic_throwError___rarg(x_437, x_396, x_394);
return x_438;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_evalTactic___main___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalTactic___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_adaptExpander(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_6, 7);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_6, 7, x_14);
x_15 = l_Lean_Elab_Tactic_evalTactic___main(x_7, x_3, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 2);
x_19 = lean_ctor_get(x_6, 3);
x_20 = lean_ctor_get(x_6, 4);
x_21 = lean_ctor_get(x_6, 5);
x_22 = lean_ctor_get(x_6, 6);
x_23 = lean_ctor_get(x_6, 7);
x_24 = lean_ctor_get(x_6, 8);
x_25 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_26 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
x_27 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 2);
x_28 = lean_ctor_get(x_6, 9);
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
lean_dec(x_6);
lean_inc(x_7);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_7);
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
lean_ctor_set(x_3, 0, x_31);
x_32 = l_Lean_Elab_Tactic_evalTactic___main(x_7, x_3, x_8);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_33 = lean_ctor_get(x_3, 1);
lean_inc(x_33);
lean_dec(x_3);
x_34 = lean_ctor_get(x_6, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_6, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_6, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_6, 4);
lean_inc(x_38);
x_39 = lean_ctor_get(x_6, 5);
lean_inc(x_39);
x_40 = lean_ctor_get(x_6, 6);
lean_inc(x_40);
x_41 = lean_ctor_get(x_6, 7);
lean_inc(x_41);
x_42 = lean_ctor_get(x_6, 8);
lean_inc(x_42);
x_43 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_44 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
x_45 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 2);
x_46 = lean_ctor_get(x_6, 9);
lean_inc(x_46);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 lean_ctor_release(x_6, 7);
 lean_ctor_release(x_6, 8);
 lean_ctor_release(x_6, 9);
 x_47 = x_6;
} else {
 lean_dec_ref(x_6);
 x_47 = lean_box(0);
}
lean_inc(x_7);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_2);
lean_ctor_set(x_48, 1, x_7);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 10, 3);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_34);
lean_ctor_set(x_50, 1, x_35);
lean_ctor_set(x_50, 2, x_36);
lean_ctor_set(x_50, 3, x_37);
lean_ctor_set(x_50, 4, x_38);
lean_ctor_set(x_50, 5, x_39);
lean_ctor_set(x_50, 6, x_40);
lean_ctor_set(x_50, 7, x_49);
lean_ctor_set(x_50, 8, x_42);
lean_ctor_set(x_50, 9, x_46);
lean_ctor_set_uint8(x_50, sizeof(void*)*10, x_43);
lean_ctor_set_uint8(x_50, sizeof(void*)*10 + 1, x_44);
lean_ctor_set_uint8(x_50, sizeof(void*)*10 + 2, x_45);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_33);
x_52 = l_Lean_Elab_Tactic_evalTactic___main(x_7, x_51, x_8);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_5);
if (x_53 == 0)
{
return x_5;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_5, 0);
x_55 = lean_ctor_get(x_5, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_5);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_withLCtx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_dec(x_14);
lean_ctor_set(x_7, 2, x_2);
lean_ctor_set(x_7, 1, x_1);
x_15 = lean_apply_2(x_3, x_4, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_2);
lean_ctor_set(x_19, 3, x_17);
lean_ctor_set(x_19, 4, x_18);
lean_ctor_set(x_6, 0, x_19);
x_20 = lean_apply_2(x_3, x_4, x_5);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 2);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 4);
x_25 = lean_ctor_get(x_6, 5);
x_26 = lean_ctor_get(x_6, 6);
x_27 = lean_ctor_get(x_6, 7);
x_28 = lean_ctor_get(x_6, 8);
x_29 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_30 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
x_31 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 2);
x_32 = lean_ctor_get(x_6, 9);
lean_inc(x_32);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_33 = lean_ctor_get(x_7, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_7, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_7, 4);
lean_inc(x_35);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 x_36 = x_7;
} else {
 lean_dec_ref(x_7);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 5, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_1);
lean_ctor_set(x_37, 2, x_2);
lean_ctor_set(x_37, 3, x_34);
lean_ctor_set(x_37, 4, x_35);
x_38 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_21);
lean_ctor_set(x_38, 2, x_22);
lean_ctor_set(x_38, 3, x_23);
lean_ctor_set(x_38, 4, x_24);
lean_ctor_set(x_38, 5, x_25);
lean_ctor_set(x_38, 6, x_26);
lean_ctor_set(x_38, 7, x_27);
lean_ctor_set(x_38, 8, x_28);
lean_ctor_set(x_38, 9, x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*10, x_29);
lean_ctor_set_uint8(x_38, sizeof(void*)*10 + 1, x_30);
lean_ctor_set_uint8(x_38, sizeof(void*)*10 + 2, x_31);
lean_ctor_set(x_4, 0, x_38);
x_39 = lean_apply_2(x_3, x_4, x_5);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = lean_ctor_get(x_6, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_6, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_6, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_6, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_6, 5);
lean_inc(x_45);
x_46 = lean_ctor_get(x_6, 6);
lean_inc(x_46);
x_47 = lean_ctor_get(x_6, 7);
lean_inc(x_47);
x_48 = lean_ctor_get(x_6, 8);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_50 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
x_51 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 2);
x_52 = lean_ctor_get(x_6, 9);
lean_inc(x_52);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 lean_ctor_release(x_6, 7);
 lean_ctor_release(x_6, 8);
 lean_ctor_release(x_6, 9);
 x_53 = x_6;
} else {
 lean_dec_ref(x_6);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_7, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_7, 3);
lean_inc(x_55);
x_56 = lean_ctor_get(x_7, 4);
lean_inc(x_56);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 x_57 = x_7;
} else {
 lean_dec_ref(x_7);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 5, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_1);
lean_ctor_set(x_58, 2, x_2);
lean_ctor_set(x_58, 3, x_55);
lean_ctor_set(x_58, 4, x_56);
if (lean_is_scalar(x_53)) {
 x_59 = lean_alloc_ctor(0, 10, 3);
} else {
 x_59 = x_53;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_41);
lean_ctor_set(x_59, 2, x_42);
lean_ctor_set(x_59, 3, x_43);
lean_ctor_set(x_59, 4, x_44);
lean_ctor_set(x_59, 5, x_45);
lean_ctor_set(x_59, 6, x_46);
lean_ctor_set(x_59, 7, x_47);
lean_ctor_set(x_59, 8, x_48);
lean_ctor_set(x_59, 9, x_52);
lean_ctor_set_uint8(x_59, sizeof(void*)*10, x_49);
lean_ctor_set_uint8(x_59, sizeof(void*)*10 + 1, x_50);
lean_ctor_set_uint8(x_59, sizeof(void*)*10 + 2, x_51);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_40);
x_61 = lean_apply_2(x_3, x_60, x_5);
return x_61;
}
}
}
lean_object* l_Lean_Elab_Tactic_withLCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withLCtx___rarg), 5, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_resetSynthInstanceCache___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_resetSynthInstanceCache(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
x_4 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_161; lean_object* x_162; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_161 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_2);
x_162 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_161, x_2, x_3);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_164 = l_Lean_Elab_Tactic_save(x_163);
x_165 = lean_apply_2(x_1, x_2, x_163);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_164);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_166);
x_8 = x_168;
x_9 = x_167;
goto block_160;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_ctor_get(x_165, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_165, 1);
lean_inc(x_170);
lean_dec(x_165);
x_171 = l_Lean_Elab_Tactic_restore(x_170, x_164);
lean_dec(x_164);
x_172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_172, 0, x_169);
x_8 = x_172;
x_9 = x_171;
goto block_160;
}
}
else
{
uint8_t x_173; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_173 = !lean_is_exclusive(x_162);
if (x_173 == 0)
{
return x_162;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_162, 0);
x_175 = lean_ctor_get(x_162, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_162);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
block_160:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_9, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_11, 2);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_12, 2);
lean_dec(x_21);
lean_ctor_set(x_12, 2, x_7);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
x_25 = lean_ctor_get(x_12, 3);
x_26 = lean_ctor_get(x_12, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_7);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set(x_11, 2, x_27);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_9);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
x_31 = lean_ctor_get(x_11, 3);
x_32 = lean_ctor_get(x_11, 4);
x_33 = lean_ctor_get(x_11, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_12, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_12, 4);
lean_inc(x_37);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_38 = x_12;
} else {
 lean_dec_ref(x_12);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 5, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_7);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_37);
x_40 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_30);
lean_ctor_set(x_40, 2, x_39);
lean_ctor_set(x_40, 3, x_31);
lean_ctor_set(x_40, 4, x_32);
lean_ctor_set(x_40, 5, x_33);
lean_ctor_set(x_10, 0, x_40);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_13);
lean_ctor_set(x_41, 1, x_9);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_42 = lean_ctor_get(x_10, 1);
x_43 = lean_ctor_get(x_10, 2);
x_44 = lean_ctor_get(x_10, 3);
x_45 = lean_ctor_get(x_10, 4);
x_46 = lean_ctor_get(x_10, 5);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
x_47 = lean_ctor_get(x_11, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_11, 3);
lean_inc(x_49);
x_50 = lean_ctor_get(x_11, 4);
lean_inc(x_50);
x_51 = lean_ctor_get(x_11, 5);
lean_inc(x_51);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_52 = x_11;
} else {
 lean_dec_ref(x_11);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_12, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_12, 3);
lean_inc(x_55);
x_56 = lean_ctor_get(x_12, 4);
lean_inc(x_56);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_57 = x_12;
} else {
 lean_dec_ref(x_12);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 5, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_54);
lean_ctor_set(x_58, 2, x_7);
lean_ctor_set(x_58, 3, x_55);
lean_ctor_set(x_58, 4, x_56);
if (lean_is_scalar(x_52)) {
 x_59 = lean_alloc_ctor(0, 6, 0);
} else {
 x_59 = x_52;
}
lean_ctor_set(x_59, 0, x_47);
lean_ctor_set(x_59, 1, x_48);
lean_ctor_set(x_59, 2, x_58);
lean_ctor_set(x_59, 3, x_49);
lean_ctor_set(x_59, 4, x_50);
lean_ctor_set(x_59, 5, x_51);
x_60 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_42);
lean_ctor_set(x_60, 2, x_43);
lean_ctor_set(x_60, 3, x_44);
lean_ctor_set(x_60, 4, x_45);
lean_ctor_set(x_60, 5, x_46);
lean_ctor_set(x_9, 0, x_60);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_13);
lean_ctor_set(x_61, 1, x_9);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_62 = lean_ctor_get(x_9, 1);
lean_inc(x_62);
lean_dec(x_9);
x_63 = lean_ctor_get(x_10, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_10, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_10, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_10, 4);
lean_inc(x_66);
x_67 = lean_ctor_get(x_10, 5);
lean_inc(x_67);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 lean_ctor_release(x_10, 5);
 x_68 = x_10;
} else {
 lean_dec_ref(x_10);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_11, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_11, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_11, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_11, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_11, 5);
lean_inc(x_73);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_74 = x_11;
} else {
 lean_dec_ref(x_11);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_12, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_12, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_12, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_12, 4);
lean_inc(x_78);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_79 = x_12;
} else {
 lean_dec_ref(x_12);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 5, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_76);
lean_ctor_set(x_80, 2, x_7);
lean_ctor_set(x_80, 3, x_77);
lean_ctor_set(x_80, 4, x_78);
if (lean_is_scalar(x_74)) {
 x_81 = lean_alloc_ctor(0, 6, 0);
} else {
 x_81 = x_74;
}
lean_ctor_set(x_81, 0, x_69);
lean_ctor_set(x_81, 1, x_70);
lean_ctor_set(x_81, 2, x_80);
lean_ctor_set(x_81, 3, x_71);
lean_ctor_set(x_81, 4, x_72);
lean_ctor_set(x_81, 5, x_73);
if (lean_is_scalar(x_68)) {
 x_82 = lean_alloc_ctor(0, 6, 0);
} else {
 x_82 = x_68;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_63);
lean_ctor_set(x_82, 2, x_64);
lean_ctor_set(x_82, 3, x_65);
lean_ctor_set(x_82, 4, x_66);
lean_ctor_set(x_82, 5, x_67);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_62);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_13);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_9, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_8, 0);
lean_inc(x_88);
lean_dec(x_8);
x_89 = !lean_is_exclusive(x_9);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_9, 0);
lean_dec(x_90);
x_91 = !lean_is_exclusive(x_85);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_85, 0);
lean_dec(x_92);
x_93 = !lean_is_exclusive(x_86);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_86, 2);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_87);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_87, 2);
lean_dec(x_96);
lean_ctor_set(x_87, 2, x_7);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_88);
lean_ctor_set(x_97, 1, x_9);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_87, 0);
x_99 = lean_ctor_get(x_87, 1);
x_100 = lean_ctor_get(x_87, 3);
x_101 = lean_ctor_get(x_87, 4);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_87);
x_102 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_99);
lean_ctor_set(x_102, 2, x_7);
lean_ctor_set(x_102, 3, x_100);
lean_ctor_set(x_102, 4, x_101);
lean_ctor_set(x_86, 2, x_102);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_88);
lean_ctor_set(x_103, 1, x_9);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_104 = lean_ctor_get(x_86, 0);
x_105 = lean_ctor_get(x_86, 1);
x_106 = lean_ctor_get(x_86, 3);
x_107 = lean_ctor_get(x_86, 4);
x_108 = lean_ctor_get(x_86, 5);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_86);
x_109 = lean_ctor_get(x_87, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_87, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_87, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_87, 4);
lean_inc(x_112);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 lean_ctor_release(x_87, 3);
 lean_ctor_release(x_87, 4);
 x_113 = x_87;
} else {
 lean_dec_ref(x_87);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 5, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_109);
lean_ctor_set(x_114, 1, x_110);
lean_ctor_set(x_114, 2, x_7);
lean_ctor_set(x_114, 3, x_111);
lean_ctor_set(x_114, 4, x_112);
x_115 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_115, 0, x_104);
lean_ctor_set(x_115, 1, x_105);
lean_ctor_set(x_115, 2, x_114);
lean_ctor_set(x_115, 3, x_106);
lean_ctor_set(x_115, 4, x_107);
lean_ctor_set(x_115, 5, x_108);
lean_ctor_set(x_85, 0, x_115);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_88);
lean_ctor_set(x_116, 1, x_9);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_117 = lean_ctor_get(x_85, 1);
x_118 = lean_ctor_get(x_85, 2);
x_119 = lean_ctor_get(x_85, 3);
x_120 = lean_ctor_get(x_85, 4);
x_121 = lean_ctor_get(x_85, 5);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_85);
x_122 = lean_ctor_get(x_86, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_86, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_86, 3);
lean_inc(x_124);
x_125 = lean_ctor_get(x_86, 4);
lean_inc(x_125);
x_126 = lean_ctor_get(x_86, 5);
lean_inc(x_126);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 lean_ctor_release(x_86, 2);
 lean_ctor_release(x_86, 3);
 lean_ctor_release(x_86, 4);
 lean_ctor_release(x_86, 5);
 x_127 = x_86;
} else {
 lean_dec_ref(x_86);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_87, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_87, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_87, 3);
lean_inc(x_130);
x_131 = lean_ctor_get(x_87, 4);
lean_inc(x_131);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 lean_ctor_release(x_87, 3);
 lean_ctor_release(x_87, 4);
 x_132 = x_87;
} else {
 lean_dec_ref(x_87);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(0, 5, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_128);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set(x_133, 2, x_7);
lean_ctor_set(x_133, 3, x_130);
lean_ctor_set(x_133, 4, x_131);
if (lean_is_scalar(x_127)) {
 x_134 = lean_alloc_ctor(0, 6, 0);
} else {
 x_134 = x_127;
}
lean_ctor_set(x_134, 0, x_122);
lean_ctor_set(x_134, 1, x_123);
lean_ctor_set(x_134, 2, x_133);
lean_ctor_set(x_134, 3, x_124);
lean_ctor_set(x_134, 4, x_125);
lean_ctor_set(x_134, 5, x_126);
x_135 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_117);
lean_ctor_set(x_135, 2, x_118);
lean_ctor_set(x_135, 3, x_119);
lean_ctor_set(x_135, 4, x_120);
lean_ctor_set(x_135, 5, x_121);
lean_ctor_set(x_9, 0, x_135);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_88);
lean_ctor_set(x_136, 1, x_9);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_137 = lean_ctor_get(x_9, 1);
lean_inc(x_137);
lean_dec(x_9);
x_138 = lean_ctor_get(x_85, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_85, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_85, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_85, 4);
lean_inc(x_141);
x_142 = lean_ctor_get(x_85, 5);
lean_inc(x_142);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 lean_ctor_release(x_85, 2);
 lean_ctor_release(x_85, 3);
 lean_ctor_release(x_85, 4);
 lean_ctor_release(x_85, 5);
 x_143 = x_85;
} else {
 lean_dec_ref(x_85);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_86, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_86, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_86, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_86, 4);
lean_inc(x_147);
x_148 = lean_ctor_get(x_86, 5);
lean_inc(x_148);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 lean_ctor_release(x_86, 2);
 lean_ctor_release(x_86, 3);
 lean_ctor_release(x_86, 4);
 lean_ctor_release(x_86, 5);
 x_149 = x_86;
} else {
 lean_dec_ref(x_86);
 x_149 = lean_box(0);
}
x_150 = lean_ctor_get(x_87, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_87, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_87, 3);
lean_inc(x_152);
x_153 = lean_ctor_get(x_87, 4);
lean_inc(x_153);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 lean_ctor_release(x_87, 3);
 lean_ctor_release(x_87, 4);
 x_154 = x_87;
} else {
 lean_dec_ref(x_87);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(0, 5, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_150);
lean_ctor_set(x_155, 1, x_151);
lean_ctor_set(x_155, 2, x_7);
lean_ctor_set(x_155, 3, x_152);
lean_ctor_set(x_155, 4, x_153);
if (lean_is_scalar(x_149)) {
 x_156 = lean_alloc_ctor(0, 6, 0);
} else {
 x_156 = x_149;
}
lean_ctor_set(x_156, 0, x_144);
lean_ctor_set(x_156, 1, x_145);
lean_ctor_set(x_156, 2, x_155);
lean_ctor_set(x_156, 3, x_146);
lean_ctor_set(x_156, 4, x_147);
lean_ctor_set(x_156, 5, x_148);
if (lean_is_scalar(x_143)) {
 x_157 = lean_alloc_ctor(0, 6, 0);
} else {
 x_157 = x_143;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_138);
lean_ctor_set(x_157, 2, x_139);
lean_ctor_set(x_157, 3, x_140);
lean_ctor_set(x_157, 4, x_141);
lean_ctor_set(x_157, 5, x_142);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_137);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_88);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_resettingSynthInstanceCache___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_163; lean_object* x_164; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_163 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_3);
x_164 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_163, x_3, x_4);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = l_Lean_Elab_Tactic_save(x_165);
x_167 = lean_apply_2(x_2, x_3, x_165);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_166);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_168);
x_10 = x_170;
x_11 = x_169;
goto block_162;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_167, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_167, 1);
lean_inc(x_172);
lean_dec(x_167);
x_173 = l_Lean_Elab_Tactic_restore(x_172, x_166);
lean_dec(x_166);
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_171);
x_10 = x_174;
x_11 = x_173;
goto block_162;
}
}
else
{
uint8_t x_175; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_164);
if (x_175 == 0)
{
return x_164;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_164, 0);
x_177 = lean_ctor_get(x_164, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_164);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
block_162:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_13, 2);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_14, 2);
lean_dec(x_23);
lean_ctor_set(x_14, 2, x_9);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
x_27 = lean_ctor_get(x_14, 3);
x_28 = lean_ctor_get(x_14, 4);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_9);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set(x_13, 2, x_29);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_11);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
x_33 = lean_ctor_get(x_13, 3);
x_34 = lean_ctor_get(x_13, 4);
x_35 = lean_ctor_get(x_13, 5);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
x_36 = lean_ctor_get(x_14, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_14, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_14, 4);
lean_inc(x_39);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 x_40 = x_14;
} else {
 lean_dec_ref(x_14);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 5, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_9);
lean_ctor_set(x_41, 3, x_38);
lean_ctor_set(x_41, 4, x_39);
x_42 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_32);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_33);
lean_ctor_set(x_42, 4, x_34);
lean_ctor_set(x_42, 5, x_35);
lean_ctor_set(x_12, 0, x_42);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_15);
lean_ctor_set(x_43, 1, x_11);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_44 = lean_ctor_get(x_12, 1);
x_45 = lean_ctor_get(x_12, 2);
x_46 = lean_ctor_get(x_12, 3);
x_47 = lean_ctor_get(x_12, 4);
x_48 = lean_ctor_get(x_12, 5);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_12);
x_49 = lean_ctor_get(x_13, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_13, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_13, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_13, 4);
lean_inc(x_52);
x_53 = lean_ctor_get(x_13, 5);
lean_inc(x_53);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 x_54 = x_13;
} else {
 lean_dec_ref(x_13);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_14, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_14, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_14, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_14, 4);
lean_inc(x_58);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 x_59 = x_14;
} else {
 lean_dec_ref(x_14);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 5, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_56);
lean_ctor_set(x_60, 2, x_9);
lean_ctor_set(x_60, 3, x_57);
lean_ctor_set(x_60, 4, x_58);
if (lean_is_scalar(x_54)) {
 x_61 = lean_alloc_ctor(0, 6, 0);
} else {
 x_61 = x_54;
}
lean_ctor_set(x_61, 0, x_49);
lean_ctor_set(x_61, 1, x_50);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_51);
lean_ctor_set(x_61, 4, x_52);
lean_ctor_set(x_61, 5, x_53);
x_62 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_44);
lean_ctor_set(x_62, 2, x_45);
lean_ctor_set(x_62, 3, x_46);
lean_ctor_set(x_62, 4, x_47);
lean_ctor_set(x_62, 5, x_48);
lean_ctor_set(x_11, 0, x_62);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_15);
lean_ctor_set(x_63, 1, x_11);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_64 = lean_ctor_get(x_11, 1);
lean_inc(x_64);
lean_dec(x_11);
x_65 = lean_ctor_get(x_12, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_12, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_12, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_12, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_12, 5);
lean_inc(x_69);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 lean_ctor_release(x_12, 5);
 x_70 = x_12;
} else {
 lean_dec_ref(x_12);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_13, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_13, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_13, 3);
lean_inc(x_73);
x_74 = lean_ctor_get(x_13, 4);
lean_inc(x_74);
x_75 = lean_ctor_get(x_13, 5);
lean_inc(x_75);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 x_76 = x_13;
} else {
 lean_dec_ref(x_13);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_14, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_14, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_14, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_14, 4);
lean_inc(x_80);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 x_81 = x_14;
} else {
 lean_dec_ref(x_14);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 5, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_82, 1, x_78);
lean_ctor_set(x_82, 2, x_9);
lean_ctor_set(x_82, 3, x_79);
lean_ctor_set(x_82, 4, x_80);
if (lean_is_scalar(x_76)) {
 x_83 = lean_alloc_ctor(0, 6, 0);
} else {
 x_83 = x_76;
}
lean_ctor_set(x_83, 0, x_71);
lean_ctor_set(x_83, 1, x_72);
lean_ctor_set(x_83, 2, x_82);
lean_ctor_set(x_83, 3, x_73);
lean_ctor_set(x_83, 4, x_74);
lean_ctor_set(x_83, 5, x_75);
if (lean_is_scalar(x_70)) {
 x_84 = lean_alloc_ctor(0, 6, 0);
} else {
 x_84 = x_70;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_65);
lean_ctor_set(x_84, 2, x_66);
lean_ctor_set(x_84, 3, x_67);
lean_ctor_set(x_84, 4, x_68);
lean_ctor_set(x_84, 5, x_69);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_64);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_15);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_11, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_88, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_10, 0);
lean_inc(x_90);
lean_dec(x_10);
x_91 = !lean_is_exclusive(x_11);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_11, 0);
lean_dec(x_92);
x_93 = !lean_is_exclusive(x_87);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_87, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_88);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_88, 2);
lean_dec(x_96);
x_97 = !lean_is_exclusive(x_89);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_89, 2);
lean_dec(x_98);
lean_ctor_set(x_89, 2, x_9);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_90);
lean_ctor_set(x_99, 1, x_11);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_89, 0);
x_101 = lean_ctor_get(x_89, 1);
x_102 = lean_ctor_get(x_89, 3);
x_103 = lean_ctor_get(x_89, 4);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_89);
x_104 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_104, 0, x_100);
lean_ctor_set(x_104, 1, x_101);
lean_ctor_set(x_104, 2, x_9);
lean_ctor_set(x_104, 3, x_102);
lean_ctor_set(x_104, 4, x_103);
lean_ctor_set(x_88, 2, x_104);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_90);
lean_ctor_set(x_105, 1, x_11);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_106 = lean_ctor_get(x_88, 0);
x_107 = lean_ctor_get(x_88, 1);
x_108 = lean_ctor_get(x_88, 3);
x_109 = lean_ctor_get(x_88, 4);
x_110 = lean_ctor_get(x_88, 5);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_88);
x_111 = lean_ctor_get(x_89, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_89, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_89, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_89, 4);
lean_inc(x_114);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 lean_ctor_release(x_89, 4);
 x_115 = x_89;
} else {
 lean_dec_ref(x_89);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 5, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_112);
lean_ctor_set(x_116, 2, x_9);
lean_ctor_set(x_116, 3, x_113);
lean_ctor_set(x_116, 4, x_114);
x_117 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_117, 0, x_106);
lean_ctor_set(x_117, 1, x_107);
lean_ctor_set(x_117, 2, x_116);
lean_ctor_set(x_117, 3, x_108);
lean_ctor_set(x_117, 4, x_109);
lean_ctor_set(x_117, 5, x_110);
lean_ctor_set(x_87, 0, x_117);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_90);
lean_ctor_set(x_118, 1, x_11);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_119 = lean_ctor_get(x_87, 1);
x_120 = lean_ctor_get(x_87, 2);
x_121 = lean_ctor_get(x_87, 3);
x_122 = lean_ctor_get(x_87, 4);
x_123 = lean_ctor_get(x_87, 5);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_87);
x_124 = lean_ctor_get(x_88, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_88, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_88, 3);
lean_inc(x_126);
x_127 = lean_ctor_get(x_88, 4);
lean_inc(x_127);
x_128 = lean_ctor_get(x_88, 5);
lean_inc(x_128);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 lean_ctor_release(x_88, 4);
 lean_ctor_release(x_88, 5);
 x_129 = x_88;
} else {
 lean_dec_ref(x_88);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_89, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_89, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_89, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_89, 4);
lean_inc(x_133);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 lean_ctor_release(x_89, 4);
 x_134 = x_89;
} else {
 lean_dec_ref(x_89);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 5, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_130);
lean_ctor_set(x_135, 1, x_131);
lean_ctor_set(x_135, 2, x_9);
lean_ctor_set(x_135, 3, x_132);
lean_ctor_set(x_135, 4, x_133);
if (lean_is_scalar(x_129)) {
 x_136 = lean_alloc_ctor(0, 6, 0);
} else {
 x_136 = x_129;
}
lean_ctor_set(x_136, 0, x_124);
lean_ctor_set(x_136, 1, x_125);
lean_ctor_set(x_136, 2, x_135);
lean_ctor_set(x_136, 3, x_126);
lean_ctor_set(x_136, 4, x_127);
lean_ctor_set(x_136, 5, x_128);
x_137 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_119);
lean_ctor_set(x_137, 2, x_120);
lean_ctor_set(x_137, 3, x_121);
lean_ctor_set(x_137, 4, x_122);
lean_ctor_set(x_137, 5, x_123);
lean_ctor_set(x_11, 0, x_137);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_90);
lean_ctor_set(x_138, 1, x_11);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_139 = lean_ctor_get(x_11, 1);
lean_inc(x_139);
lean_dec(x_11);
x_140 = lean_ctor_get(x_87, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_87, 2);
lean_inc(x_141);
x_142 = lean_ctor_get(x_87, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_87, 4);
lean_inc(x_143);
x_144 = lean_ctor_get(x_87, 5);
lean_inc(x_144);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 lean_ctor_release(x_87, 3);
 lean_ctor_release(x_87, 4);
 lean_ctor_release(x_87, 5);
 x_145 = x_87;
} else {
 lean_dec_ref(x_87);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_88, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_88, 1);
lean_inc(x_147);
x_148 = lean_ctor_get(x_88, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_88, 4);
lean_inc(x_149);
x_150 = lean_ctor_get(x_88, 5);
lean_inc(x_150);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 lean_ctor_release(x_88, 4);
 lean_ctor_release(x_88, 5);
 x_151 = x_88;
} else {
 lean_dec_ref(x_88);
 x_151 = lean_box(0);
}
x_152 = lean_ctor_get(x_89, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_89, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_89, 3);
lean_inc(x_154);
x_155 = lean_ctor_get(x_89, 4);
lean_inc(x_155);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 lean_ctor_release(x_89, 4);
 x_156 = x_89;
} else {
 lean_dec_ref(x_89);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 5, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_152);
lean_ctor_set(x_157, 1, x_153);
lean_ctor_set(x_157, 2, x_9);
lean_ctor_set(x_157, 3, x_154);
lean_ctor_set(x_157, 4, x_155);
if (lean_is_scalar(x_151)) {
 x_158 = lean_alloc_ctor(0, 6, 0);
} else {
 x_158 = x_151;
}
lean_ctor_set(x_158, 0, x_146);
lean_ctor_set(x_158, 1, x_147);
lean_ctor_set(x_158, 2, x_157);
lean_ctor_set(x_158, 3, x_148);
lean_ctor_set(x_158, 4, x_149);
lean_ctor_set(x_158, 5, x_150);
if (lean_is_scalar(x_145)) {
 x_159 = lean_alloc_ctor(0, 6, 0);
} else {
 x_159 = x_145;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_140);
lean_ctor_set(x_159, 2, x_141);
lean_ctor_set(x_159, 3, x_142);
lean_ctor_set(x_159, 4, x_143);
lean_ctor_set(x_159, 5, x_144);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_139);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_90);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Elab_Tactic_withMVarContext___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = l_Lean_Elab_Tactic_getMVarDecl(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_10 = x_5;
} else {
 lean_dec_ref(x_5);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_6, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 2);
x_16 = lean_ctor_get(x_7, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 4);
lean_inc(x_18);
x_19 = lean_array_get_size(x_15);
x_20 = lean_array_get_size(x_18);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
lean_inc(x_18);
lean_ctor_set(x_7, 2, x_18);
lean_ctor_set(x_7, 1, x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_11);
if (x_21 == 0)
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
x_23 = lean_apply_2(x_2, x_22, x_9);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1(x_3, x_8, lean_box(0), x_15, x_18, x_24);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_3);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_10);
x_26 = lean_apply_2(x_2, x_22, x_9);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_184; lean_object* x_185; 
x_27 = lean_ctor_get(x_9, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 2);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
lean_dec(x_29);
x_184 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_22);
x_185 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_184, x_22, x_9);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_187 = l_Lean_Elab_Tactic_save(x_186);
x_188 = lean_apply_2(x_2, x_22, x_186);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_189);
x_31 = x_191;
x_32 = x_190;
goto block_183;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_188, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 1);
lean_inc(x_193);
lean_dec(x_188);
x_194 = l_Lean_Elab_Tactic_restore(x_193, x_187);
lean_dec(x_187);
x_195 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_195, 0, x_192);
x_31 = x_195;
x_32 = x_194;
goto block_183;
}
}
else
{
uint8_t x_196; 
lean_dec(x_30);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_2);
x_196 = !lean_is_exclusive(x_185);
if (x_196 == 0)
{
return x_185;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_185, 0);
x_198 = lean_ctor_get(x_185, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_185);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
block_183:
{
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_32, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_33, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_34, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_35, 2);
lean_dec(x_44);
lean_ctor_set(x_35, 2, x_30);
if (lean_is_scalar(x_10)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_10;
 lean_ctor_set_tag(x_45, 1);
}
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_32);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_35, 0);
x_47 = lean_ctor_get(x_35, 1);
x_48 = lean_ctor_get(x_35, 3);
x_49 = lean_ctor_get(x_35, 4);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_35);
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_47);
lean_ctor_set(x_50, 2, x_30);
lean_ctor_set(x_50, 3, x_48);
lean_ctor_set(x_50, 4, x_49);
lean_ctor_set(x_34, 2, x_50);
if (lean_is_scalar(x_10)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_10;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_36);
lean_ctor_set(x_51, 1, x_32);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_52 = lean_ctor_get(x_34, 0);
x_53 = lean_ctor_get(x_34, 1);
x_54 = lean_ctor_get(x_34, 3);
x_55 = lean_ctor_get(x_34, 4);
x_56 = lean_ctor_get(x_34, 5);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_34);
x_57 = lean_ctor_get(x_35, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_35, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_35, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_35, 4);
lean_inc(x_60);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 lean_ctor_release(x_35, 3);
 lean_ctor_release(x_35, 4);
 x_61 = x_35;
} else {
 lean_dec_ref(x_35);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 5, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_57);
lean_ctor_set(x_62, 1, x_58);
lean_ctor_set(x_62, 2, x_30);
lean_ctor_set(x_62, 3, x_59);
lean_ctor_set(x_62, 4, x_60);
x_63 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_63, 0, x_52);
lean_ctor_set(x_63, 1, x_53);
lean_ctor_set(x_63, 2, x_62);
lean_ctor_set(x_63, 3, x_54);
lean_ctor_set(x_63, 4, x_55);
lean_ctor_set(x_63, 5, x_56);
lean_ctor_set(x_33, 0, x_63);
if (lean_is_scalar(x_10)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_10;
 lean_ctor_set_tag(x_64, 1);
}
lean_ctor_set(x_64, 0, x_36);
lean_ctor_set(x_64, 1, x_32);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_65 = lean_ctor_get(x_33, 1);
x_66 = lean_ctor_get(x_33, 2);
x_67 = lean_ctor_get(x_33, 3);
x_68 = lean_ctor_get(x_33, 4);
x_69 = lean_ctor_get(x_33, 5);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_33);
x_70 = lean_ctor_get(x_34, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_34, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_34, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_34, 4);
lean_inc(x_73);
x_74 = lean_ctor_get(x_34, 5);
lean_inc(x_74);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 lean_ctor_release(x_34, 4);
 lean_ctor_release(x_34, 5);
 x_75 = x_34;
} else {
 lean_dec_ref(x_34);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_35, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_35, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_35, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_35, 4);
lean_inc(x_79);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 lean_ctor_release(x_35, 3);
 lean_ctor_release(x_35, 4);
 x_80 = x_35;
} else {
 lean_dec_ref(x_35);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 5, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_76);
lean_ctor_set(x_81, 1, x_77);
lean_ctor_set(x_81, 2, x_30);
lean_ctor_set(x_81, 3, x_78);
lean_ctor_set(x_81, 4, x_79);
if (lean_is_scalar(x_75)) {
 x_82 = lean_alloc_ctor(0, 6, 0);
} else {
 x_82 = x_75;
}
lean_ctor_set(x_82, 0, x_70);
lean_ctor_set(x_82, 1, x_71);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_72);
lean_ctor_set(x_82, 4, x_73);
lean_ctor_set(x_82, 5, x_74);
x_83 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_65);
lean_ctor_set(x_83, 2, x_66);
lean_ctor_set(x_83, 3, x_67);
lean_ctor_set(x_83, 4, x_68);
lean_ctor_set(x_83, 5, x_69);
lean_ctor_set(x_32, 0, x_83);
if (lean_is_scalar(x_10)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_10;
 lean_ctor_set_tag(x_84, 1);
}
lean_ctor_set(x_84, 0, x_36);
lean_ctor_set(x_84, 1, x_32);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_85 = lean_ctor_get(x_32, 1);
lean_inc(x_85);
lean_dec(x_32);
x_86 = lean_ctor_get(x_33, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_33, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_33, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_33, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_33, 5);
lean_inc(x_90);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 lean_ctor_release(x_33, 3);
 lean_ctor_release(x_33, 4);
 lean_ctor_release(x_33, 5);
 x_91 = x_33;
} else {
 lean_dec_ref(x_33);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_34, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_34, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_34, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_34, 4);
lean_inc(x_95);
x_96 = lean_ctor_get(x_34, 5);
lean_inc(x_96);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 lean_ctor_release(x_34, 4);
 lean_ctor_release(x_34, 5);
 x_97 = x_34;
} else {
 lean_dec_ref(x_34);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_35, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_35, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_35, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_35, 4);
lean_inc(x_101);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 lean_ctor_release(x_35, 3);
 lean_ctor_release(x_35, 4);
 x_102 = x_35;
} else {
 lean_dec_ref(x_35);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 5, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set(x_103, 2, x_30);
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
if (lean_is_scalar(x_91)) {
 x_105 = lean_alloc_ctor(0, 6, 0);
} else {
 x_105 = x_91;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_86);
lean_ctor_set(x_105, 2, x_87);
lean_ctor_set(x_105, 3, x_88);
lean_ctor_set(x_105, 4, x_89);
lean_ctor_set(x_105, 5, x_90);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_85);
if (lean_is_scalar(x_10)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_10;
 lean_ctor_set_tag(x_107, 1);
}
lean_ctor_set(x_107, 0, x_36);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_108 = lean_ctor_get(x_32, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_31, 0);
lean_inc(x_111);
lean_dec(x_31);
x_112 = !lean_is_exclusive(x_32);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_32, 0);
lean_dec(x_113);
x_114 = !lean_is_exclusive(x_108);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_108, 0);
lean_dec(x_115);
x_116 = !lean_is_exclusive(x_109);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_109, 2);
lean_dec(x_117);
x_118 = !lean_is_exclusive(x_110);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_110, 2);
lean_dec(x_119);
lean_ctor_set(x_110, 2, x_30);
if (lean_is_scalar(x_10)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_10;
}
lean_ctor_set(x_120, 0, x_111);
lean_ctor_set(x_120, 1, x_32);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_121 = lean_ctor_get(x_110, 0);
x_122 = lean_ctor_get(x_110, 1);
x_123 = lean_ctor_get(x_110, 3);
x_124 = lean_ctor_get(x_110, 4);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_110);
x_125 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_122);
lean_ctor_set(x_125, 2, x_30);
lean_ctor_set(x_125, 3, x_123);
lean_ctor_set(x_125, 4, x_124);
lean_ctor_set(x_109, 2, x_125);
if (lean_is_scalar(x_10)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_10;
}
lean_ctor_set(x_126, 0, x_111);
lean_ctor_set(x_126, 1, x_32);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_127 = lean_ctor_get(x_109, 0);
x_128 = lean_ctor_get(x_109, 1);
x_129 = lean_ctor_get(x_109, 3);
x_130 = lean_ctor_get(x_109, 4);
x_131 = lean_ctor_get(x_109, 5);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_109);
x_132 = lean_ctor_get(x_110, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_110, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_110, 3);
lean_inc(x_134);
x_135 = lean_ctor_get(x_110, 4);
lean_inc(x_135);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 lean_ctor_release(x_110, 3);
 lean_ctor_release(x_110, 4);
 x_136 = x_110;
} else {
 lean_dec_ref(x_110);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 5, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_133);
lean_ctor_set(x_137, 2, x_30);
lean_ctor_set(x_137, 3, x_134);
lean_ctor_set(x_137, 4, x_135);
x_138 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_138, 0, x_127);
lean_ctor_set(x_138, 1, x_128);
lean_ctor_set(x_138, 2, x_137);
lean_ctor_set(x_138, 3, x_129);
lean_ctor_set(x_138, 4, x_130);
lean_ctor_set(x_138, 5, x_131);
lean_ctor_set(x_108, 0, x_138);
if (lean_is_scalar(x_10)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_10;
}
lean_ctor_set(x_139, 0, x_111);
lean_ctor_set(x_139, 1, x_32);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_140 = lean_ctor_get(x_108, 1);
x_141 = lean_ctor_get(x_108, 2);
x_142 = lean_ctor_get(x_108, 3);
x_143 = lean_ctor_get(x_108, 4);
x_144 = lean_ctor_get(x_108, 5);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_108);
x_145 = lean_ctor_get(x_109, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_109, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_109, 3);
lean_inc(x_147);
x_148 = lean_ctor_get(x_109, 4);
lean_inc(x_148);
x_149 = lean_ctor_get(x_109, 5);
lean_inc(x_149);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 lean_ctor_release(x_109, 2);
 lean_ctor_release(x_109, 3);
 lean_ctor_release(x_109, 4);
 lean_ctor_release(x_109, 5);
 x_150 = x_109;
} else {
 lean_dec_ref(x_109);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_110, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_110, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_110, 3);
lean_inc(x_153);
x_154 = lean_ctor_get(x_110, 4);
lean_inc(x_154);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 lean_ctor_release(x_110, 3);
 lean_ctor_release(x_110, 4);
 x_155 = x_110;
} else {
 lean_dec_ref(x_110);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 5, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_151);
lean_ctor_set(x_156, 1, x_152);
lean_ctor_set(x_156, 2, x_30);
lean_ctor_set(x_156, 3, x_153);
lean_ctor_set(x_156, 4, x_154);
if (lean_is_scalar(x_150)) {
 x_157 = lean_alloc_ctor(0, 6, 0);
} else {
 x_157 = x_150;
}
lean_ctor_set(x_157, 0, x_145);
lean_ctor_set(x_157, 1, x_146);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_157, 3, x_147);
lean_ctor_set(x_157, 4, x_148);
lean_ctor_set(x_157, 5, x_149);
x_158 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_140);
lean_ctor_set(x_158, 2, x_141);
lean_ctor_set(x_158, 3, x_142);
lean_ctor_set(x_158, 4, x_143);
lean_ctor_set(x_158, 5, x_144);
lean_ctor_set(x_32, 0, x_158);
if (lean_is_scalar(x_10)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_10;
}
lean_ctor_set(x_159, 0, x_111);
lean_ctor_set(x_159, 1, x_32);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_160 = lean_ctor_get(x_32, 1);
lean_inc(x_160);
lean_dec(x_32);
x_161 = lean_ctor_get(x_108, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_108, 2);
lean_inc(x_162);
x_163 = lean_ctor_get(x_108, 3);
lean_inc(x_163);
x_164 = lean_ctor_get(x_108, 4);
lean_inc(x_164);
x_165 = lean_ctor_get(x_108, 5);
lean_inc(x_165);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 lean_ctor_release(x_108, 2);
 lean_ctor_release(x_108, 3);
 lean_ctor_release(x_108, 4);
 lean_ctor_release(x_108, 5);
 x_166 = x_108;
} else {
 lean_dec_ref(x_108);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_109, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_109, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_109, 3);
lean_inc(x_169);
x_170 = lean_ctor_get(x_109, 4);
lean_inc(x_170);
x_171 = lean_ctor_get(x_109, 5);
lean_inc(x_171);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 lean_ctor_release(x_109, 2);
 lean_ctor_release(x_109, 3);
 lean_ctor_release(x_109, 4);
 lean_ctor_release(x_109, 5);
 x_172 = x_109;
} else {
 lean_dec_ref(x_109);
 x_172 = lean_box(0);
}
x_173 = lean_ctor_get(x_110, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_110, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_110, 3);
lean_inc(x_175);
x_176 = lean_ctor_get(x_110, 4);
lean_inc(x_176);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 lean_ctor_release(x_110, 3);
 lean_ctor_release(x_110, 4);
 x_177 = x_110;
} else {
 lean_dec_ref(x_110);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(0, 5, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_173);
lean_ctor_set(x_178, 1, x_174);
lean_ctor_set(x_178, 2, x_30);
lean_ctor_set(x_178, 3, x_175);
lean_ctor_set(x_178, 4, x_176);
if (lean_is_scalar(x_172)) {
 x_179 = lean_alloc_ctor(0, 6, 0);
} else {
 x_179 = x_172;
}
lean_ctor_set(x_179, 0, x_167);
lean_ctor_set(x_179, 1, x_168);
lean_ctor_set(x_179, 2, x_178);
lean_ctor_set(x_179, 3, x_169);
lean_ctor_set(x_179, 4, x_170);
lean_ctor_set(x_179, 5, x_171);
if (lean_is_scalar(x_166)) {
 x_180 = lean_alloc_ctor(0, 6, 0);
} else {
 x_180 = x_166;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_161);
lean_ctor_set(x_180, 2, x_162);
lean_ctor_set(x_180, 3, x_163);
lean_ctor_set(x_180, 4, x_164);
lean_ctor_set(x_180, 5, x_165);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_160);
if (lean_is_scalar(x_10)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_10;
}
lean_ctor_set(x_182, 0, x_111);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
}
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; 
x_200 = lean_ctor_get(x_7, 0);
x_201 = lean_ctor_get(x_7, 2);
x_202 = lean_ctor_get(x_7, 3);
x_203 = lean_ctor_get(x_7, 4);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_7);
x_204 = lean_ctor_get(x_8, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_8, 4);
lean_inc(x_205);
x_206 = lean_array_get_size(x_201);
x_207 = lean_array_get_size(x_205);
x_208 = lean_nat_dec_eq(x_206, x_207);
lean_dec(x_207);
lean_dec(x_206);
lean_inc(x_205);
x_209 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_209, 0, x_200);
lean_ctor_set(x_209, 1, x_204);
lean_ctor_set(x_209, 2, x_205);
lean_ctor_set(x_209, 3, x_202);
lean_ctor_set(x_209, 4, x_203);
lean_ctor_set(x_6, 0, x_209);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_6);
lean_ctor_set(x_210, 1, x_11);
if (x_208 == 0)
{
lean_object* x_211; 
lean_dec(x_205);
lean_dec(x_201);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
x_211 = lean_apply_2(x_2, x_210, x_9);
return x_211;
}
else
{
lean_object* x_212; uint8_t x_213; 
x_212 = lean_unsigned_to_nat(0u);
x_213 = l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1(x_3, x_8, lean_box(0), x_201, x_205, x_212);
lean_dec(x_205);
lean_dec(x_201);
lean_dec(x_8);
lean_dec(x_3);
if (x_213 == 0)
{
lean_object* x_214; 
lean_dec(x_10);
x_214 = lean_apply_2(x_2, x_210, x_9);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_278; lean_object* x_279; 
x_215 = lean_ctor_get(x_9, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_ctor_get(x_216, 2);
lean_inc(x_217);
lean_dec(x_216);
x_218 = lean_ctor_get(x_217, 2);
lean_inc(x_218);
lean_dec(x_217);
x_278 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_210);
x_279 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_278, x_210, x_9);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec(x_279);
x_281 = l_Lean_Elab_Tactic_save(x_280);
x_282 = lean_apply_2(x_2, x_210, x_280);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_281);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_285, 0, x_283);
x_219 = x_285;
x_220 = x_284;
goto block_277;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_286 = lean_ctor_get(x_282, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_282, 1);
lean_inc(x_287);
lean_dec(x_282);
x_288 = l_Lean_Elab_Tactic_restore(x_287, x_281);
lean_dec(x_281);
x_289 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_289, 0, x_286);
x_219 = x_289;
x_220 = x_288;
goto block_277;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_218);
lean_dec(x_210);
lean_dec(x_10);
lean_dec(x_2);
x_290 = lean_ctor_get(x_279, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_279, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_292 = x_279;
} else {
 lean_dec_ref(x_279);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
block_277:
{
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_222, 2);
lean_inc(x_223);
x_224 = lean_ctor_get(x_219, 0);
lean_inc(x_224);
lean_dec(x_219);
x_225 = lean_ctor_get(x_220, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_226 = x_220;
} else {
 lean_dec_ref(x_220);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_221, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_221, 2);
lean_inc(x_228);
x_229 = lean_ctor_get(x_221, 3);
lean_inc(x_229);
x_230 = lean_ctor_get(x_221, 4);
lean_inc(x_230);
x_231 = lean_ctor_get(x_221, 5);
lean_inc(x_231);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 lean_ctor_release(x_221, 2);
 lean_ctor_release(x_221, 3);
 lean_ctor_release(x_221, 4);
 lean_ctor_release(x_221, 5);
 x_232 = x_221;
} else {
 lean_dec_ref(x_221);
 x_232 = lean_box(0);
}
x_233 = lean_ctor_get(x_222, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_222, 1);
lean_inc(x_234);
x_235 = lean_ctor_get(x_222, 3);
lean_inc(x_235);
x_236 = lean_ctor_get(x_222, 4);
lean_inc(x_236);
x_237 = lean_ctor_get(x_222, 5);
lean_inc(x_237);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 lean_ctor_release(x_222, 2);
 lean_ctor_release(x_222, 3);
 lean_ctor_release(x_222, 4);
 lean_ctor_release(x_222, 5);
 x_238 = x_222;
} else {
 lean_dec_ref(x_222);
 x_238 = lean_box(0);
}
x_239 = lean_ctor_get(x_223, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_223, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_223, 3);
lean_inc(x_241);
x_242 = lean_ctor_get(x_223, 4);
lean_inc(x_242);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 lean_ctor_release(x_223, 2);
 lean_ctor_release(x_223, 3);
 lean_ctor_release(x_223, 4);
 x_243 = x_223;
} else {
 lean_dec_ref(x_223);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(0, 5, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_239);
lean_ctor_set(x_244, 1, x_240);
lean_ctor_set(x_244, 2, x_218);
lean_ctor_set(x_244, 3, x_241);
lean_ctor_set(x_244, 4, x_242);
if (lean_is_scalar(x_238)) {
 x_245 = lean_alloc_ctor(0, 6, 0);
} else {
 x_245 = x_238;
}
lean_ctor_set(x_245, 0, x_233);
lean_ctor_set(x_245, 1, x_234);
lean_ctor_set(x_245, 2, x_244);
lean_ctor_set(x_245, 3, x_235);
lean_ctor_set(x_245, 4, x_236);
lean_ctor_set(x_245, 5, x_237);
if (lean_is_scalar(x_232)) {
 x_246 = lean_alloc_ctor(0, 6, 0);
} else {
 x_246 = x_232;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_227);
lean_ctor_set(x_246, 2, x_228);
lean_ctor_set(x_246, 3, x_229);
lean_ctor_set(x_246, 4, x_230);
lean_ctor_set(x_246, 5, x_231);
if (lean_is_scalar(x_226)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_226;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_225);
if (lean_is_scalar(x_10)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_10;
 lean_ctor_set_tag(x_248, 1);
}
lean_ctor_set(x_248, 0, x_224);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_249 = lean_ctor_get(x_220, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_250, 2);
lean_inc(x_251);
x_252 = lean_ctor_get(x_219, 0);
lean_inc(x_252);
lean_dec(x_219);
x_253 = lean_ctor_get(x_220, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_254 = x_220;
} else {
 lean_dec_ref(x_220);
 x_254 = lean_box(0);
}
x_255 = lean_ctor_get(x_249, 1);
lean_inc(x_255);
x_256 = lean_ctor_get(x_249, 2);
lean_inc(x_256);
x_257 = lean_ctor_get(x_249, 3);
lean_inc(x_257);
x_258 = lean_ctor_get(x_249, 4);
lean_inc(x_258);
x_259 = lean_ctor_get(x_249, 5);
lean_inc(x_259);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 lean_ctor_release(x_249, 2);
 lean_ctor_release(x_249, 3);
 lean_ctor_release(x_249, 4);
 lean_ctor_release(x_249, 5);
 x_260 = x_249;
} else {
 lean_dec_ref(x_249);
 x_260 = lean_box(0);
}
x_261 = lean_ctor_get(x_250, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_250, 1);
lean_inc(x_262);
x_263 = lean_ctor_get(x_250, 3);
lean_inc(x_263);
x_264 = lean_ctor_get(x_250, 4);
lean_inc(x_264);
x_265 = lean_ctor_get(x_250, 5);
lean_inc(x_265);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 lean_ctor_release(x_250, 2);
 lean_ctor_release(x_250, 3);
 lean_ctor_release(x_250, 4);
 lean_ctor_release(x_250, 5);
 x_266 = x_250;
} else {
 lean_dec_ref(x_250);
 x_266 = lean_box(0);
}
x_267 = lean_ctor_get(x_251, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_251, 1);
lean_inc(x_268);
x_269 = lean_ctor_get(x_251, 3);
lean_inc(x_269);
x_270 = lean_ctor_get(x_251, 4);
lean_inc(x_270);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 lean_ctor_release(x_251, 2);
 lean_ctor_release(x_251, 3);
 lean_ctor_release(x_251, 4);
 x_271 = x_251;
} else {
 lean_dec_ref(x_251);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(0, 5, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_267);
lean_ctor_set(x_272, 1, x_268);
lean_ctor_set(x_272, 2, x_218);
lean_ctor_set(x_272, 3, x_269);
lean_ctor_set(x_272, 4, x_270);
if (lean_is_scalar(x_266)) {
 x_273 = lean_alloc_ctor(0, 6, 0);
} else {
 x_273 = x_266;
}
lean_ctor_set(x_273, 0, x_261);
lean_ctor_set(x_273, 1, x_262);
lean_ctor_set(x_273, 2, x_272);
lean_ctor_set(x_273, 3, x_263);
lean_ctor_set(x_273, 4, x_264);
lean_ctor_set(x_273, 5, x_265);
if (lean_is_scalar(x_260)) {
 x_274 = lean_alloc_ctor(0, 6, 0);
} else {
 x_274 = x_260;
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_255);
lean_ctor_set(x_274, 2, x_256);
lean_ctor_set(x_274, 3, x_257);
lean_ctor_set(x_274, 4, x_258);
lean_ctor_set(x_274, 5, x_259);
if (lean_is_scalar(x_254)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_254;
}
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_253);
if (lean_is_scalar(x_10)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_10;
}
lean_ctor_set(x_276, 0, x_252);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
}
}
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; uint8_t x_303; uint8_t x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_294 = lean_ctor_get(x_6, 1);
x_295 = lean_ctor_get(x_6, 2);
x_296 = lean_ctor_get(x_6, 3);
x_297 = lean_ctor_get(x_6, 4);
x_298 = lean_ctor_get(x_6, 5);
x_299 = lean_ctor_get(x_6, 6);
x_300 = lean_ctor_get(x_6, 7);
x_301 = lean_ctor_get(x_6, 8);
x_302 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_303 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
x_304 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 2);
x_305 = lean_ctor_get(x_6, 9);
lean_inc(x_305);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_6);
x_306 = lean_ctor_get(x_7, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_7, 2);
lean_inc(x_307);
x_308 = lean_ctor_get(x_7, 3);
lean_inc(x_308);
x_309 = lean_ctor_get(x_7, 4);
lean_inc(x_309);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 x_310 = x_7;
} else {
 lean_dec_ref(x_7);
 x_310 = lean_box(0);
}
x_311 = lean_ctor_get(x_8, 1);
lean_inc(x_311);
x_312 = lean_ctor_get(x_8, 4);
lean_inc(x_312);
x_313 = lean_array_get_size(x_307);
x_314 = lean_array_get_size(x_312);
x_315 = lean_nat_dec_eq(x_313, x_314);
lean_dec(x_314);
lean_dec(x_313);
lean_inc(x_312);
if (lean_is_scalar(x_310)) {
 x_316 = lean_alloc_ctor(0, 5, 0);
} else {
 x_316 = x_310;
}
lean_ctor_set(x_316, 0, x_306);
lean_ctor_set(x_316, 1, x_311);
lean_ctor_set(x_316, 2, x_312);
lean_ctor_set(x_316, 3, x_308);
lean_ctor_set(x_316, 4, x_309);
x_317 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_294);
lean_ctor_set(x_317, 2, x_295);
lean_ctor_set(x_317, 3, x_296);
lean_ctor_set(x_317, 4, x_297);
lean_ctor_set(x_317, 5, x_298);
lean_ctor_set(x_317, 6, x_299);
lean_ctor_set(x_317, 7, x_300);
lean_ctor_set(x_317, 8, x_301);
lean_ctor_set(x_317, 9, x_305);
lean_ctor_set_uint8(x_317, sizeof(void*)*10, x_302);
lean_ctor_set_uint8(x_317, sizeof(void*)*10 + 1, x_303);
lean_ctor_set_uint8(x_317, sizeof(void*)*10 + 2, x_304);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_11);
if (x_315 == 0)
{
lean_object* x_319; 
lean_dec(x_312);
lean_dec(x_307);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
x_319 = lean_apply_2(x_2, x_318, x_9);
return x_319;
}
else
{
lean_object* x_320; uint8_t x_321; 
x_320 = lean_unsigned_to_nat(0u);
x_321 = l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1(x_3, x_8, lean_box(0), x_307, x_312, x_320);
lean_dec(x_312);
lean_dec(x_307);
lean_dec(x_8);
lean_dec(x_3);
if (x_321 == 0)
{
lean_object* x_322; 
lean_dec(x_10);
x_322 = lean_apply_2(x_2, x_318, x_9);
return x_322;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_386; lean_object* x_387; 
x_323 = lean_ctor_get(x_9, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
lean_dec(x_323);
x_325 = lean_ctor_get(x_324, 2);
lean_inc(x_325);
lean_dec(x_324);
x_326 = lean_ctor_get(x_325, 2);
lean_inc(x_326);
lean_dec(x_325);
x_386 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_318);
x_387 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_386, x_318, x_9);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
lean_dec(x_387);
x_389 = l_Lean_Elab_Tactic_save(x_388);
x_390 = lean_apply_2(x_2, x_318, x_388);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_389);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_393 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_393, 0, x_391);
x_327 = x_393;
x_328 = x_392;
goto block_385;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_394 = lean_ctor_get(x_390, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_390, 1);
lean_inc(x_395);
lean_dec(x_390);
x_396 = l_Lean_Elab_Tactic_restore(x_395, x_389);
lean_dec(x_389);
x_397 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_397, 0, x_394);
x_327 = x_397;
x_328 = x_396;
goto block_385;
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_326);
lean_dec(x_318);
lean_dec(x_10);
lean_dec(x_2);
x_398 = lean_ctor_get(x_387, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_387, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_400 = x_387;
} else {
 lean_dec_ref(x_387);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_398);
lean_ctor_set(x_401, 1, x_399);
return x_401;
}
block_385:
{
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_330, 2);
lean_inc(x_331);
x_332 = lean_ctor_get(x_327, 0);
lean_inc(x_332);
lean_dec(x_327);
x_333 = lean_ctor_get(x_328, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_334 = x_328;
} else {
 lean_dec_ref(x_328);
 x_334 = lean_box(0);
}
x_335 = lean_ctor_get(x_329, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_329, 2);
lean_inc(x_336);
x_337 = lean_ctor_get(x_329, 3);
lean_inc(x_337);
x_338 = lean_ctor_get(x_329, 4);
lean_inc(x_338);
x_339 = lean_ctor_get(x_329, 5);
lean_inc(x_339);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 lean_ctor_release(x_329, 2);
 lean_ctor_release(x_329, 3);
 lean_ctor_release(x_329, 4);
 lean_ctor_release(x_329, 5);
 x_340 = x_329;
} else {
 lean_dec_ref(x_329);
 x_340 = lean_box(0);
}
x_341 = lean_ctor_get(x_330, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_330, 1);
lean_inc(x_342);
x_343 = lean_ctor_get(x_330, 3);
lean_inc(x_343);
x_344 = lean_ctor_get(x_330, 4);
lean_inc(x_344);
x_345 = lean_ctor_get(x_330, 5);
lean_inc(x_345);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 lean_ctor_release(x_330, 4);
 lean_ctor_release(x_330, 5);
 x_346 = x_330;
} else {
 lean_dec_ref(x_330);
 x_346 = lean_box(0);
}
x_347 = lean_ctor_get(x_331, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_331, 1);
lean_inc(x_348);
x_349 = lean_ctor_get(x_331, 3);
lean_inc(x_349);
x_350 = lean_ctor_get(x_331, 4);
lean_inc(x_350);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 lean_ctor_release(x_331, 2);
 lean_ctor_release(x_331, 3);
 lean_ctor_release(x_331, 4);
 x_351 = x_331;
} else {
 lean_dec_ref(x_331);
 x_351 = lean_box(0);
}
if (lean_is_scalar(x_351)) {
 x_352 = lean_alloc_ctor(0, 5, 0);
} else {
 x_352 = x_351;
}
lean_ctor_set(x_352, 0, x_347);
lean_ctor_set(x_352, 1, x_348);
lean_ctor_set(x_352, 2, x_326);
lean_ctor_set(x_352, 3, x_349);
lean_ctor_set(x_352, 4, x_350);
if (lean_is_scalar(x_346)) {
 x_353 = lean_alloc_ctor(0, 6, 0);
} else {
 x_353 = x_346;
}
lean_ctor_set(x_353, 0, x_341);
lean_ctor_set(x_353, 1, x_342);
lean_ctor_set(x_353, 2, x_352);
lean_ctor_set(x_353, 3, x_343);
lean_ctor_set(x_353, 4, x_344);
lean_ctor_set(x_353, 5, x_345);
if (lean_is_scalar(x_340)) {
 x_354 = lean_alloc_ctor(0, 6, 0);
} else {
 x_354 = x_340;
}
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_335);
lean_ctor_set(x_354, 2, x_336);
lean_ctor_set(x_354, 3, x_337);
lean_ctor_set(x_354, 4, x_338);
lean_ctor_set(x_354, 5, x_339);
if (lean_is_scalar(x_334)) {
 x_355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_355 = x_334;
}
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_333);
if (lean_is_scalar(x_10)) {
 x_356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_356 = x_10;
 lean_ctor_set_tag(x_356, 1);
}
lean_ctor_set(x_356, 0, x_332);
lean_ctor_set(x_356, 1, x_355);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_357 = lean_ctor_get(x_328, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_358, 2);
lean_inc(x_359);
x_360 = lean_ctor_get(x_327, 0);
lean_inc(x_360);
lean_dec(x_327);
x_361 = lean_ctor_get(x_328, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_362 = x_328;
} else {
 lean_dec_ref(x_328);
 x_362 = lean_box(0);
}
x_363 = lean_ctor_get(x_357, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_357, 2);
lean_inc(x_364);
x_365 = lean_ctor_get(x_357, 3);
lean_inc(x_365);
x_366 = lean_ctor_get(x_357, 4);
lean_inc(x_366);
x_367 = lean_ctor_get(x_357, 5);
lean_inc(x_367);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 lean_ctor_release(x_357, 4);
 lean_ctor_release(x_357, 5);
 x_368 = x_357;
} else {
 lean_dec_ref(x_357);
 x_368 = lean_box(0);
}
x_369 = lean_ctor_get(x_358, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_358, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_358, 3);
lean_inc(x_371);
x_372 = lean_ctor_get(x_358, 4);
lean_inc(x_372);
x_373 = lean_ctor_get(x_358, 5);
lean_inc(x_373);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 lean_ctor_release(x_358, 2);
 lean_ctor_release(x_358, 3);
 lean_ctor_release(x_358, 4);
 lean_ctor_release(x_358, 5);
 x_374 = x_358;
} else {
 lean_dec_ref(x_358);
 x_374 = lean_box(0);
}
x_375 = lean_ctor_get(x_359, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_359, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_359, 3);
lean_inc(x_377);
x_378 = lean_ctor_get(x_359, 4);
lean_inc(x_378);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 lean_ctor_release(x_359, 2);
 lean_ctor_release(x_359, 3);
 lean_ctor_release(x_359, 4);
 x_379 = x_359;
} else {
 lean_dec_ref(x_359);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(0, 5, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_375);
lean_ctor_set(x_380, 1, x_376);
lean_ctor_set(x_380, 2, x_326);
lean_ctor_set(x_380, 3, x_377);
lean_ctor_set(x_380, 4, x_378);
if (lean_is_scalar(x_374)) {
 x_381 = lean_alloc_ctor(0, 6, 0);
} else {
 x_381 = x_374;
}
lean_ctor_set(x_381, 0, x_369);
lean_ctor_set(x_381, 1, x_370);
lean_ctor_set(x_381, 2, x_380);
lean_ctor_set(x_381, 3, x_371);
lean_ctor_set(x_381, 4, x_372);
lean_ctor_set(x_381, 5, x_373);
if (lean_is_scalar(x_368)) {
 x_382 = lean_alloc_ctor(0, 6, 0);
} else {
 x_382 = x_368;
}
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_363);
lean_ctor_set(x_382, 2, x_364);
lean_ctor_set(x_382, 3, x_365);
lean_ctor_set(x_382, 4, x_366);
lean_ctor_set(x_382, 5, x_367);
if (lean_is_scalar(x_362)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_362;
}
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_361);
if (lean_is_scalar(x_10)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_10;
}
lean_ctor_set(x_384, 0, x_360);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_withMVarContext(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMVarContext___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_Tactic_withMVarContext___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_getGoals___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_getGoals(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getGoals___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getGoals___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_getGoals(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_setGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Elab_Tactic_setGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_setGoals(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_appendGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_append___rarg(x_5, x_1);
lean_ctor_set(x_3, 1, x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = l_List_append___rarg(x_10, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* l_Lean_Elab_Tactic_appendGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_appendGoals(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_List_filterAuxM___main___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_inc(x_7);
x_9 = l_Lean_Elab_Tactic_isExprMVarAssigned(x_7, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_8;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_3 = x_12;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_14; 
lean_free_object(x_1);
lean_dec(x_7);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_1 = x_8;
x_4 = x_14;
goto _start;
}
}
else
{
uint8_t x_16; 
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_20);
x_22 = l_Lean_Elab_Tactic_isExprMVarAssigned(x_20, x_3, x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_2);
x_1 = x_21;
x_2 = x_26;
x_4 = x_25;
goto _start;
}
else
{
lean_object* x_28; 
lean_dec(x_20);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_1 = x_21;
x_4 = x_28;
goto _start;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_32 = x_22;
} else {
 lean_dec_ref(x_22);
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
}
}
lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Elab_Tactic_getGoals___rarg(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_box(0);
lean_inc(x_1);
x_7 = l_List_filterAuxM___main___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(x_4, x_6, x_1, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_List_reverse___rarg(x_8);
x_11 = l_Lean_Elab_Tactic_setGoals(x_10, x_1, x_9);
lean_dec(x_1);
return x_11;
}
else
{
uint8_t x_12; 
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
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_pruneSolvedGoals(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Elab_Tactic_getGoals___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_getMainGoal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no goals to be solved");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_getMainGoal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_getMainGoal___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_getMainGoal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_getMainGoal___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Elab_Tactic_getMainGoal___closed__3;
x_7 = l_Lean_Elab_Tactic_throwError___rarg(x_6, x_1, x_5);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
return x_3;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tactic failed, resulting expression contains metavariables");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_ensureHasNoMVars___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Tactic_instantiateMVars(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_Expr_hasMVar(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_2);
x_9 = lean_box(0);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_free_object(x_4);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_6);
x_11 = l_Lean_indentExpr(x_10);
x_12 = l_Lean_Elab_Tactic_ensureHasNoMVars___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Tactic_throwError___rarg(x_13, x_2, x_7);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = l_Lean_Expr_hasMVar(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_2);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_21 = l_Lean_indentExpr(x_20);
x_22 = l_Lean_Elab_Tactic_ensureHasNoMVars___closed__3;
x_23 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_Tactic_throwError___rarg(x_23, x_2, x_16);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
return x_4;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_withMainMVarContext___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_7, x_1, x_2, x_6);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_withMainMVarContext(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainMVarContext___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_7);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_7, x_9, x_2, x_6);
lean_dec(x_7);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaMAtMain___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_List_append___rarg(x_6, x_1);
x_8 = l_Lean_Elab_Tactic_setGoals(x_7, x_3, x_4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
lean_inc(x_7);
x_9 = lean_apply_1(x_1, x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_11, 0, x_8);
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_7, x_12, x_2, x_6);
lean_dec(x_7);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* _init_l_Lean_Elab_Tactic_liftMetaTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
lean_inc(x_7);
x_9 = lean_apply_1(x_1, x_7);
x_10 = l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_13, 0, x_8);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_7, x_14, x_2, x_6);
lean_dec(x_7);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_liftMetaTactic___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_done(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_List_isEmpty___rarg(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_free_object(x_3);
x_8 = l_Lean_Elab_Tactic_reportUnsolvedGoals(x_5, x_1, x_6);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_1);
x_9 = lean_box(0);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = l_List_isEmpty___rarg(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_reportUnsolvedGoals(x_10, x_1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
return x_3;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_focusAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Elab_Tactic_setGoals(x_10, x_2, x_6);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_2);
x_13 = lean_apply_2(x_1, x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Tactic_getGoals___rarg(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_List_append___rarg(x_17, x_8);
x_20 = l_Lean_Elab_Tactic_setGoals(x_19, x_2, x_18);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_14);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_4);
if (x_29 == 0)
{
return x_4;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_4);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_focusAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_focusAux___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_focus___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_done(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_focus___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_focus___rarg___lambda__1), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_focus___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Elab_Tactic_focus___rarg___closed__1;
x_5 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
x_6 = l_Lean_Elab_Tactic_focusAux___rarg(x_5, x_2, x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_focus(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_focus___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_7);
x_9 = l_Lean_MetavarContext_isAnonymousMVar(x_7, x_5);
if (x_9 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_4 = x_6;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_3, 0);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_2);
x_14 = l_Lean_Name_appendIndexAfter(x_2, x_8);
x_15 = l_Lean_Name_append___main(x_1, x_14);
x_16 = l_Lean_MetavarContext_renameMVar(x_7, x_5, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_8, x_17);
lean_dec(x_8);
lean_ctor_set(x_3, 1, x_18);
lean_ctor_set(x_3, 0, x_16);
x_4 = x_6;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
lean_inc(x_8);
lean_inc(x_2);
x_20 = l_Lean_Name_appendIndexAfter(x_2, x_8);
x_21 = l_Lean_Name_append___main(x_1, x_20);
x_22 = l_Lean_MetavarContext_renameMVar(x_7, x_5, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_8, x_23);
lean_dec(x_8);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_3 = x_25;
x_4 = x_6;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_Tactic_getMCtx___rarg(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_8 = x_6;
} else {
 lean_dec_ref(x_6);
 x_8 = lean_box(0);
}
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_81; 
x_81 = lean_box(0);
x_9 = x_81;
goto block_80;
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_3, 1);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_8);
lean_dec(x_2);
x_83 = lean_ctor_get(x_7, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_3, 0);
lean_inc(x_85);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_7);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_7, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_83);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_83, 0);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_84);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_inc(x_91);
x_92 = l_Lean_MetavarContext_isAnonymousMVar(x_91, x_85);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_85);
lean_dec(x_1);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_7);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = l_Lean_MetavarContext_renameMVar(x_91, x_85, x_1);
lean_ctor_set(x_84, 1, x_95);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_7);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_98 = lean_ctor_get(x_84, 0);
x_99 = lean_ctor_get(x_84, 1);
x_100 = lean_ctor_get(x_84, 2);
x_101 = lean_ctor_get(x_84, 3);
x_102 = lean_ctor_get(x_84, 4);
x_103 = lean_ctor_get(x_84, 5);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_84);
lean_inc(x_85);
lean_inc(x_99);
x_104 = l_Lean_MetavarContext_isAnonymousMVar(x_99, x_85);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_85);
lean_dec(x_1);
x_105 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_105, 0, x_98);
lean_ctor_set(x_105, 1, x_99);
lean_ctor_set(x_105, 2, x_100);
lean_ctor_set(x_105, 3, x_101);
lean_ctor_set(x_105, 4, x_102);
lean_ctor_set(x_105, 5, x_103);
lean_ctor_set(x_83, 0, x_105);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_7);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = l_Lean_MetavarContext_renameMVar(x_99, x_85, x_1);
x_109 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_109, 0, x_98);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_109, 2, x_100);
lean_ctor_set(x_109, 3, x_101);
lean_ctor_set(x_109, 4, x_102);
lean_ctor_set(x_109, 5, x_103);
lean_ctor_set(x_83, 0, x_109);
x_110 = lean_box(0);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_7);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_112 = lean_ctor_get(x_83, 1);
x_113 = lean_ctor_get(x_83, 2);
x_114 = lean_ctor_get(x_83, 3);
x_115 = lean_ctor_get(x_83, 4);
x_116 = lean_ctor_get(x_83, 5);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_83);
x_117 = lean_ctor_get(x_84, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_84, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_84, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_84, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_84, 4);
lean_inc(x_121);
x_122 = lean_ctor_get(x_84, 5);
lean_inc(x_122);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 lean_ctor_release(x_84, 2);
 lean_ctor_release(x_84, 3);
 lean_ctor_release(x_84, 4);
 lean_ctor_release(x_84, 5);
 x_123 = x_84;
} else {
 lean_dec_ref(x_84);
 x_123 = lean_box(0);
}
lean_inc(x_85);
lean_inc(x_118);
x_124 = l_Lean_MetavarContext_isAnonymousMVar(x_118, x_85);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_85);
lean_dec(x_1);
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(0, 6, 0);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_117);
lean_ctor_set(x_125, 1, x_118);
lean_ctor_set(x_125, 2, x_119);
lean_ctor_set(x_125, 3, x_120);
lean_ctor_set(x_125, 4, x_121);
lean_ctor_set(x_125, 5, x_122);
x_126 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_112);
lean_ctor_set(x_126, 2, x_113);
lean_ctor_set(x_126, 3, x_114);
lean_ctor_set(x_126, 4, x_115);
lean_ctor_set(x_126, 5, x_116);
lean_ctor_set(x_7, 0, x_126);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_7);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = l_Lean_MetavarContext_renameMVar(x_118, x_85, x_1);
if (lean_is_scalar(x_123)) {
 x_130 = lean_alloc_ctor(0, 6, 0);
} else {
 x_130 = x_123;
}
lean_ctor_set(x_130, 0, x_117);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_130, 2, x_119);
lean_ctor_set(x_130, 3, x_120);
lean_ctor_set(x_130, 4, x_121);
lean_ctor_set(x_130, 5, x_122);
x_131 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_112);
lean_ctor_set(x_131, 2, x_113);
lean_ctor_set(x_131, 3, x_114);
lean_ctor_set(x_131, 4, x_115);
lean_ctor_set(x_131, 5, x_116);
lean_ctor_set(x_7, 0, x_131);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_7);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_134 = lean_ctor_get(x_7, 1);
lean_inc(x_134);
lean_dec(x_7);
x_135 = lean_ctor_get(x_83, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_83, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_83, 3);
lean_inc(x_137);
x_138 = lean_ctor_get(x_83, 4);
lean_inc(x_138);
x_139 = lean_ctor_get(x_83, 5);
lean_inc(x_139);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 lean_ctor_release(x_83, 2);
 lean_ctor_release(x_83, 3);
 lean_ctor_release(x_83, 4);
 lean_ctor_release(x_83, 5);
 x_140 = x_83;
} else {
 lean_dec_ref(x_83);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get(x_84, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_84, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_84, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_84, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_84, 4);
lean_inc(x_145);
x_146 = lean_ctor_get(x_84, 5);
lean_inc(x_146);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 lean_ctor_release(x_84, 2);
 lean_ctor_release(x_84, 3);
 lean_ctor_release(x_84, 4);
 lean_ctor_release(x_84, 5);
 x_147 = x_84;
} else {
 lean_dec_ref(x_84);
 x_147 = lean_box(0);
}
lean_inc(x_85);
lean_inc(x_142);
x_148 = l_Lean_MetavarContext_isAnonymousMVar(x_142, x_85);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_85);
lean_dec(x_1);
if (lean_is_scalar(x_147)) {
 x_149 = lean_alloc_ctor(0, 6, 0);
} else {
 x_149 = x_147;
}
lean_ctor_set(x_149, 0, x_141);
lean_ctor_set(x_149, 1, x_142);
lean_ctor_set(x_149, 2, x_143);
lean_ctor_set(x_149, 3, x_144);
lean_ctor_set(x_149, 4, x_145);
lean_ctor_set(x_149, 5, x_146);
if (lean_is_scalar(x_140)) {
 x_150 = lean_alloc_ctor(0, 6, 0);
} else {
 x_150 = x_140;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_135);
lean_ctor_set(x_150, 2, x_136);
lean_ctor_set(x_150, 3, x_137);
lean_ctor_set(x_150, 4, x_138);
lean_ctor_set(x_150, 5, x_139);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_134);
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_154 = l_Lean_MetavarContext_renameMVar(x_142, x_85, x_1);
if (lean_is_scalar(x_147)) {
 x_155 = lean_alloc_ctor(0, 6, 0);
} else {
 x_155 = x_147;
}
lean_ctor_set(x_155, 0, x_141);
lean_ctor_set(x_155, 1, x_154);
lean_ctor_set(x_155, 2, x_143);
lean_ctor_set(x_155, 3, x_144);
lean_ctor_set(x_155, 4, x_145);
lean_ctor_set(x_155, 5, x_146);
if (lean_is_scalar(x_140)) {
 x_156 = lean_alloc_ctor(0, 6, 0);
} else {
 x_156 = x_140;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_135);
lean_ctor_set(x_156, 2, x_136);
lean_ctor_set(x_156, 3, x_137);
lean_ctor_set(x_156, 4, x_138);
lean_ctor_set(x_156, 5, x_139);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_134);
x_158 = lean_box(0);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
}
else
{
lean_object* x_160; 
lean_dec(x_82);
x_160 = lean_box(0);
x_9 = x_160;
goto block_80;
}
}
block_80:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_9);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_11, 1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(x_1, x_2, x_19, x_3);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
lean_ctor_set(x_11, 1, x_21);
x_22 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_8;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
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
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(x_1, x_2, x_31, x_3);
lean_dec(x_1);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_26);
lean_ctor_set(x_34, 3, x_27);
lean_ctor_set(x_34, 4, x_28);
lean_ctor_set(x_34, 5, x_29);
lean_ctor_set(x_10, 0, x_34);
x_35 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_8;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_7);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_37 = lean_ctor_get(x_10, 1);
x_38 = lean_ctor_get(x_10, 2);
x_39 = lean_ctor_get(x_10, 3);
x_40 = lean_ctor_get(x_10, 4);
x_41 = lean_ctor_get(x_10, 5);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_10);
x_42 = lean_ctor_get(x_11, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_11, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_11, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_11, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_11, 5);
lean_inc(x_47);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_48 = x_11;
} else {
 lean_dec_ref(x_11);
 x_48 = lean_box(0);
}
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(x_1, x_2, x_50, x_3);
lean_dec(x_1);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(0, 6, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_42);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_44);
lean_ctor_set(x_53, 3, x_45);
lean_ctor_set(x_53, 4, x_46);
lean_ctor_set(x_53, 5, x_47);
x_54 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_37);
lean_ctor_set(x_54, 2, x_38);
lean_ctor_set(x_54, 3, x_39);
lean_ctor_set(x_54, 4, x_40);
lean_ctor_set(x_54, 5, x_41);
lean_ctor_set(x_7, 0, x_54);
x_55 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_8;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_7);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_57 = lean_ctor_get(x_7, 1);
lean_inc(x_57);
lean_dec(x_7);
x_58 = lean_ctor_get(x_10, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_10, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_10, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_10, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_10, 5);
lean_inc(x_62);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 lean_ctor_release(x_10, 5);
 x_63 = x_10;
} else {
 lean_dec_ref(x_10);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_11, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_11, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_11, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_11, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_11, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_11, 5);
lean_inc(x_69);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_70 = x_11;
} else {
 lean_dec_ref(x_11);
 x_70 = lean_box(0);
}
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_65);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(x_1, x_2, x_72, x_3);
lean_dec(x_1);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
if (lean_is_scalar(x_70)) {
 x_75 = lean_alloc_ctor(0, 6, 0);
} else {
 x_75 = x_70;
}
lean_ctor_set(x_75, 0, x_64);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_75, 2, x_66);
lean_ctor_set(x_75, 3, x_67);
lean_ctor_set(x_75, 4, x_68);
lean_ctor_set(x_75, 5, x_69);
if (lean_is_scalar(x_63)) {
 x_76 = lean_alloc_ctor(0, 6, 0);
} else {
 x_76 = x_63;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_58);
lean_ctor_set(x_76, 2, x_59);
lean_ctor_set(x_76, 3, x_60);
lean_ctor_set(x_76, 4, x_61);
lean_ctor_set(x_76, 5, x_62);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_57);
x_78 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_8;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Tactic_tagUntaggedGoals(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_evalSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_box(0);
x_9 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_7, x_6, x_4, x_8, x_2, x_3);
lean_dec(x_6);
return x_9;
}
}
lean_object* l_Lean_Elab_Tactic_evalSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalSeq(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSeq___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSeq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSeq___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalChoiceAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_fget(x_1, x_2);
x_9 = l_Lean_Elab_Tactic_save(x_4);
lean_inc(x_3);
x_10 = l_Lean_Elab_Tactic_evalTactic___main(x_8, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_Elab_Tactic_restore(x_13, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_10, 1, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_2 = x_16;
x_4 = x_14;
goto _start;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = l_Lean_Elab_Tactic_restore(x_19, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
lean_dec(x_2);
x_2 = x_23;
x_4 = x_20;
goto _start;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalChoiceAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_evalChoiceAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalChoiceAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_evalChoiceAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalChoiceAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_evalChoiceAux(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Syntax_getArgs(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Elab_Tactic_evalChoiceAux___main(x_4, x_5, x_2, x_3);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_evalChoice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalChoice(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalChoice___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalChoice(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_choiceKind___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalSkip___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_Tactic_evalSkip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSkip___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_evalSkip___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_evalSkip(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSkip___boxed), 2, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSkip(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_skip___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalFailIfSuccess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tactic succeeded");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalFailIfSuccess___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalFailIfSuccess___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalFailIfSuccess___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalFailIfSuccess___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Elab_Tactic_save(x_3);
lean_inc(x_2);
x_7 = l_Lean_Elab_Tactic_evalTactic___main(x_5, x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Elab_Tactic_evalFailIfSuccess___closed__3;
x_10 = l_Lean_Elab_Tactic_throwError___rarg(x_9, x_2, x_8);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
x_14 = l_Lean_Elab_Tactic_restore(x_12, x_6);
lean_dec(x_6);
x_15 = lean_box(0);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 1, x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = l_Lean_Elab_Tactic_restore(x_16, x_6);
lean_dec(x_6);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalFailIfSuccess(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalFailIfSuccess___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_failIfSuccess___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Tactic_evalTraceState___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 9);
x_5 = l_Lean_Syntax_getPos(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
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
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
}
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Tactic_evalTraceState___spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_FileMap_toPosition(x_7, x_3);
lean_dec(x_7);
x_10 = l_Lean_Elab_Tactic_addContext(x_1, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_box(0);
x_14 = l_String_splitAux___main___closed__1;
x_15 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_15, 0, x_8);
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
x_20 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_20, 0, x_8);
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
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalTraceState___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Tactic_evalTraceState___spec__4(x_3, x_2, x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 2);
x_16 = l_Std_PersistentArray_push___rarg(x_15, x_10);
lean_ctor_set(x_8, 2, x_16);
x_17 = lean_box(0);
lean_ctor_set(x_6, 0, x_17);
return x_6;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 3);
x_22 = lean_ctor_get(x_8, 4);
x_23 = lean_ctor_get(x_8, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_24 = l_Std_PersistentArray_push___rarg(x_20, x_10);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_21);
lean_ctor_set(x_25, 4, x_22);
lean_ctor_set(x_25, 5, x_23);
lean_ctor_set(x_7, 0, x_25);
x_26 = lean_box(0);
lean_ctor_set(x_6, 0, x_26);
return x_6;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_dec(x_7);
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_8, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_8, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_8, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_8, 5);
lean_inc(x_33);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 lean_ctor_release(x_8, 4);
 lean_ctor_release(x_8, 5);
 x_34 = x_8;
} else {
 lean_dec_ref(x_8);
 x_34 = lean_box(0);
}
x_35 = l_Std_PersistentArray_push___rarg(x_30, x_10);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 6, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_32);
lean_ctor_set(x_36, 5, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
x_38 = lean_box(0);
lean_ctor_set(x_6, 1, x_37);
lean_ctor_set(x_6, 0, x_38);
return x_6;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
lean_dec(x_6);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_41 = x_7;
} else {
 lean_dec_ref(x_7);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_8, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_8, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_8, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_8, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_8, 4);
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
x_49 = l_Std_PersistentArray_push___rarg(x_44, x_39);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 6, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_42);
lean_ctor_set(x_50, 1, x_43);
lean_ctor_set(x_50, 2, x_49);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_46);
lean_ctor_set(x_50, 5, x_47);
if (lean_is_scalar(x_41)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_41;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_40);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_6);
if (x_54 == 0)
{
return x_6;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_6, 0);
x_56 = lean_ctor_get(x_6, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_6);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTraceState___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Elab_getRefPos___at_Lean_Elab_Tactic_evalTraceState___spec__2(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalTraceState___spec__3(x_6, x_1, x_2, x_3, x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_Tactic_evalTraceState___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Elab_goalsToMessageData(x_4);
x_7 = 0;
x_8 = l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTraceState___spec__1(x_7, x_6, x_1, x_5);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalTraceState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTraceState___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_getRefPos___at_Lean_Elab_Tactic_evalTraceState___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_getRefPos___at_Lean_Elab_Tactic_evalTraceState___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Tactic_evalTraceState___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Tactic_evalTraceState___spec__4(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalTraceState___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalTraceState___spec__3(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTraceState___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTraceState___spec__1(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_evalTraceState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalTraceState(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTraceState___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTraceState(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalAssumption___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalAssumption___rarg___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_assumption___boxed), 3, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = l_Lean_Elab_Tactic_evalAssumption___rarg___closed__1;
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_14, 0, x_7);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_6, x_15, x_1, x_5);
lean_dec(x_6);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_1);
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
lean_object* l_Lean_Elab_Tactic_evalAssumption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalAssumption___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalAssumption___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_evalAssumption___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalAssumption(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalAssumption___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAssumption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Syntax_getId(x_1);
x_6 = l_Lean_Meta_intro(x_2, x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
return x_6;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = l_Lean_Meta_intro1(x_1, x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
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
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalIntro(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_57; uint8_t x_58; 
x_57 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
lean_inc(x_1);
x_58 = l_Lean_Syntax_isOfKind(x_1, x_57);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = 0;
x_4 = x_59;
goto block_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = l_Lean_Syntax_getArgs(x_1);
x_61 = lean_array_get_size(x_60);
lean_dec(x_60);
x_62 = lean_unsigned_to_nat(2u);
x_63 = lean_nat_dec_eq(x_61, x_62);
lean_dec(x_61);
x_4 = x_63;
goto block_56;
}
block_56:
{
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
lean_dec(x_1);
x_8 = l_Lean_nullKind___closed__2;
lean_inc(x_7);
x_9 = l_Lean_Syntax_isOfKind(x_7, x_8);
if (x_9 == 0)
{
uint8_t x_51; 
x_51 = 0;
x_10 = x_51;
goto block_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = l_Lean_Syntax_getArgs(x_7);
x_53 = lean_array_get_size(x_52);
lean_dec(x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_nat_dec_eq(x_53, x_54);
lean_dec(x_53);
x_10 = x_55;
goto block_50;
}
block_50:
{
if (x_10 == 0)
{
if (x_9 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
x_11 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Syntax_getArgs(x_7);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
x_14 = lean_nat_dec_eq(x_13, x_6);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_7);
x_15 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_7, x_16);
lean_dec(x_7);
lean_inc(x_2);
x_18 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
lean_inc(x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntro___lambda__1___boxed), 4, 2);
lean_closure_set(x_23, 0, x_17);
lean_closure_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
x_25 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_27, 0, x_22);
x_28 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_21, x_28, x_2, x_20);
lean_dec(x_21);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_7);
lean_inc(x_2);
x_34 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
lean_inc(x_37);
x_39 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntro___lambda__2___boxed), 3, 1);
lean_closure_set(x_39, 0, x_37);
x_40 = l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
x_41 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_41, 0, x_39);
lean_closure_set(x_41, 1, x_40);
x_42 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_43, 0, x_38);
x_44 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_44, 0, x_42);
lean_closure_set(x_44, 1, x_43);
x_45 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_37, x_44, x_2, x_36);
lean_dec(x_37);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_34);
if (x_46 == 0)
{
return x_34;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_34, 0);
x_48 = lean_ctor_get(x_34, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_34);
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
}
}
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_evalIntro___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalIntro___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntro), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntro(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_3__getIntrosSize___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l___private_Lean_Elab_Tactic_Basic_3__getIntrosSize___main(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
return x_5;
}
case 8:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 3);
x_7 = l___private_Lean_Elab_Tactic_Basic_3__getIntrosSize___main(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
return x_9;
}
default: 
{
lean_object* x_10; 
x_10 = lean_unsigned_to_nat(0u);
return x_10;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_3__getIntrosSize___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Basic_3__getIntrosSize___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_3__getIntrosSize(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Basic_3__getIntrosSize___main(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_3__getIntrosSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Basic_3__getIntrosSize(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalIntros___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = l_Lean_Syntax_getId(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = x_10;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_5 = lean_array_get_size(x_1);
x_6 = x_1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalIntros___spec__1(x_7, x_6);
x_9 = x_8;
x_10 = l_Array_toList___rarg(x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = l_Lean_Meta_introN(x_2, x_5, x_10, x_11, x_3, x_4);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l_Lean_Meta_getMVarType(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Meta_instantiateMVars(x_5, x_2, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l___private_Lean_Elab_Tactic_Basic_3__getIntrosSize___main(x_8);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = 1;
x_13 = l_Lean_Meta_introN(x_1, x_10, x_11, x_12, x_2, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
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
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_11);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
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
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_4);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalIntros(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_51; uint8_t x_52; 
x_51 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
lean_inc(x_1);
x_52 = l_Lean_Syntax_isOfKind(x_1, x_51);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = 0;
x_4 = x_53;
goto block_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = l_Lean_Syntax_getArgs(x_1);
x_55 = lean_array_get_size(x_54);
lean_dec(x_54);
x_56 = lean_unsigned_to_nat(2u);
x_57 = lean_nat_dec_eq(x_55, x_56);
lean_dec(x_55);
x_4 = x_57;
goto block_50;
}
block_50:
{
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_43; uint8_t x_44; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
lean_dec(x_1);
x_43 = l_Lean_nullKind___closed__2;
lean_inc(x_7);
x_44 = l_Lean_Syntax_isOfKind(x_7, x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = 0;
x_8 = x_45;
goto block_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = l_Lean_Syntax_getArgs(x_7);
x_47 = lean_array_get_size(x_46);
lean_dec(x_46);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_eq(x_47, x_48);
lean_dec(x_47);
x_8 = x_49;
goto block_42;
}
block_42:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Syntax_getArgs(x_7);
lean_dec(x_7);
lean_inc(x_2);
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntros___lambda__1___boxed), 4, 2);
lean_closure_set(x_15, 0, x_9);
lean_closure_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
x_17 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_19, 0, x_14);
x_20 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_13, x_20, x_2, x_12);
lean_dec(x_13);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
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
lean_dec(x_7);
lean_inc(x_2);
x_26 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
lean_inc(x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntros___lambda__2___boxed), 3, 1);
lean_closure_set(x_31, 0, x_29);
x_32 = l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
x_33 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_33, 0, x_31);
lean_closure_set(x_33, 1, x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 3, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_35, 0, x_30);
x_36 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_36, 0, x_34);
lean_closure_set(x_36, 1, x_35);
x_37 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_29, x_36, x_2, x_28);
lean_dec(x_29);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
return x_26;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_26, 0);
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_26);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_evalIntros___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalIntros___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntros), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntros(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_isLocalIdent_x3f___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 9);
x_9 = l_Lean_Elab_replaceRef(x_1, x_8);
lean_dec(x_8);
lean_ctor_set(x_6, 9, x_9);
lean_inc(x_2);
x_10 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_4, x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_14 = l_Lean_Name_toString___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_13);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Meta_clear___lambda__1___closed__6;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Core_getConstInfo___closed__5;
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Elab_Tactic_throwError___rarg(x_21, x_2, x_12);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_11, 0);
lean_inc(x_25);
lean_dec(x_11);
x_26 = l_Lean_Expr_fvarId_x21(x_25);
lean_dec(x_25);
lean_ctor_set(x_10, 0, x_26);
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_dec(x_10);
x_28 = lean_ctor_get(x_11, 0);
lean_inc(x_28);
lean_dec(x_11);
x_29 = l_Lean_Expr_fvarId_x21(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
return x_10;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_10, 0);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_10);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_35 = lean_ctor_get(x_6, 0);
x_36 = lean_ctor_get(x_6, 1);
x_37 = lean_ctor_get(x_6, 2);
x_38 = lean_ctor_get(x_6, 3);
x_39 = lean_ctor_get(x_6, 4);
x_40 = lean_ctor_get(x_6, 5);
x_41 = lean_ctor_get(x_6, 6);
x_42 = lean_ctor_get(x_6, 7);
x_43 = lean_ctor_get(x_6, 8);
x_44 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_45 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
x_46 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 2);
x_47 = lean_ctor_get(x_6, 9);
lean_inc(x_47);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_6);
x_48 = l_Lean_Elab_replaceRef(x_1, x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_49, 0, x_35);
lean_ctor_set(x_49, 1, x_36);
lean_ctor_set(x_49, 2, x_37);
lean_ctor_set(x_49, 3, x_38);
lean_ctor_set(x_49, 4, x_39);
lean_ctor_set(x_49, 5, x_40);
lean_ctor_set(x_49, 6, x_41);
lean_ctor_set(x_49, 7, x_42);
lean_ctor_set(x_49, 8, x_43);
lean_ctor_set(x_49, 9, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*10, x_44);
lean_ctor_set_uint8(x_49, sizeof(void*)*10 + 1, x_45);
lean_ctor_set_uint8(x_49, sizeof(void*)*10 + 2, x_46);
lean_ctor_set(x_2, 0, x_49);
lean_inc(x_2);
x_50 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_4, x_2, x_3);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_54 = l_Lean_Name_toString___closed__1;
x_55 = l_Lean_Name_toStringWithSep___main(x_54, x_53);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Lean_Meta_clear___lambda__1___closed__6;
x_59 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Lean_Core_getConstInfo___closed__5;
x_61 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_Elab_Tactic_throwError___rarg(x_61, x_2, x_52);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_ctor_get(x_50, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_64 = x_50;
} else {
 lean_dec_ref(x_50);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_51, 0);
lean_inc(x_65);
lean_dec(x_51);
x_66 = l_Lean_Expr_fvarId_x21(x_65);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_ctor_get(x_50, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_50, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_70 = x_50;
} else {
 lean_dec_ref(x_50);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_72 = lean_ctor_get(x_2, 0);
x_73 = lean_ctor_get(x_2, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_2);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_72, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 5);
lean_inc(x_79);
x_80 = lean_ctor_get(x_72, 6);
lean_inc(x_80);
x_81 = lean_ctor_get(x_72, 7);
lean_inc(x_81);
x_82 = lean_ctor_get(x_72, 8);
lean_inc(x_82);
x_83 = lean_ctor_get_uint8(x_72, sizeof(void*)*10);
x_84 = lean_ctor_get_uint8(x_72, sizeof(void*)*10 + 1);
x_85 = lean_ctor_get_uint8(x_72, sizeof(void*)*10 + 2);
x_86 = lean_ctor_get(x_72, 9);
lean_inc(x_86);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 lean_ctor_release(x_72, 5);
 lean_ctor_release(x_72, 6);
 lean_ctor_release(x_72, 7);
 lean_ctor_release(x_72, 8);
 lean_ctor_release(x_72, 9);
 x_87 = x_72;
} else {
 lean_dec_ref(x_72);
 x_87 = lean_box(0);
}
x_88 = l_Lean_Elab_replaceRef(x_1, x_86);
lean_dec(x_86);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 10, 3);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_74);
lean_ctor_set(x_89, 1, x_75);
lean_ctor_set(x_89, 2, x_76);
lean_ctor_set(x_89, 3, x_77);
lean_ctor_set(x_89, 4, x_78);
lean_ctor_set(x_89, 5, x_79);
lean_ctor_set(x_89, 6, x_80);
lean_ctor_set(x_89, 7, x_81);
lean_ctor_set(x_89, 8, x_82);
lean_ctor_set(x_89, 9, x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*10, x_83);
lean_ctor_set_uint8(x_89, sizeof(void*)*10 + 1, x_84);
lean_ctor_set_uint8(x_89, sizeof(void*)*10 + 2, x_85);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_73);
lean_inc(x_90);
x_91 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_4, x_90, x_3);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_95 = l_Lean_Name_toString___closed__1;
x_96 = l_Lean_Name_toStringWithSep___main(x_95, x_94);
x_97 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = l_Lean_Meta_clear___lambda__1___closed__6;
x_100 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = l_Lean_Core_getConstInfo___closed__5;
x_102 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Elab_Tactic_throwError___rarg(x_102, x_90, x_93);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_90);
lean_dec(x_1);
x_104 = lean_ctor_get(x_91, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_105 = x_91;
} else {
 lean_dec_ref(x_91);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_92, 0);
lean_inc(x_106);
lean_dec(x_92);
x_107 = l_Lean_Expr_fvarId_x21(x_106);
lean_dec(x_106);
if (lean_is_scalar(x_105)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_105;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_104);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_90);
lean_dec(x_1);
x_109 = lean_ctor_get(x_91, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_91, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_111 = x_91;
} else {
 lean_dec_ref(x_91);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_getFVarIds___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = x_2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_2, x_1, x_10);
x_12 = x_9;
lean_inc(x_3);
x_13 = l_Lean_Elab_Tactic_getFVarId(x_12, x_3, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_1, x_16);
x_18 = x_14;
x_19 = lean_array_fset(x_11, x_1, x_18);
lean_dec(x_1);
x_1 = x_17;
x_2 = x_19;
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
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
}
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = x_1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Tactic_getFVarIds___spec__1), 4, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_4);
x_7 = x_6;
x_8 = lean_apply_2(x_7, x_2, x_3);
return x_8;
}
}
lean_object* l_Lean_Elab_Tactic_evalRevert___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_revert___boxed), 5, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_7);
lean_inc(x_4);
x_9 = l_Lean_Elab_Tactic_liftMetaM___rarg(x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
x_14 = l_Lean_Elab_Tactic_setGoals(x_13, x_4, x_11);
lean_dec(x_4);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalRevert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Tactic_revert___elambda__1___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_Syntax_getArgs(x_1);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
lean_inc(x_2);
x_15 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3);
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
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getFVarIds), 3, 1);
lean_closure_set(x_20, 0, x_14);
lean_inc(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRevert___lambda__1), 5, 2);
lean_closure_set(x_21, 0, x_18);
lean_closure_set(x_21, 1, x_19);
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_18, x_22, x_2, x_17);
lean_dec(x_18);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_2);
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
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRevert), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRevert(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_revert___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_2(x_1, x_2, x_4);
lean_inc(x_5);
x_8 = l_Lean_Elab_Tactic_liftMetaM___rarg(x_7, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
x_12 = l_Lean_Elab_Tactic_setGoals(x_11, x_5, x_10);
lean_dec(x_5);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget(x_2, x_3);
lean_inc(x_4);
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
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
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getFVarId), 3, 1);
lean_closure_set(x_16, 0, x_10);
lean_inc(x_14);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1___lambda__1), 6, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_15);
x_18 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
lean_inc(x_4);
x_19 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_14, x_18, x_4, x_13);
lean_dec(x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
lean_dec(x_3);
x_3 = x_22;
x_5 = x_20;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
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
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
}
}
lean_object* l_Lean_Elab_Tactic_forEachVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1(x_2, x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_forEachVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_forEachVar(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalClear___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_clear___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_evalClear(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Tactic_clear___elambda__1___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_Syntax_getArgs(x_1);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = l_Lean_Elab_Tactic_evalClear___closed__1;
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1(x_15, x_14, x_16, x_2, x_3);
lean_dec(x_14);
return x_17;
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalClear), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalClear(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_clear___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalSubst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_subst___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_evalSubst(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Tactic_subst___elambda__1___closed__1;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_Syntax_getArgs(x_1);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
lean_dec(x_1);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = l_Lean_Elab_Tactic_evalSubst___closed__1;
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1(x_15, x_14, x_16, x_2, x_3);
lean_dec(x_14);
return x_17;
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSubst), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSubst(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_subst___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalParen(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Elab_Tactic_evalTactic___main(x_5, x_2, x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_evalParen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalParen(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalParen___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalParen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___lambda__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalNestedTacticBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic), 3, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_Lean_Elab_Tactic_focus___rarg(x_6, x_2, x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_Tactic_evalNestedTacticBlock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalNestedTacticBlock(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalNestedTacticBlock___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalNestedTacticBlockCurly(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalNestedTacticBlock(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_evalNestedTacticBlockCurly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalNestedTacticBlockCurly(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalNestedTacticBlockCurly___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlockCurly(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_List_findM_x3f___main___at_Lean_Elab_Tactic_evalCase___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_Elab_Tactic_getMVarDecl(x_7, x_3, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Name_isSuffixOf___main(x_1, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_free_object(x_9);
x_2 = x_8;
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_16; 
lean_inc(x_7);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Name_isSuffixOf___main(x_1, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
x_2 = x_8;
x_4 = x_18;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_inc(x_7);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_7);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
}
}
}
lean_object* l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_name_eq(x_4, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__2(x_5, x_2);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_free_object(x_1);
lean_dec(x_4);
return x_5;
}
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_name_eq(x_8, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__2(x_9, x_2);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_dec(x_8);
return x_9;
}
}
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalCase___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tag not found");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalCase___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalCase___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalCase___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalCase___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalCase(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_44; uint8_t x_45; 
x_44 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
lean_inc(x_1);
x_45 = l_Lean_Syntax_isOfKind(x_1, x_44);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = 0;
x_4 = x_46;
goto block_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = l_Lean_Syntax_getArgs(x_1);
x_48 = lean_array_get_size(x_47);
lean_dec(x_47);
x_49 = lean_unsigned_to_nat(3u);
x_50 = lean_nat_dec_eq(x_48, x_49);
lean_dec(x_48);
x_4 = x_50;
goto block_43;
}
block_43:
{
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
lean_inc(x_2);
x_11 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_List_findM_x3f___main___at_Lean_Elab_Tactic_evalCase___spec__1(x_10, x_12, x_2, x_13);
lean_dec(x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_9);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_evalCase___closed__3;
x_18 = l_Lean_Elab_Tactic_throwError___rarg(x_17, x_2, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__2(x_12, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Elab_Tactic_setGoals(x_23, x_2, x_19);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_2);
x_26 = l_Lean_Elab_Tactic_evalTactic___main(x_9, x_2, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_2);
x_28 = l_Lean_Elab_Tactic_done(x_2, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Elab_Tactic_setGoals(x_21, x_2, x_29);
lean_dec(x_2);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_21);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
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
lean_dec(x_21);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
return x_26;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_26, 0);
x_37 = lean_ctor_get(x_26, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_26);
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
uint8_t x_39; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_11);
if (x_39 == 0)
{
return x_11;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_11, 0);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_11);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
}
lean_object* l_List_findM_x3f___main___at_Lean_Elab_Tactic_evalCase___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_findM_x3f___main___at_Lean_Elab_Tactic_evalCase___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCase), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCase(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalOrelse(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_Syntax_getArgs(x_1);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(3u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_Elab_Tactic_save(x_3);
lean_inc(x_2);
x_17 = l_Lean_Elab_Tactic_evalTactic___main(x_13, x_2, x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Elab_Tactic_restore(x_18, x_16);
lean_dec(x_16);
x_20 = l_Lean_Elab_Tactic_evalTactic___main(x_15, x_2, x_19);
return x_20;
}
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalOrelse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalOrelse), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalOrelse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalOrelse___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_4__regTraceClasses___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_tactic_parenthesizer___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_4__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Tactic_Basic_4__regTraceClasses___closed__1;
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
lean_object* initialize_Lean_Util_CollectMVars(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assumption(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Revert(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Subst(lean_object*);
lean_object* initialize_Lean_Elab_Util(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Tactic_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_goalsToMessageData___closed__1 = _init_l_Lean_Elab_goalsToMessageData___closed__1();
lean_mark_persistent(l_Lean_Elab_goalsToMessageData___closed__1);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__1 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__1);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__2 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__2);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__3 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__3);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__4 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__4);
l_Lean_Elab_Tactic_State_inhabited___closed__1 = _init_l_Lean_Elab_Tactic_State_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_State_inhabited___closed__1);
l_Lean_Elab_Tactic_State_inhabited = _init_l_Lean_Elab_Tactic_State_inhabited();
lean_mark_persistent(l_Lean_Elab_Tactic_State_inhabited);
l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__1 = _init_l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__1);
l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__2 = _init_l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__2);
l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__3 = _init_l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__3);
l_Lean_Elab_Tactic_EStateM_Backtrackable = _init_l_Lean_Elab_Tactic_EStateM_Backtrackable();
lean_mark_persistent(l_Lean_Elab_Tactic_EStateM_Backtrackable);
l_Lean_Elab_Tactic_liftTermElabM___rarg___closed__1 = _init_l_Lean_Elab_Tactic_liftTermElabM___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_liftTermElabM___rarg___closed__1);
l_Lean_Elab_Tactic_collectMVars___closed__1 = _init_l_Lean_Elab_Tactic_collectMVars___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_collectMVars___closed__1);
l_Lean_Elab_Tactic_monadLog___closed__1 = _init_l_Lean_Elab_Tactic_monadLog___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__1);
l_Lean_Elab_Tactic_monadLog___closed__2 = _init_l_Lean_Elab_Tactic_monadLog___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__2);
l_Lean_Elab_Tactic_monadLog___closed__3 = _init_l_Lean_Elab_Tactic_monadLog___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__3);
l_Lean_Elab_Tactic_monadLog___closed__4 = _init_l_Lean_Elab_Tactic_monadLog___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__4);
l_Lean_Elab_Tactic_monadLog___closed__5 = _init_l_Lean_Elab_Tactic_monadLog___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__5);
l_Lean_Elab_Tactic_monadLog___closed__6 = _init_l_Lean_Elab_Tactic_monadLog___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__6);
l_Lean_Elab_Tactic_monadLog___closed__7 = _init_l_Lean_Elab_Tactic_monadLog___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__7);
l_Lean_Elab_Tactic_monadLog___closed__8 = _init_l_Lean_Elab_Tactic_monadLog___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__8);
l_Lean_Elab_Tactic_monadLog___closed__9 = _init_l_Lean_Elab_Tactic_monadLog___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__9);
l_Lean_Elab_Tactic_monadLog___closed__10 = _init_l_Lean_Elab_Tactic_monadLog___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__10);
l_Lean_Elab_Tactic_monadLog___closed__11 = _init_l_Lean_Elab_Tactic_monadLog___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__11);
l_Lean_Elab_Tactic_monadLog = _init_l_Lean_Elab_Tactic_monadLog();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog);
l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg___closed__1 = _init_l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg___closed__1);
l_Lean_Elab_Tactic_monadQuotation___closed__1 = _init_l_Lean_Elab_Tactic_monadQuotation___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_monadQuotation___closed__1);
l_Lean_Elab_Tactic_monadQuotation___closed__2 = _init_l_Lean_Elab_Tactic_monadQuotation___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_monadQuotation___closed__2);
l_Lean_Elab_Tactic_monadQuotation___closed__3 = _init_l_Lean_Elab_Tactic_monadQuotation___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_monadQuotation___closed__3);
l_Lean_Elab_Tactic_monadQuotation___closed__4 = _init_l_Lean_Elab_Tactic_monadQuotation___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_monadQuotation___closed__4);
l_Lean_Elab_Tactic_monadQuotation = _init_l_Lean_Elab_Tactic_monadQuotation();
lean_mark_persistent(l_Lean_Elab_Tactic_monadQuotation);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__1 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__1);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__2 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__2);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__3 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__3);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__4 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__4);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__5 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__5);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__6 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__6);
l_Std_PersistentHashMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__3 = _init_l_Std_PersistentHashMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__3();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__3);
l_Lean_SMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__1___closed__1 = _init_l_Lean_SMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__1___closed__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__1___closed__1);
l_Lean_SMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__1___closed__2 = _init_l_Lean_SMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__1___closed__2();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__1___closed__2);
l_Lean_SMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__1 = _init_l_Lean_SMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Tactic_tacticElabAttribute___spec__1);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__1 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__1);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__2 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__2);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__3 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__3);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__4 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__4);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__5 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__5);
res = l_Lean_Elab_Tactic_mkTacticAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_tacticElabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute);
lean_dec_ref(res);
l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__1 = _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__1);
l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__2 = _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__2);
l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__3 = _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__3);
l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__4 = _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__4);
l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__5 = _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__5);
l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__6 = _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__6);
l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__7 = _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__7);
l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__8 = _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__8);
l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__9 = _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__9);
l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__10 = _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__10);
l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__11 = _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__11);
l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__12 = _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__12);
l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter = _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter();
lean_mark_persistent(l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter);
l_Lean_Elab_Tactic_evalTactic___main___closed__1 = _init_l_Lean_Elab_Tactic_evalTactic___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___main___closed__1);
l_Lean_Elab_Tactic_evalTactic___main___closed__2 = _init_l_Lean_Elab_Tactic_evalTactic___main___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___main___closed__2);
l_Lean_Elab_Tactic_evalTactic___main___closed__3 = _init_l_Lean_Elab_Tactic_evalTactic___main___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___main___closed__3);
l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1 = _init_l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1);
l_Lean_Elab_Tactic_getMainGoal___closed__1 = _init_l_Lean_Elab_Tactic_getMainGoal___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_getMainGoal___closed__1);
l_Lean_Elab_Tactic_getMainGoal___closed__2 = _init_l_Lean_Elab_Tactic_getMainGoal___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_getMainGoal___closed__2);
l_Lean_Elab_Tactic_getMainGoal___closed__3 = _init_l_Lean_Elab_Tactic_getMainGoal___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_getMainGoal___closed__3);
l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1 = _init_l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1);
l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2 = _init_l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2);
l_Lean_Elab_Tactic_ensureHasNoMVars___closed__3 = _init_l_Lean_Elab_Tactic_ensureHasNoMVars___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_ensureHasNoMVars___closed__3);
l_Lean_Elab_Tactic_liftMetaTactic___closed__1 = _init_l_Lean_Elab_Tactic_liftMetaTactic___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_liftMetaTactic___closed__1);
l_Lean_Elab_Tactic_focus___rarg___closed__1 = _init_l_Lean_Elab_Tactic_focus___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_focus___rarg___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSeq___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSeq___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSeq___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalSeq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalChoice(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalSkip(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalFailIfSuccess___closed__1 = _init_l_Lean_Elab_Tactic_evalFailIfSuccess___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalFailIfSuccess___closed__1);
l_Lean_Elab_Tactic_evalFailIfSuccess___closed__2 = _init_l_Lean_Elab_Tactic_evalFailIfSuccess___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalFailIfSuccess___closed__2);
l_Lean_Elab_Tactic_evalFailIfSuccess___closed__3 = _init_l_Lean_Elab_Tactic_evalFailIfSuccess___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalFailIfSuccess___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalTraceState(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalAssumption___rarg___closed__1 = _init_l_Lean_Elab_Tactic_evalAssumption___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalAssumption___rarg___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalAssumption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalIntro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalIntros(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalRevert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalClear___closed__1 = _init_l_Lean_Elab_Tactic_evalClear___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalClear___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalClear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalSubst___closed__1 = _init_l_Lean_Elab_Tactic_evalSubst___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSubst___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalSubst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalParen(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlockCurly(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalCase___closed__1 = _init_l_Lean_Elab_Tactic_evalCase___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalCase___closed__1);
l_Lean_Elab_Tactic_evalCase___closed__2 = _init_l_Lean_Elab_Tactic_evalCase___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalCase___closed__2);
l_Lean_Elab_Tactic_evalCase___closed__3 = _init_l_Lean_Elab_Tactic_evalCase___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalCase___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalCase(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalOrelse___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalOrelse___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalOrelse___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalOrelse(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Basic_4__regTraceClasses___closed__1 = _init_l___private_Lean_Elab_Tactic_Basic_4__regTraceClasses___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_4__regTraceClasses___closed__1);
res = l___private_Lean_Elab_Tactic_Basic_4__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
