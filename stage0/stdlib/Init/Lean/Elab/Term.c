// Lean compiler output
// Module: Init.Lean.Elab.Term
// Imports: Init.Lean.Meta Init.Lean.Elab.Log Init.Lean.Elab.Alias Init.Lean.Elab.ResolveName
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
extern lean_object* l___private_Init_Lean_Meta_Check_2__checkLambdaLet___lambda__2___closed__1;
lean_object* l_Lean_Elab_Term_elabBinders(lean_object*);
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_16__regTraceClasses___closed__1;
extern lean_object* l_Lean_Parser_Term_app___elambda__1___closed__1;
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__2;
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Term_ensureType___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Environment_8__persistentEnvExtensionsRef;
lean_object* l_Lean_Elab_Term_elabDepArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__8;
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Term_11__mkFreshLevelMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___closed__3;
lean_object* l_Lean_Elab_Term_tracer___closed__5;
lean_object* l_Lean_Elab_Term_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName(lean_object*);
extern lean_object* l_Lean_nameToExprAux___main___closed__1;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__1;
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__8;
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Term_11__mkFreshLevelMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabHole___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabDepArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__2;
lean_object* l_Lean_Elab_Term_elabArrow___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_PersistentHashMap_containsAtAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tracer___closed__3;
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_ensureType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCacheWhen(lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
extern lean_object* l_Lean_List_format___rarg___closed__2;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__3;
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshId(lean_object*);
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_elabArrow___closed__2;
lean_object* l_HashMapImp_find___at_Lean_Elab_Term_elabTerm___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParen(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_8__elabBindersAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinder___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_nameToExprAux___main___closed__4;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2;
lean_object* l_Lean_Elab_Term_getLocalInsts___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCacheWhen___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__2(lean_object*);
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Log_1__resetTraceState___at_Lean_Elab_Term_elabTerm___spec__7(lean_object*);
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___closed__6;
lean_object* l___private_Init_Lean_Elab_Log_1__resetTraceState___at_Lean_Elab_Term_elabTerm___spec__7___rarg(lean_object*);
extern lean_object* l_Lean_stxInh;
extern lean_object* l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_10__resolveLocalName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSort___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_9__resolveLocalNameAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__3;
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__2;
lean_object* l_Lean_Elab_Term_elabTypeStx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__5;
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getEnv___boxed(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrow___closed__3;
lean_object* l_AssocList_foldlM___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__15(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__5;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__6;
lean_object* l___private_Init_Lean_Util_Trace_4__checkTraceOption___at_Lean_Elab_Term_elabTerm___spec__13___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabHole(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabForall(lean_object*);
lean_object* l_Lean_Elab_Term_elabParen___closed__3;
extern lean_object* l_Lean_Elab_mkElabAttribute___rarg___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__1;
lean_object* l_Lean_Elab_Term_NamedArg_hasToString(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_mkTermElabAttribute___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache(lean_object*);
lean_object* l_Lean_registerAttribute(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_14__expandAppAux(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Elab_Term_TermElabM_monadLog___spec__1(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__2;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__3;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__1;
lean_object* l_Lean_Elab_Term_elabSort___boxed(lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Elab_Term_withLCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTerm___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTypeStx___rarg(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__1;
extern lean_object* l_Lean_Parser_Term_cons___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___closed__2;
lean_object* l_Lean_Elab_Term_dbgTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_FileMap_ofString___closed__1;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__2;
lean_object* l_AssocList_find___main___at_Lean_Elab_Term_elabTerm___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_5__expandOptIdent(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_TermElabM_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Elab_Term_elabTerm___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_6__matchBinder___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_termElabAttribute___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__11(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getTraceState(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_6__matchBinder___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__4;
lean_object* l_Lean_Elab_Term_elabParen___closed__2;
lean_object* l_Lean_Elab_Term_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_prop___elambda__1___rarg___closed__2;
lean_object* l_Lean_Elab_Term_elabParen___closed__1;
lean_object* l_Lean_Elab_Term_elabListLit___closed__1;
lean_object* l_Lean_Elab_Term_liftMetaM(lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Term_elabListLit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_6__matchBinder___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabListLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___rarg___closed__1;
lean_object* l_Lean_Meta_isClass(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_4__expandBinderIdent(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_7__elabBinderViews___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabListLit___closed__2;
extern lean_object* l_Lean_Meta_dbgTrace___rarg___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_12__mkConsts(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_4__expandBinderIdent___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__16(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Name_appendIndexAfter___closed__1;
lean_object* l_Lean_Elab_Term_addContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_15__expandApp(lean_object*);
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Term_ensureType___spec__3___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_Monad;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__2;
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___at_Lean_Elab_Term_elabTerm___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getTraceState___rarg(lean_object*);
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_Lean_Elab_Term_dbgTrace(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__1;
extern lean_object* l_Lean_Parser_Term_id___elambda__1___closed__2;
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__3;
lean_object* l_Lean_SMap_find___at_Lean_Elab_Term_elabTerm___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshId___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___closed__7;
lean_object* l_Lean_Elab_Term_elabProp___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_mkHole___closed__1;
lean_object* l_PersistentHashMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__3;
lean_object* l_Lean_Elab_Term_elabId(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_termElabAttribute___closed__1;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__3;
lean_object* l_Lean_Elab_Term_mkHole___closed__2;
uint8_t l_PersistentHashMap_containsAtAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabParen(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_3__expandBinderType___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_elabForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__6;
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_setTraceState___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__7;
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_ensureType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___boxed(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_TermElabM_monadLog___spec__2(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__2;
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__3;
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withNode___rarg___closed__1;
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicitUniv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTypeStx(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_Elab_Term_termElabAttribute___closed__3;
lean_object* l___private_Init_Lean_Elab_Log_1__resetTraceState___at_Lean_Elab_Term_elabTerm___spec__7___boxed(lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___closed__5;
lean_object* l_Lean_Elab_Term_withNode___rarg___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_7__elabBinderViews___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__3;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabListLit___closed__4;
extern lean_object* l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
extern lean_object* l_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx(lean_object*);
lean_object* l_Lean_Elab_logInfoAt___at_Lean_Elab_Term_elabTerm___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__3;
lean_object* l___private_Init_Lean_Elab_Term_10__resolveLocalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__5;
lean_object* l___private_Init_Lean_Elab_Term_6__matchBinder___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow(lean_object*);
lean_object* l_Lean_Elab_Term_elabTypeStx___rarg___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshId___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_elabParen___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_8__elabBindersAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabTerm___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkBuiltinTermElabTable(lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabTerm___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_6__matchBinder___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabProp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTerm___spec__3(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_9__resolveLocalNameAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_6__matchBinder___closed__1;
extern lean_object* l_Lean_Parser_mkTermParserAttribute___closed__4;
lean_object* l_Lean_Elab_Term_mkTermElabAttribute(lean_object*);
uint8_t l_PersistentHashMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__4(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__1;
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__7;
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_addBuiltinTermElab___closed__2;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabApp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_6__matchBinder(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSort(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_6__matchBinder___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__5(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_16__regTraceClasses(lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_11__mkFreshLevelMVars___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
extern lean_object* l___private_Init_Lean_Environment_5__envExtensionsRef;
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabProp(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_arrow___elambda__1___closed__2;
lean_object* l_HashMapImp_expand___at_Lean_Elab_Term_addBuiltinTermElab___spec__13(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_7__elabBinderViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp(lean_object*);
lean_object* l_Lean_Elab_Term_addBuiltinTermElab___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___rarg(lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__1;
lean_object* l_Lean_Elab_Term_addBuiltinTermElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLocalInsts(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProp(lean_object*);
lean_object* l_HashMapImp_find___at_Lean_Elab_Term_elabTerm___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_formatEntry___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__2;
lean_object* l_Lean_Elab_Term_isClass(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_ensureType___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__1;
lean_object* l_Lean_Elab_Term_elabListLit___closed__5;
lean_object* l_Lean_Elab_Term_elabBinders___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_HashMapImp_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Elab_Term_elabTerm___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__4;
lean_object* l_Lean_Elab_Term_withNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_setParam___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__3;
lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_fix1___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_3__expandBinderType(lean_object*);
extern lean_object* l_Lean_Meta_Exception_toStr___closed__7;
lean_object* l___private_Init_Lean_Elab_Term_8__elabBindersAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicitUniv___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__6;
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Term_withLCtx(lean_object*);
lean_object* l_Lean_Elab_Term_withNode(lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_Lean_Elab_Term_getNamespace___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__1;
lean_object* l_Lean_Elab_Term_elabHole(lean_object*);
extern lean_object* l_Lean_Parser_Term_implicitBinder___elambda__1___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId(lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__2;
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Lean_Elab_Term_elabArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__4;
lean_object* l___private_Init_Lean_Elab_Term_11__mkFreshLevelMVars(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__7;
lean_object* l_Lean_Elab_Term_elabApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__3;
extern lean_object* l_Lean_Parser_Term_instBinder___elambda__1___rarg___closed__2;
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__5;
lean_object* l_Lean_Elab_Term_getLCtx(lean_object*, lean_object*);
uint8_t l_HashMapImp_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_ensureType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkHole;
extern lean_object* l_Lean_mkInitAttr___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_elabId___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_asNode___closed__1;
lean_object* l_Lean_nameToExprAux___main(lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_SMap_find___at_Lean_Elab_Term_elabTerm___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__2;
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Term_tracer___closed__4;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr(lean_object*);
lean_object* l_Lean_registerTagAttribute___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___closed__1;
extern lean_object* l_Lean_Parser_Term_paren___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__1;
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_elabTerm___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__1;
extern lean_object* l_Lean_Parser_Term_app___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar___rarg(lean_object*);
lean_object* l_PersistentHashMap_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__8(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_6__matchBinder___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__2;
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCacheWhen___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_13__elabAppAux___closed__1;
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1;
lean_object* l_Lean_Elab_Term_elabTerm___closed__2;
lean_object* l_Lean_Elab_Term_elabHole___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSort(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_13__elabAppAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkHole___closed__3;
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___rarg___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logInfoAt___at_Lean_Elab_Term_elabTerm___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_Term_elabListLit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_5__expandOptIdent___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__2;
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Term_elabTerm___spec__11(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___closed__1;
lean_object* l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1___closed__1;
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___rarg___closed__2;
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Term_namedArgument___elambda__1___rarg___closed__2;
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getEnv(lean_object*);
lean_object* l_Lean_Elab_Term_getOpenDecls(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabListLit(lean_object*);
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__4;
lean_object* l_Lean_Elab_Term_tracer___closed__2;
lean_object* l___private_Init_Lean_Util_Trace_4__checkTraceOption___at_Lean_Elab_Term_elabTerm___spec__13(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName(lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_13__elabAppAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx___main(lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___closed__3;
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_Elab_Term_addBuiltinTermElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___at_Lean_Elab_Term_elabTerm___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_8__elabBindersAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tracer___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_7__elabBinderViews___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__3;
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___closed__9;
lean_object* l_Lean_Elab_Term_getOpenDecls___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getTraceState___boxed(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__2;
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar(lean_object*);
lean_object* l_Lean_Elab_Term_tracer___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__4;
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Term_elabTerm___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1;
lean_object* l_Lean_Elab_Term_getLCtx___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar___boxed(lean_object*);
uint8_t l___private_Init_Lean_Util_Trace_3__checkTraceOptionAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_elabTerm___spec__10(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_setTraceState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_resolveName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_SMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabListLit___closed__3;
lean_object* l_Lean_Elab_Term_addContext(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_listLit___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__4;
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l_Lean_Elab_Term_tracer;
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_builtinTermElabTable;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_mkTermElabAttribute___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at_Lean_Elab_Term_elabTerm___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Term_elabListLit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__1;
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1;
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Elab_Term_elabTerm___spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrow(lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_14__expandAppAux___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__5;
extern lean_object* l_HashMap_Inhabited___closed__1;
extern lean_object* l_Lean_Parser_Term_simpleBinder___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__1;
lean_object* l_AssocList_contains___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getNamespace(lean_object*, lean_object*);
extern lean_object* l_String_Inhabited;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__1;
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_mkTermElabAttribute___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__6;
lean_object* l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___rarg___closed__2;
lean_object* l_Lean_Elab_Term_resolveName___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__2;
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCache(lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__12(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___closed__8;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_6__matchBinder___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_resolveName___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
extern lean_object* l_Lean_initAttr;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOptions___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_tracer___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___closed__4;
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__14(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at_Lean_Elab_Term_elabTerm___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftMetaM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_mkTermElabAttribute___closed__1;
extern lean_object* l_Lean_Parser_Term_type___elambda__1___rarg___closed__2;
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__2;
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_sort___elambda__1___rarg___closed__2;
lean_object* l_Lean_Elab_Term_elabBinder(lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Elab_Term_TermElabM_monadLog___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_TermElabM_monadLog___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_TermElabM_monadLog___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_TermElabM_monadLog___spec__2___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_3, 2, x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_13);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Elab_Term_TermElabM_monadLog___spec__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_TermElabM_monadLog___lambda__2___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_TermElabM_monadLog___closed__1;
x_2 = l_Lean_Elab_Term_TermElabM_monadLog___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_TermElabM_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_TermElabM_monadLog___lambda__3___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_TermElabM_monadLog___closed__1;
x_2 = l_Lean_Elab_Term_TermElabM_monadLog___closed__4;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_TermElabM_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_TermElabM_monadLog___lambda__4___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_TermElabM_monadLog___closed__1;
x_2 = l_Lean_Elab_Term_TermElabM_monadLog___closed__6;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_TermElabM_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_TermElabM_monadLog___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_TermElabM_monadLog___closed__8;
x_2 = l_Lean_Elab_Term_TermElabM_monadLog___closed__3;
x_3 = l_Lean_Elab_Term_TermElabM_monadLog___closed__5;
x_4 = l_Lean_Elab_Term_TermElabM_monadLog___closed__7;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_TermElabM_monadLog___closed__9;
return x_1;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_TermElabM_monadLog___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_TermElabM_monadLog___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_TermElabM_monadLog___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_TermElabM_monadLog___lambda__4(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
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
uint8_t l_PersistentHashMap_containsAtAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = lean_name_eq(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_2 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = 1;
return x_12;
}
}
}
}
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__5(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
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
lean_object* x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = x_2 >> x_5;
x_15 = l_PersistentHashMap_containsAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__5(x_13, x_14, x_3);
lean_dec(x_13);
return x_15;
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
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_PersistentHashMap_containsAtAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__6(x_17, x_18, x_3);
return x_19;
}
}
}
uint8_t l_PersistentHashMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
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
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_HashMapImp_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__2(x_4, x_2);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_PersistentHashMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__4(x_5, x_2);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_HashMapImp_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__2(x_9, x_2);
return x_10;
}
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__11(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_name_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_name_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_name_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; size_t x_84; uint8_t x_85; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__10(x_1, x_82, x_4, x_5);
x_84 = 7;
x_85 = x_84 <= x_3;
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_83);
x_87 = lean_unsigned_to_nat(4u);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_dec(x_83);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_iterateMAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__11(x_3, x_89, x_90, x_89, x_82, x_91);
lean_dec(x_90);
lean_dec(x_89);
return x_92;
}
else
{
return x_83;
}
}
else
{
return x_83;
}
}
}
}
lean_object* l_PersistentHashMap_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Name_hash(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l_AssocList_foldlM___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__15(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Name_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_foldlM___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__15(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_HashMapImp_expand___at_Lean_Elab_Term_addBuiltinTermElab___spec__13(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__14(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__16(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__16(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_HashMapImp_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__3(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_HashMapImp_expand___at_Lean_Elab_Term_addBuiltinTermElab___spec__13(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_AssocList_replace___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__16(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Name_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__3(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_HashMapImp_expand___at_Lean_Elab_Term_addBuiltinTermElab___spec__13(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_AssocList_replace___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__16(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_SMap_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_PersistentHashMap_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__8(x_6, x_2, x_3);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_PersistentHashMap_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__8(x_9, x_2, x_3);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_4);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_HashMapImp_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__12(x_13, x_2, x_3);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = l_HashMapImp_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__12(x_15, x_2, x_3);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_4);
return x_18;
}
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
lean_object* _init_l_Lean_Elab_Term_addBuiltinTermElab___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already been defined");
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_SMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__1(x_8, x_1);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_6);
x_11 = lean_io_ref_get(x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_io_ref_reset(x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_SMap_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__7(x_12, x_1, x_3);
x_17 = lean_io_ref_set(x_5, x_16, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
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
uint8_t x_22; 
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_26 = l_System_FilePath_dirName___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_1);
x_28 = l_Lean_Elab_Term_addBuiltinTermElab___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_Elab_Term_addBuiltinTermElab___closed__2;
x_31 = lean_string_append(x_29, x_30);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_31);
return x_6;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_6, 0);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_6);
x_34 = l_Lean_SMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__1(x_32, x_1);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_io_ref_get(x_5, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_io_ref_reset(x_5, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_SMap_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__7(x_36, x_1, x_3);
x_41 = lean_io_ref_set(x_5, x_40, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_36);
lean_dec(x_3);
lean_dec(x_1);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_44 = x_38;
} else {
 lean_dec_ref(x_38);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
lean_dec(x_1);
x_46 = lean_ctor_get(x_35, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_48 = x_35;
} else {
 lean_dec_ref(x_35);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_3);
x_50 = l_System_FilePath_dirName___closed__1;
x_51 = l_Lean_Name_toStringWithSep___main(x_50, x_1);
x_52 = l_Lean_Elab_Term_addBuiltinTermElab___closed__1;
x_53 = lean_string_append(x_52, x_51);
lean_dec(x_51);
x_54 = l_Lean_Elab_Term_addBuiltinTermElab___closed__2;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_33);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_3);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_6);
if (x_57 == 0)
{
return x_6;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_6, 0);
x_59 = lean_ctor_get(x_6, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_6);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
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
lean_object* l_PersistentHashMap_containsAtAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_PersistentHashMap_containsAtAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__11(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9(x_1, x_6, x_7, x_4, x_5);
return x_8;
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
x_1 = l_Lean_nameToExprAux___main___closed__4;
x_2 = l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addBuiltinTermElab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__6;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__8() {
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
x_16 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__7;
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
lean_dec(x_6);
x_26 = l_System_FilePath_dirName___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_3);
x_28 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__8;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Char_HasRepr___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_4);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_3);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
x_34 = l_Lean_initAttr;
x_35 = lean_box(0);
x_36 = l_Lean_ParametricAttribute_setParam___rarg(x_34, x_33, x_6, x_35);
x_37 = l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1(x_36, x_4);
lean_dec(x_36);
return x_37;
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
lean_object* x_1; 
x_1 = lean_mk_string("unexpected term elaborator type at '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' `TermElab` expected");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__4() {
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
if (x_4 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__1;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_inc(x_1);
x_9 = l_Lean_Elab_syntaxNodeKindOfAttrParam(x_1, x_8, x_3, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_22; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_1);
x_22 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_23 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Lean_ConstantInfo_type(x_25);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 4)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = l_Lean_nameToExprAux___main___closed__1;
x_37 = lean_string_dec_eq(x_35, x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_10);
lean_dec(x_1);
x_38 = lean_box(0);
x_13 = x_38;
goto block_21;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__1;
x_40 = lean_string_dec_eq(x_34, x_39);
lean_dec(x_34);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_10);
lean_dec(x_1);
x_41 = lean_box(0);
x_13 = x_41;
goto block_21;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
x_43 = lean_string_dec_eq(x_33, x_42);
lean_dec(x_33);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_32);
lean_dec(x_10);
lean_dec(x_1);
x_44 = lean_box(0);
x_13 = x_44;
goto block_21;
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__4;
x_46 = lean_string_dec_eq(x_32, x_45);
lean_dec(x_32);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_10);
lean_dec(x_1);
x_47 = lean_box(0);
x_13 = x_47;
goto block_21;
}
else
{
lean_object* x_48; 
lean_dec(x_12);
x_48 = l_Lean_Elab_Term_declareBuiltinTermElab(x_1, x_10, x_2, x_11);
return x_48;
}
}
}
}
}
else
{
lean_object* x_49; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_1);
x_49 = lean_box(0);
x_13 = x_49;
goto block_21;
}
}
else
{
lean_object* x_50; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_1);
x_50 = lean_box(0);
x_13 = x_50;
goto block_21;
}
}
else
{
lean_object* x_51; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_1);
x_51 = lean_box(0);
x_13 = x_51;
goto block_21;
}
}
else
{
lean_object* x_52; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_1);
x_52 = lean_box(0);
x_13 = x_52;
goto block_21;
}
}
else
{
lean_object* x_53; 
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_1);
x_53 = lean_box(0);
x_13 = x_53;
goto block_21;
}
}
else
{
lean_object* x_54; 
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_1);
x_54 = lean_box(0);
x_13 = x_54;
goto block_21;
}
}
block_21:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
x_14 = l_System_FilePath_dirName___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_2);
x_16 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__2;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__3;
x_19 = lean_string_append(x_17, x_18);
if (lean_is_scalar(x_12)) {
 x_20 = lean_alloc_ctor(1, 2, 0);
} else {
 x_20 = x_12;
 lean_ctor_set_tag(x_20, 1);
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
}
else
{
uint8_t x_55; 
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_9);
if (x_55 == 0)
{
return x_9;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_9, 0);
x_57 = lean_ctor_get(x_9, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_9);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Builtin term elaborator");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_1 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__2;
x_2 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__5;
x_3 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__6;
x_4 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__3;
x_5 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__4;
x_6 = l_Lean_AttributeImpl_inhabited___closed__4;
x_7 = l_Lean_AttributeImpl_inhabited___closed__5;
x_8 = 1;
x_9 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 4, x_5);
lean_ctor_set(x_9, 5, x_6);
lean_ctor_set(x_9, 6, x_7);
lean_ctor_set(x_9, 7, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*8, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__7;
x_3 = l_Lean_registerAttribute(x_2, x_1);
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
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_mkTermElabAttribute___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_5);
return x_11;
}
}
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_HashMap_Inhabited___closed__1;
x_3 = l_PersistentHashMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l___private_Init_Lean_Environment_5__envExtensionsRef;
x_14 = lean_io_ref_get(x_13, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_15);
lean_dec(x_15);
x_18 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__2;
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_io_ref_get(x_13, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_io_ref_reset(x_13, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_19);
x_26 = x_19;
x_27 = lean_array_push(x_21, x_26);
x_28 = lean_io_ref_set(x_13, x_27, x_24);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_19);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_19);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_21);
lean_dec(x_19);
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
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
lean_dec(x_19);
x_41 = !lean_is_exclusive(x_20);
if (x_41 == 0)
{
return x_20;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_20, 0);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_20);
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
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_14);
if (x_45 == 0)
{
return x_14;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_14, 0);
x_47 = lean_ctor_get(x_14, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_14);
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
uint8_t x_49; 
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_3);
if (x_49 == 0)
{
return x_3;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_3, 0);
x_51 = lean_ctor_get(x_3, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_3);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_mkTermElabAttribute___spec__3(x_1, x_6, x_6, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_4);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = l_Array_empty___closed__1;
lean_inc(x_11);
x_13 = lean_apply_1(x_11, x_12);
x_14 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_15 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4(x_15, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 4);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_11);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_22);
x_24 = lean_io_ref_get(x_3, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_io_ref_reset(x_3, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_23);
x_30 = x_23;
x_31 = lean_array_push(x_25, x_30);
x_32 = lean_io_ref_set(x_3, x_31, x_28);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_23);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_23);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
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
lean_dec(x_25);
lean_dec(x_23);
x_41 = !lean_is_exclusive(x_27);
if (x_41 == 0)
{
return x_27;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_27, 0);
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_27);
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
lean_dec(x_23);
x_45 = !lean_is_exclusive(x_24);
if (x_45 == 0)
{
return x_24;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_24, 0);
x_47 = lean_ctor_get(x_24, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_24);
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
lean_dec(x_11);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_16);
if (x_49 == 0)
{
return x_16;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_16, 0);
x_51 = lean_ctor_get(x_16, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_16);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
lean_dec(x_1);
x_54 = l_System_FilePath_dirName___closed__1;
x_55 = l_Lean_Name_toStringWithSep___main(x_54, x_53);
x_56 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_59 = lean_string_append(x_57, x_58);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_59);
return x_4;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_4, 0);
x_61 = lean_ctor_get(x_4, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_4);
x_62 = lean_array_get_size(x_60);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_mkTermElabAttribute___spec__3(x_1, x_60, x_60, x_62, x_63);
lean_dec(x_62);
lean_dec(x_60);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
x_66 = l_Array_empty___closed__1;
lean_inc(x_65);
x_67 = lean_apply_1(x_65, x_66);
x_68 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_69 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_69, 0, x_67);
lean_closure_set(x_69, 1, x_68);
x_70 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4(x_69, x_61);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_1, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_1, 4);
lean_inc(x_76);
lean_dec(x_1);
x_77 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_65);
lean_ctor_set(x_77, 3, x_74);
lean_ctor_set(x_77, 4, x_75);
lean_ctor_set(x_77, 5, x_76);
x_78 = lean_io_ref_get(x_3, x_72);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_io_ref_reset(x_3, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_77);
x_84 = x_77;
x_85 = lean_array_push(x_79, x_84);
x_86 = lean_io_ref_set(x_3, x_85, x_82);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_77);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_77);
x_90 = lean_ctor_get(x_86, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_92 = x_86;
} else {
 lean_dec_ref(x_86);
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
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_79);
lean_dec(x_77);
x_94 = lean_ctor_get(x_81, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_81, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_96 = x_81;
} else {
 lean_dec_ref(x_81);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_77);
x_98 = lean_ctor_get(x_78, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_78, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_100 = x_78;
} else {
 lean_dec_ref(x_78);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_65);
lean_dec(x_1);
x_102 = lean_ctor_get(x_70, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_70, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_104 = x_70;
} else {
 lean_dec_ref(x_70);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_106 = lean_ctor_get(x_1, 0);
lean_inc(x_106);
lean_dec(x_1);
x_107 = l_System_FilePath_dirName___closed__1;
x_108 = l_Lean_Name_toStringWithSep___main(x_107, x_106);
x_109 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_110 = lean_string_append(x_109, x_108);
lean_dec(x_108);
x_111 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_112 = lean_string_append(x_110, x_111);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_61);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_4);
if (x_114 == 0)
{
return x_4;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_4, 0);
x_116 = lean_ctor_get(x_4, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_4);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
lean_object* _init_l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_fix1___rarg___lambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_3);
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___rarg___lambda__2___boxed), 2, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1___closed__1;
x_8 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_8);
lean_ctor_set(x_9, 4, x_6);
x_10 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__2(x_9, x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Elab_mkElabAttribute___rarg___closed__1;
lean_inc(x_2);
x_14 = lean_string_append(x_2, x_13);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean_closure_set(x_15, 0, x_1);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = l_Lean_AttributeImpl_inhabited___closed__1;
x_18 = l_Lean_AttributeImpl_inhabited___closed__4;
x_19 = l_Lean_AttributeImpl_inhabited___closed__5;
x_20 = 0;
x_21 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_15);
lean_ctor_set(x_21, 4, x_16);
lean_ctor_set(x_21, 5, x_18);
lean_ctor_set(x_21, 6, x_19);
lean_ctor_set(x_21, 7, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*8, x_20);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_2);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = l_Lean_Elab_mkElabAttribute___rarg___closed__1;
lean_inc(x_2);
x_26 = lean_string_append(x_2, x_25);
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean_closure_set(x_27, 0, x_1);
lean_inc(x_1);
x_28 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean_closure_set(x_28, 0, x_1);
x_29 = l_Lean_AttributeImpl_inhabited___closed__1;
x_30 = l_Lean_AttributeImpl_inhabited___closed__4;
x_31 = l_Lean_AttributeImpl_inhabited___closed__5;
x_32 = 0;
x_33 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_29);
lean_ctor_set(x_33, 3, x_27);
lean_ctor_set(x_33, 4, x_28);
lean_ctor_set(x_33, 5, x_30);
lean_ctor_set(x_33, 6, x_31);
lean_ctor_set(x_33, 7, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*8, x_32);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_34, 2, x_2);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_24);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_10);
if (x_36 == 0)
{
return x_10;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_10, 0);
x_38 = lean_ctor_get(x_10, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_10);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabTerm");
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
lean_object* l_Lean_Elab_Term_mkTermElabAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_mkTermElabAttribute___closed__2;
x_3 = l_Lean_Parser_mkTermParserAttribute___closed__4;
x_4 = l_Lean_Elab_Term_builtinTermElabTable;
x_5 = l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_mkTermElabAttribute___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_mkTermElabAttribute___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Term_termElabAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_termElabAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Term_termElabAttribute___closed__1;
x_2 = lean_box(0);
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_4 = l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1___closed__1;
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
lean_object* _init_l_Lean_Elab_Term_termElabAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_AttributeImpl_inhabited___closed__6;
x_2 = l_Lean_Elab_Term_termElabAttribute___closed__2;
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_liftMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_apply_2(x_1, x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 1);
lean_ctor_set(x_3, 0, x_9);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
lean_ctor_set(x_3, 0, x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_3, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_26 = lean_apply_2(x_1, x_4, x_21);
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
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_25);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
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
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_24);
lean_ctor_set(x_36, 4, x_25);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
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
lean_object* l_Lean_Elab_Term_getNamespace(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_getNamespace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_getNamespace(x_1, x_2);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 2);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_3, 4);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_18, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_18, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 5);
lean_inc(x_27);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 x_28 = x_18;
} else {
 lean_dec_ref(x_18);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 6, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set(x_29, 4, x_1);
lean_ctor_set(x_29, 5, x_27);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_19);
lean_ctor_set(x_30, 2, x_20);
lean_ctor_set(x_30, 3, x_21);
lean_ctor_set(x_30, 4, x_22);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
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
lean_object* l_Lean_Elab_Term_addContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_alloc_ctor(5, 4, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
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
lean_object* l_Lean_Elab_Term_tracer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_apply_1(x_1, x_7);
lean_ctor_set(x_5, 4, x_8);
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
x_17 = lean_apply_1(x_1, x_15);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_14);
lean_ctor_set(x_18, 4, x_17);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_21, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_21, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_21, 5);
lean_inc(x_31);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 lean_ctor_release(x_21, 5);
 x_32 = x_21;
} else {
 lean_dec_ref(x_21);
 x_32 = lean_box(0);
}
x_33 = lean_apply_1(x_1, x_30);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 6, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 4, x_33);
lean_ctor_set(x_34, 5, x_31);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_22);
lean_ctor_set(x_35, 2, x_23);
lean_ctor_set(x_35, 3, x_24);
lean_ctor_set(x_35, 4, x_25);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
lean_object* _init_l_Lean_Elab_Term_tracer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getOptions___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_tracer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_tracer___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_tracer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getTraceState___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_tracer___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_addContext___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_tracer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_tracer___closed__1;
x_2 = l_Lean_Elab_Term_tracer___closed__2;
x_3 = l_Lean_Elab_Term_tracer___closed__3;
x_4 = l_Lean_Elab_Term_tracer___closed__4;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_tracer() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_tracer___closed__5;
return x_1;
}
}
lean_object* l_Lean_Elab_Term_tracer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_tracer___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
lean_object* l_Lean_Elab_Term_isDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_5, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 1);
lean_ctor_set(x_4, 0, x_10);
lean_ctor_set(x_8, 1, x_4);
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
lean_ctor_set(x_4, 0, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_4, 0, x_16);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_4, 0, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get(x_4, 2);
x_25 = lean_ctor_get(x_4, 3);
x_26 = lean_ctor_get(x_4, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_27 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_5, x_22);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_25);
lean_ctor_set(x_31, 4, x_26);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_35 = x_27;
} else {
 lean_dec_ref(x_27);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_23);
lean_ctor_set(x_37, 2, x_24);
lean_ctor_set(x_37, 3, x_25);
lean_ctor_set(x_37, 4, x_26);
if (lean_is_scalar(x_35)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_35;
}
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l_Lean_Elab_Term_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = l_Lean_Meta_inferType(x_1, x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 1);
lean_ctor_set(x_3, 0, x_9);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
lean_ctor_set(x_3, 0, x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_3, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_26 = l_Lean_Meta_inferType(x_1, x_4, x_21);
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
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_25);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
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
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_24);
lean_ctor_set(x_36, 4, x_25);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Lean_Elab_Term_whnf(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = l_Lean_Meta_whnf(x_1, x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 1);
lean_ctor_set(x_3, 0, x_9);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
lean_ctor_set(x_3, 0, x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_3, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_26 = l_Lean_Meta_whnf(x_1, x_4, x_21);
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
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_25);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
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
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_24);
lean_ctor_set(x_36, 4, x_25);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Lean_Elab_Term_isClass(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = l_Lean_Meta_isClass(x_1, x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 1);
lean_ctor_set(x_3, 0, x_9);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
lean_ctor_set(x_3, 0, x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_3, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_26 = l_Lean_Meta_isClass(x_1, x_4, x_21);
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
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_25);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
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
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_24);
lean_ctor_set(x_36, 4, x_25);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 1);
lean_ctor_set(x_1, 0, x_6);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_1);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get(x_1, 4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_15 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set(x_19, 4, x_14);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_mkFreshLevelMVar___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_mkFreshLevelMVar(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_mkFreshExprMVar(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_Lean_Meta_mkFreshExprMVar(x_1, x_2, x_3, x_6, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 1);
lean_ctor_set(x_5, 0, x_11);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_5, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 3);
x_19 = lean_ctor_get(x_5, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_20 = l_Lean_Meta_mkFreshExprMVar(x_1, x_2, x_3, x_6, x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_17);
lean_ctor_set(x_24, 3, x_18);
lean_ctor_set(x_24, 4, x_19);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshExprMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_mkForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_Lean_Meta_mkForall(x_1, x_2, x_5, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 1);
lean_ctor_set(x_4, 0, x_10);
lean_ctor_set(x_8, 1, x_4);
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
lean_ctor_set(x_4, 0, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_4, 0, x_16);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_4, 0, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get(x_4, 2);
x_25 = lean_ctor_get(x_4, 3);
x_26 = lean_ctor_get(x_4, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_27 = l_Lean_Meta_mkForall(x_1, x_2, x_5, x_22);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_25);
lean_ctor_set(x_31, 4, x_26);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_35 = x_27;
} else {
 lean_dec_ref(x_27);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_23);
lean_ctor_set(x_37, 2, x_24);
lean_ctor_set(x_37, 3, x_25);
lean_ctor_set(x_37, 4, x_26);
if (lean_is_scalar(x_35)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_35;
}
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_withNode___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("term elaborator failed, unexpected syntax");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_withNode___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_withNode___rarg___closed__1;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_withNode___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; 
x_5 = lean_apply_3(x_2, x_1, x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_Elab_Term_withNode___rarg___closed__2;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_withNode(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNode___rarg), 4, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabTerm___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTerm___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
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
lean_object* x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_18 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTerm___spec__3(x_16, x_17, x_3);
lean_dec(x_16);
return x_18;
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
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabTerm___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_find___at_Lean_Elab_Term_elabTerm___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTerm___spec__3(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_Term_elabTerm___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_find___at_Lean_Elab_Term_elabTerm___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_Elab_Term_elabTerm___spec__6(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find___at_Lean_Elab_Term_elabTerm___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_PersistentHashMap_find___at_Lean_Elab_Term_elabTerm___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_HashMapImp_find___at_Lean_Elab_Term_elabTerm___spec__5(x_4, x_2);
return x_7;
}
else
{
return x_6;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_HashMapImp_find___at_Lean_Elab_Term_elabTerm___spec__5(x_8, x_2);
return x_9;
}
}
}
lean_object* l___private_Init_Lean_Elab_Log_1__resetTraceState___at_Lean_Elab_Term_elabTerm___spec__7___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = l_Lean_Elab_Term_getTraceState___rarg(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 1);
lean_dec(x_6);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_3, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 4);
lean_dec(x_10);
x_11 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_11);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_ctor_get(x_4, 3);
x_16 = lean_ctor_get(x_4, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_17 = l_Lean_TraceState_Inhabited___closed__1;
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_17);
lean_ctor_set(x_18, 5, x_16);
lean_ctor_set(x_3, 0, x_18);
return x_2;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 2);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_3, 4);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_4, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_4, 5);
lean_inc(x_27);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_28 = x_4;
} else {
 lean_dec_ref(x_4);
 x_28 = lean_box(0);
}
x_29 = l_Lean_TraceState_Inhabited___closed__1;
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 6, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set(x_30, 5, x_27);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_19);
lean_ctor_set(x_31, 2, x_20);
lean_ctor_set(x_31, 3, x_21);
lean_ctor_set(x_31, 4, x_22);
lean_ctor_set(x_2, 1, x_31);
return x_2;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
lean_dec(x_2);
x_33 = lean_ctor_get(x_3, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 4);
lean_inc(x_36);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_37 = x_3;
} else {
 lean_dec_ref(x_3);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_4, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_4, 5);
lean_inc(x_42);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_43 = x_4;
} else {
 lean_dec_ref(x_4);
 x_43 = lean_box(0);
}
x_44 = l_Lean_TraceState_Inhabited___closed__1;
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 6, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_39);
lean_ctor_set(x_45, 2, x_40);
lean_ctor_set(x_45, 3, x_41);
lean_ctor_set(x_45, 4, x_44);
lean_ctor_set(x_45, 5, x_42);
if (lean_is_scalar(x_37)) {
 x_46 = lean_alloc_ctor(0, 5, 0);
} else {
 x_46 = x_37;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_33);
lean_ctor_set(x_46, 2, x_34);
lean_ctor_set(x_46, 3, x_35);
lean_ctor_set(x_46, 4, x_36);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_32);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
lean_object* l___private_Init_Lean_Elab_Log_1__resetTraceState___at_Lean_Elab_Term_elabTerm___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Log_1__resetTraceState___at_Lean_Elab_Term_elabTerm___spec__7___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Term_elabTerm___spec__11(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 2);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_box(0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_FileMap_toPosition(x_6, x_8);
x_11 = l_String_splitAux___main___closed__1;
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set(x_12, 4, x_1);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = l_Lean_FileMap_toPosition(x_6, x_14);
x_16 = l_String_splitAux___main___closed__1;
lean_inc(x_7);
x_17 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_9);
lean_ctor_set(x_17, 3, x_16);
lean_ctor_set(x_17, 4, x_1);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_elabTerm___spec__10(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_elabTerm___spec__11(x_3, x_2, x_6, x_4, x_5);
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
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_9, 2, x_13);
x_14 = lean_box(0);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set(x_22, 4, x_20);
x_23 = lean_box(0);
lean_ctor_set(x_7, 1, x_22);
lean_ctor_set(x_7, 0, x_23);
return x_7;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_7, 1);
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_24);
lean_inc(x_25);
lean_dec(x_7);
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
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 lean_ctor_release(x_24, 4);
 x_31 = x_24;
} else {
 lean_dec_ref(x_24);
 x_31 = lean_box(0);
}
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_28);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 5, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_29);
lean_ctor_set(x_33, 4, x_30);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
lean_object* l_Lean_Elab_logInfoAt___at_Lean_Elab_Term_elabTerm___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = l_Lean_Elab_logAt___at_Lean_Elab_Term_elabTerm___spec__10(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = 0;
lean_inc(x_1);
x_14 = l_Lean_Elab_logAt___at_Lean_Elab_Term_elabTerm___spec__10(x_1, x_13, x_10, x_4, x_5);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_3 = x_12;
x_5 = x_15;
goto _start;
}
}
}
lean_object* l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___at_Lean_Elab_Term_elabTerm___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = l_Lean_Elab_Term_getTraceState___rarg(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__12(x_1, x_8, x_9, x_3, x_7);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 4);
lean_dec(x_17);
lean_ctor_set(x_15, 4, x_2);
x_18 = lean_box(0);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_ctor_get(x_15, 2);
x_22 = lean_ctor_get(x_15, 3);
x_23 = lean_ctor_get(x_15, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set(x_24, 4, x_2);
lean_ctor_set(x_24, 5, x_23);
lean_ctor_set(x_12, 0, x_24);
x_25 = lean_box(0);
lean_ctor_set(x_10, 0, x_25);
return x_10;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
x_28 = lean_ctor_get(x_12, 2);
x_29 = lean_ctor_get(x_12, 3);
x_30 = lean_ctor_get(x_12, 4);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_26, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_26, 5);
lean_inc(x_35);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 lean_ctor_release(x_26, 5);
 x_36 = x_26;
} else {
 lean_dec_ref(x_26);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 6, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_37, 2, x_33);
lean_ctor_set(x_37, 3, x_34);
lean_ctor_set(x_37, 4, x_2);
lean_ctor_set(x_37, 5, x_35);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_27);
lean_ctor_set(x_38, 2, x_28);
lean_ctor_set(x_38, 3, x_29);
lean_ctor_set(x_38, 4, x_30);
x_39 = lean_box(0);
lean_ctor_set(x_10, 1, x_38);
lean_ctor_set(x_10, 0, x_39);
return x_10;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_40 = lean_ctor_get(x_10, 1);
lean_inc(x_40);
lean_dec(x_10);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_40, 4);
lean_inc(x_45);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 x_46 = x_40;
} else {
 lean_dec_ref(x_40);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_41, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_41, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_41, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_41, 5);
lean_inc(x_51);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 lean_ctor_release(x_41, 5);
 x_52 = x_41;
} else {
 lean_dec_ref(x_41);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 6, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set(x_53, 3, x_50);
lean_ctor_set(x_53, 4, x_2);
lean_ctor_set(x_53, 5, x_51);
if (lean_is_scalar(x_46)) {
 x_54 = lean_alloc_ctor(0, 5, 0);
} else {
 x_54 = x_46;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_42);
lean_ctor_set(x_54, 2, x_43);
lean_ctor_set(x_54, 3, x_44);
lean_ctor_set(x_54, 4, x_45);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
lean_object* l___private_Init_Lean_Util_Trace_4__checkTraceOption___at_Lean_Elab_Term_elabTerm___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_getOptions(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_List_isEmpty___rarg(x_6);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = l___private_Init_Lean_Util_Trace_3__checkTraceOptionAux___main(x_6, x_1);
lean_dec(x_6);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
uint8_t x_10; lean_object* x_11; 
lean_dec(x_6);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = l_List_isEmpty___rarg(x_12);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l___private_Init_Lean_Util_Trace_3__checkTraceOptionAux___main(x_12, x_1);
lean_dec(x_12);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
}
}
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Elab_Term_elabTerm___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Lean_Elab_Term_addContext(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_6, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_7, 4);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_10);
x_19 = lean_array_push(x_17, x_18);
lean_ctor_set(x_8, 0, x_19);
x_20 = lean_box(0);
lean_ctor_set(x_5, 0, x_20);
return x_5;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_22 = lean_ctor_get(x_8, 0);
lean_inc(x_22);
lean_dec(x_8);
x_23 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_10);
x_24 = lean_array_push(x_22, x_23);
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_21);
lean_ctor_set(x_7, 4, x_25);
x_26 = lean_box(0);
lean_ctor_set(x_5, 0, x_26);
return x_5;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
x_29 = lean_ctor_get(x_7, 2);
x_30 = lean_ctor_get(x_7, 3);
x_31 = lean_ctor_get(x_7, 5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_32 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_33 = lean_ctor_get(x_8, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_34 = x_8;
} else {
 lean_dec_ref(x_8);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_10);
x_36 = lean_array_push(x_33, x_35);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(0, 1, 1);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_32);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_28);
lean_ctor_set(x_38, 2, x_29);
lean_ctor_set(x_38, 3, x_30);
lean_ctor_set(x_38, 4, x_37);
lean_ctor_set(x_38, 5, x_31);
lean_ctor_set(x_6, 0, x_38);
x_39 = lean_box(0);
lean_ctor_set(x_5, 0, x_39);
return x_5;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_40 = lean_ctor_get(x_6, 1);
x_41 = lean_ctor_get(x_6, 2);
x_42 = lean_ctor_get(x_6, 3);
x_43 = lean_ctor_get(x_6, 4);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_6);
x_44 = lean_ctor_get(x_7, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_7, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_7, 5);
lean_inc(x_48);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 x_49 = x_7;
} else {
 lean_dec_ref(x_7);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_51 = lean_ctor_get(x_8, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_52 = x_8;
} else {
 lean_dec_ref(x_8);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_10);
x_54 = lean_array_push(x_51, x_53);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 1, 1);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_50);
if (lean_is_scalar(x_49)) {
 x_56 = lean_alloc_ctor(0, 6, 0);
} else {
 x_56 = x_49;
}
lean_ctor_set(x_56, 0, x_44);
lean_ctor_set(x_56, 1, x_45);
lean_ctor_set(x_56, 2, x_46);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set(x_56, 4, x_55);
lean_ctor_set(x_56, 5, x_48);
x_57 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_40);
lean_ctor_set(x_57, 2, x_41);
lean_ctor_set(x_57, 3, x_42);
lean_ctor_set(x_57, 4, x_43);
x_58 = lean_box(0);
lean_ctor_set(x_5, 1, x_57);
lean_ctor_set(x_5, 0, x_58);
return x_5;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_59 = lean_ctor_get(x_5, 0);
lean_inc(x_59);
lean_dec(x_5);
x_60 = lean_ctor_get(x_6, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_6, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_6, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_6, 4);
lean_inc(x_63);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_64 = x_6;
} else {
 lean_dec_ref(x_6);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_7, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_7, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_7, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_7, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_7, 5);
lean_inc(x_69);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 x_70 = x_7;
} else {
 lean_dec_ref(x_7);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_72 = lean_ctor_get(x_8, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_73 = x_8;
} else {
 lean_dec_ref(x_8);
 x_73 = lean_box(0);
}
x_74 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_59);
x_75 = lean_array_push(x_72, x_74);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(0, 1, 1);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_71);
if (lean_is_scalar(x_70)) {
 x_77 = lean_alloc_ctor(0, 6, 0);
} else {
 x_77 = x_70;
}
lean_ctor_set(x_77, 0, x_65);
lean_ctor_set(x_77, 1, x_66);
lean_ctor_set(x_77, 2, x_67);
lean_ctor_set(x_77, 3, x_68);
lean_ctor_set(x_77, 4, x_76);
lean_ctor_set(x_77, 5, x_69);
if (lean_is_scalar(x_64)) {
 x_78 = lean_alloc_ctor(0, 5, 0);
} else {
 x_78 = x_64;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_60);
lean_ctor_set(x_78, 2, x_61);
lean_ctor_set(x_78, 3, x_62);
lean_ctor_set(x_78, 4, x_63);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
lean_object* _init_l_Lean_Elab_Term_elabTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elaboration function for '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabTerm___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has not been implemented");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabTerm___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__4;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_44 = l_Lean_Elab_Term_getTraceState___rarg(x_4);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_6 = x_47;
goto block_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = l_Lean_Elab_Term_elabTerm___closed__3;
x_50 = l___private_Init_Lean_Util_Trace_4__checkTraceOption___at_Lean_Elab_Term_elabTerm___spec__13(x_49, x_3, x_48);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_6 = x_53;
goto block_43;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
lean_inc(x_1);
x_55 = l_Lean_Syntax_formatStx___main(x_1);
x_56 = l_Lean_Options_empty;
x_57 = l_Lean_Format_pretty(x_55, x_56);
x_58 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__4;
x_61 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Elab_Term_elabTerm___spec__14(x_60, x_59, x_3, x_54);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_6 = x_62;
goto block_43;
}
}
block_43:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_Elab_Term_termElabAttribute;
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_PersistentEnvExtension_getState___rarg(x_8, x_10);
lean_dec(x_10);
x_12 = l_Lean_SMap_find___at_Lean_Elab_Term_elabTerm___spec__1(x_11, x_5);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_System_FilePath_dirName___closed__1;
x_14 = l_Lean_Name_toStringWithSep___main(x_13, x_5);
x_15 = l_Lean_Elab_Term_elabTerm___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lean_Elab_Term_elabTerm___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
x_22 = l_Lean_Syntax_getPos(x_1);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_apply_4(x_21, x_1, x_2, x_3, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Init_Lean_Elab_Log_1__resetTraceState___at_Lean_Elab_Term_elabTerm___spec__7___rarg(x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_3);
x_28 = lean_apply_4(x_21, x_1, x_2, x_3, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___at_Lean_Elab_Term_elabTerm___spec__8(x_24, x_26, x_3, x_30);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_29);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec(x_28);
x_38 = l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___at_Lean_Elab_Term_elabTerm___spec__8(x_24, x_26, x_3, x_37);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_36);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = l_Lean_Elab_Term_withNode___rarg___closed__2;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_4);
return x_64;
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabTerm___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabTerm___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTerm___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTerm___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentHashMap_find___at_Lean_Elab_Term_elabTerm___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find___at_Lean_Elab_Term_elabTerm___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_Term_elabTerm___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Elab_Term_elabTerm___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find___at_Lean_Elab_Term_elabTerm___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find___at_Lean_Elab_Term_elabTerm___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find___at_Lean_Elab_Term_elabTerm___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find___at_Lean_Elab_Term_elabTerm___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Log_1__resetTraceState___at_Lean_Elab_Term_elabTerm___spec__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Log_1__resetTraceState___at_Lean_Elab_Term_elabTerm___spec__7(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Term_elabTerm___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_elabTerm___spec__11(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_elabTerm___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_logAt___at_Lean_Elab_Term_elabTerm___spec__10(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Lean_Elab_logInfoAt___at_Lean_Elab_Term_elabTerm___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_logInfoAt___at_Lean_Elab_Term_elabTerm___spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__12(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___at_Lean_Elab_Term_elabTerm___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___at_Lean_Elab_Term_elabTerm___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Util_Trace_4__checkTraceOption___at_Lean_Elab_Term_elabTerm___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Util_Trace_4__checkTraceOption___at_Lean_Elab_Term_elabTerm___spec__13(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Elab_Term_elabTerm___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Elab_Term_elabTerm___spec__14(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Term_ensureType___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_ensureType___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_getPos___at_Lean_Elab_Term_ensureType___spec__3(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_logAt___at_Lean_Elab_Term_elabTerm___spec__10(x_7, x_2, x_3, x_4, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_ensureType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = 2;
x_8 = l_Lean_Elab_log___at_Lean_Elab_Term_ensureType___spec__2(x_1, x_7, x_6, x_3, x_4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = lean_box(5);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_box(5);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* l_Lean_Elab_Term_ensureType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Elab_Term_inferType(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
x_8 = l_Lean_Elab_Term_whnf(x_6, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Expr_isSort(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_free_object(x_8);
x_13 = l_Lean_Elab_Term_mkFreshLevelMVar___rarg(x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_mkSort(x_14);
lean_inc(x_3);
x_17 = l_Lean_Elab_Term_isDefEq(x_10, x_16, x_3, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_Meta_Exception_toStr___closed__7;
x_22 = l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_ensureType___spec__1(x_1, x_21, x_3, x_20);
lean_dec(x_3);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_17, 0);
lean_dec(x_24);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
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
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_33 = l_Lean_Expr_isSort(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = l_Lean_Elab_Term_mkFreshLevelMVar___rarg(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_mkSort(x_35);
lean_inc(x_3);
x_38 = l_Lean_Elab_Term_isDefEq(x_31, x_37, x_3, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_2);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Meta_Exception_toStr___closed__7;
x_43 = l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_ensureType___spec__1(x_1, x_42, x_3, x_41);
lean_dec(x_3);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_3);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_45 = x_38;
} else {
 lean_dec_ref(x_38);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_ctor_get(x_38, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_49 = x_38;
} else {
 lean_dec_ref(x_38);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; 
lean_dec(x_31);
lean_dec(x_3);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_32);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_8);
if (x_52 == 0)
{
return x_8;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_8, 0);
x_54 = lean_ctor_get(x_8, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_8);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_5);
if (x_56 == 0)
{
return x_5;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_5, 0);
x_58 = lean_ctor_get(x_5, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_5);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Term_ensureType___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getPos___at_Lean_Elab_Term_ensureType___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_ensureType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_log___at_Lean_Elab_Term_ensureType___spec__2(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_ensureType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_ensureType___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_Elab_Term_mkFreshLevelMVar___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_mkSort(x_5);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_Elab_Term_elabTerm(x_1, x_8, x_2, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Term_ensureType(x_1, x_10, x_2, x_11);
lean_dec(x_1);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
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
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
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
x_2 = l_Lean_Parser_Term_prop___elambda__1___rarg___closed__2;
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
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
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
x_2 = l_Lean_Parser_Term_sort___elambda__1___rarg___closed__2;
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
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
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
x_2 = l_Lean_Parser_Term_type___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabHole___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = l_Lean_Elab_Term_mkFreshLevelMVar___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_mkSort(x_5);
x_8 = lean_box(0);
x_9 = 0;
x_10 = l_Lean_Elab_Term_mkFreshExprMVar(x_7, x_8, x_9, x_2, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = 0;
x_14 = l_Lean_Elab_Term_mkFreshExprMVar(x_11, x_12, x_13, x_2, x_3);
return x_14;
}
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
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabHole___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabHole(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_a");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___rarg(lean_object* x_1) {
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
x_6 = l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___rarg___closed__2;
x_7 = l_Lean_Name_appendIndexAfter(x_6, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_ctor_get(x_1, 4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_13, x_14);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_15);
x_17 = l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___rarg___closed__2;
x_18 = l_Lean_Name_appendIndexAfter(x_17, x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_inst");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___rarg(lean_object* x_1) {
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
x_6 = l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___rarg___closed__2;
x_7 = l_Lean_Name_appendIndexAfter(x_6, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_ctor_get(x_1, 4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_12, x_14);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_16, 4, x_13);
x_17 = l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___rarg___closed__2;
x_18 = l_Lean_Name_appendIndexAfter(x_17, x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkHole___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Name_appendIndexAfter___closed__1;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkHole___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_FileMap_ofString___closed__1;
x_2 = l_Lean_Elab_Term_mkHole___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_mkHole___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1;
x_2 = l_Lean_Elab_Term_mkHole___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_mkHole() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_mkHole___closed__3;
return x_1;
}
}
lean_object* l___private_Init_Lean_Elab_Term_3__expandBinderType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Syntax_getNumArgs(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_mkHole;
return x_7;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_3__expandBinderType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Term_3__expandBinderType(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_4__expandBinderIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Syntax_getKind(x_1);
x_5 = l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1;
x_6 = lean_name_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___rarg(x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_mkIdentFrom(x_1, x_10);
lean_dec(x_1);
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
x_14 = l_Lean_mkIdentFrom(x_1, x_12);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_4__expandBinderIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Term_4__expandBinderIdent(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Term_5__expandOptIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Syntax_getNumArgs(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Syntax_getArg(x_1, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___rarg(x_3);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_mkIdentFrom(x_1, x_11);
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
x_15 = l_Lean_mkIdentFrom(x_1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_5__expandOptIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Term_5__expandOptIdent(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_6__matchBinder___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = x_3;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_array_fget(x_3, x_2);
x_12 = lean_box(0);
lean_inc(x_11);
x_13 = x_12;
x_14 = lean_array_fset(x_3, x_2, x_13);
lean_inc(x_11);
x_15 = l___private_Init_Lean_Elab_Term_4__expandBinderIdent(x_11, x_4, x_5);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = x_19;
x_23 = lean_array_fset(x_14, x_2, x_22);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_23;
x_5 = x_17;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_6__matchBinder___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = x_3;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_array_fget(x_3, x_2);
x_12 = lean_box(0);
lean_inc(x_11);
x_13 = x_12;
x_14 = lean_array_fset(x_3, x_2, x_13);
lean_inc(x_11);
x_15 = l___private_Init_Lean_Elab_Term_4__expandBinderIdent(x_11, x_4, x_5);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 0;
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = x_19;
x_23 = lean_array_fset(x_14, x_2, x_22);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_23;
x_5 = x_17;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_6__matchBinder___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_7 = l_Array_empty___closed__1;
x_8 = x_2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_array_fget(x_2, x_1);
x_11 = lean_box(0);
lean_inc(x_10);
x_12 = x_11;
x_13 = lean_array_fset(x_2, x_1, x_12);
lean_inc(x_10);
x_14 = l___private_Init_Lean_Elab_Term_4__expandBinderIdent(x_10, x_3, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Term_mkHole;
x_18 = 0;
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_1, x_20);
x_22 = x_19;
x_23 = lean_array_fset(x_13, x_1, x_22);
lean_dec(x_1);
x_1 = x_21;
x_2 = x_23;
x_4 = x_16;
goto _start;
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_6__matchBinder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("term elaborator failed, unexpected binder syntax");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_6__matchBinder___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_6__matchBinder___closed__1;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_6__matchBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Parser_Term_simpleBinder___elambda__1___closed__2;
x_7 = lean_name_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
x_9 = lean_name_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__2;
x_11 = lean_name_eq(x_4, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Parser_Term_instBinder___elambda__1___rarg___closed__2;
x_13 = lean_name_eq(x_4, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l___private_Init_Lean_Elab_Term_6__matchBinder___closed__2;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = l_Lean_stxInh;
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_array_get(x_16, x_5, x_17);
x_19 = l___private_Init_Lean_Elab_Term_5__expandOptIdent(x_18, x_2, x_3);
lean_dec(x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_array_get(x_16, x_5, x_22);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_24);
x_26 = l_Lean_FileMap_ofString___closed__1;
x_27 = lean_array_push(x_26, x_25);
lean_ctor_set(x_19, 0, x_27);
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_array_get(x_16, x_5, x_30);
x_32 = 3;
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_32);
x_34 = l_Lean_FileMap_ofString___closed__1;
x_35 = lean_array_push(x_34, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = l_Lean_stxInh;
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_array_get(x_37, x_5, x_38);
x_40 = l_Lean_Syntax_getArgs(x_39);
lean_dec(x_39);
x_41 = lean_unsigned_to_nat(2u);
x_42 = lean_array_get(x_37, x_5, x_41);
x_43 = l___private_Init_Lean_Elab_Term_3__expandBinderType(x_42);
lean_dec(x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_6__matchBinder___spec__1(x_43, x_44, x_40, x_2, x_3);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = l_Lean_stxInh;
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_array_get(x_46, x_5, x_47);
x_49 = l_Lean_Syntax_getArgs(x_48);
lean_dec(x_48);
x_50 = lean_unsigned_to_nat(2u);
x_51 = lean_array_get(x_46, x_5, x_50);
x_52 = l___private_Init_Lean_Elab_Term_3__expandBinderType(x_51);
lean_dec(x_51);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_6__matchBinder___spec__2(x_52, x_53, x_49, x_2, x_3);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = l_Lean_stxInh;
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_array_get(x_55, x_5, x_56);
x_58 = l_Lean_Syntax_getArgs(x_57);
lean_dec(x_57);
x_59 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_6__matchBinder___spec__3(x_56, x_58, x_2, x_3);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Elab_Term_withNode___rarg___closed__2;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_3);
return x_61;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_6__matchBinder___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_6__matchBinder___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_6__matchBinder___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_6__matchBinder___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_6__matchBinder___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_6__matchBinder___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_Term_6__matchBinder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Term_6__matchBinder(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_13, 2, x_2);
lean_ctor_set(x_4, 0, x_13);
x_14 = lean_apply_2(x_3, x_4, x_5);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_4, 2);
x_18 = lean_ctor_get(x_4, 3);
x_19 = lean_ctor_get(x_4, 4);
x_20 = lean_ctor_get(x_4, 5);
x_21 = lean_ctor_get(x_4, 6);
x_22 = lean_ctor_get(x_4, 7);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_24 = x_15;
} else {
 lean_dec_ref(x_15);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 3, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_1);
lean_ctor_set(x_25, 2, x_2);
x_26 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_17);
lean_ctor_set(x_26, 3, x_18);
lean_ctor_set(x_26, 4, x_19);
lean_ctor_set(x_26, 5, x_20);
lean_ctor_set(x_26, 6, x_21);
lean_ctor_set(x_26, 7, x_22);
x_27 = lean_apply_2(x_3, x_26, x_5);
return x_27;
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_32 = lean_ctor_get(x_1, 1);
x_33 = lean_ctor_get(x_1, 2);
x_34 = lean_ctor_get(x_1, 3);
x_35 = lean_ctor_get(x_1, 4);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 4);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 5);
lean_inc(x_40);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_41 = x_2;
} else {
 lean_dec_ref(x_2);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_44 = x_3;
} else {
 lean_dec_ref(x_3);
 x_44 = lean_box(0);
}
x_45 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 3, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_45);
if (lean_is_scalar(x_41)) {
 x_47 = lean_alloc_ctor(0, 6, 0);
} else {
 x_47 = x_41;
}
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_37);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set(x_47, 3, x_38);
lean_ctor_set(x_47, 4, x_39);
lean_ctor_set(x_47, 5, x_40);
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_32);
lean_ctor_set(x_48, 2, x_33);
lean_ctor_set(x_48, 3, x_34);
lean_ctor_set(x_48, 4, x_35);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_34 = lean_ctor_get(x_10, 1);
x_35 = lean_ctor_get(x_10, 2);
x_36 = lean_ctor_get(x_10, 3);
x_37 = lean_ctor_get(x_10, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_10);
x_38 = lean_ctor_get(x_11, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_11, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_11, 4);
lean_inc(x_41);
x_42 = lean_ctor_get(x_11, 5);
lean_inc(x_42);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_43 = x_11;
} else {
 lean_dec_ref(x_11);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_12, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_12, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_46 = x_12;
} else {
 lean_dec_ref(x_12);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 3, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_6);
if (lean_is_scalar(x_43)) {
 x_48 = lean_alloc_ctor(0, 6, 0);
} else {
 x_48 = x_43;
}
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_39);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_40);
lean_ctor_set(x_48, 4, x_41);
lean_ctor_set(x_48, 5, x_42);
x_49 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_34);
lean_ctor_set(x_49, 2, x_35);
lean_ctor_set(x_49, 3, x_36);
lean_ctor_set(x_49, 4, x_37);
lean_ctor_set(x_9, 1, x_49);
return x_9;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_50 = lean_ctor_get(x_9, 0);
lean_inc(x_50);
lean_dec(x_9);
x_51 = lean_ctor_get(x_10, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_10, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_10, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_10, 4);
lean_inc(x_54);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 x_55 = x_10;
} else {
 lean_dec_ref(x_10);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_11, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_11, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_11, 3);
lean_inc(x_58);
x_59 = lean_ctor_get(x_11, 4);
lean_inc(x_59);
x_60 = lean_ctor_get(x_11, 5);
lean_inc(x_60);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_61 = x_11;
} else {
 lean_dec_ref(x_11);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_12, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_12, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_64 = x_12;
} else {
 lean_dec_ref(x_12);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 3, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_65, 2, x_6);
if (lean_is_scalar(x_61)) {
 x_66 = lean_alloc_ctor(0, 6, 0);
} else {
 x_66 = x_61;
}
lean_ctor_set(x_66, 0, x_56);
lean_ctor_set(x_66, 1, x_57);
lean_ctor_set(x_66, 2, x_65);
lean_ctor_set(x_66, 3, x_58);
lean_ctor_set(x_66, 4, x_59);
lean_ctor_set(x_66, 5, x_60);
if (lean_is_scalar(x_55)) {
 x_67 = lean_alloc_ctor(0, 5, 0);
} else {
 x_67 = x_55;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_51);
lean_ctor_set(x_67, 2, x_52);
lean_ctor_set(x_67, 3, x_53);
lean_ctor_set(x_67, 4, x_54);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_50);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_9, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 2);
lean_inc(x_71);
x_72 = !lean_is_exclusive(x_9);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_9, 1);
lean_dec(x_73);
x_74 = !lean_is_exclusive(x_69);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_69, 0);
lean_dec(x_75);
x_76 = !lean_is_exclusive(x_70);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_70, 2);
lean_dec(x_77);
x_78 = !lean_is_exclusive(x_71);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_71, 2);
lean_dec(x_79);
lean_ctor_set(x_71, 2, x_6);
return x_9;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_71, 0);
x_81 = lean_ctor_get(x_71, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_71);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_6);
lean_ctor_set(x_70, 2, x_82);
return x_9;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_83 = lean_ctor_get(x_70, 0);
x_84 = lean_ctor_get(x_70, 1);
x_85 = lean_ctor_get(x_70, 3);
x_86 = lean_ctor_get(x_70, 4);
x_87 = lean_ctor_get(x_70, 5);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_70);
x_88 = lean_ctor_get(x_71, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_71, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 x_90 = x_71;
} else {
 lean_dec_ref(x_71);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 3, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
lean_ctor_set(x_91, 2, x_6);
x_92 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_84);
lean_ctor_set(x_92, 2, x_91);
lean_ctor_set(x_92, 3, x_85);
lean_ctor_set(x_92, 4, x_86);
lean_ctor_set(x_92, 5, x_87);
lean_ctor_set(x_69, 0, x_92);
return x_9;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_93 = lean_ctor_get(x_69, 1);
x_94 = lean_ctor_get(x_69, 2);
x_95 = lean_ctor_get(x_69, 3);
x_96 = lean_ctor_get(x_69, 4);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_69);
x_97 = lean_ctor_get(x_70, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_70, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_70, 3);
lean_inc(x_99);
x_100 = lean_ctor_get(x_70, 4);
lean_inc(x_100);
x_101 = lean_ctor_get(x_70, 5);
lean_inc(x_101);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 lean_ctor_release(x_70, 2);
 lean_ctor_release(x_70, 3);
 lean_ctor_release(x_70, 4);
 lean_ctor_release(x_70, 5);
 x_102 = x_70;
} else {
 lean_dec_ref(x_70);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_71, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_71, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 x_105 = x_71;
} else {
 lean_dec_ref(x_71);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 3, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
lean_ctor_set(x_106, 2, x_6);
if (lean_is_scalar(x_102)) {
 x_107 = lean_alloc_ctor(0, 6, 0);
} else {
 x_107 = x_102;
}
lean_ctor_set(x_107, 0, x_97);
lean_ctor_set(x_107, 1, x_98);
lean_ctor_set(x_107, 2, x_106);
lean_ctor_set(x_107, 3, x_99);
lean_ctor_set(x_107, 4, x_100);
lean_ctor_set(x_107, 5, x_101);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_93);
lean_ctor_set(x_108, 2, x_94);
lean_ctor_set(x_108, 3, x_95);
lean_ctor_set(x_108, 4, x_96);
lean_ctor_set(x_9, 1, x_108);
return x_9;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_109 = lean_ctor_get(x_9, 0);
lean_inc(x_109);
lean_dec(x_9);
x_110 = lean_ctor_get(x_69, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_69, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_69, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_69, 4);
lean_inc(x_113);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 lean_ctor_release(x_69, 2);
 lean_ctor_release(x_69, 3);
 lean_ctor_release(x_69, 4);
 x_114 = x_69;
} else {
 lean_dec_ref(x_69);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_70, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_70, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_70, 3);
lean_inc(x_117);
x_118 = lean_ctor_get(x_70, 4);
lean_inc(x_118);
x_119 = lean_ctor_get(x_70, 5);
lean_inc(x_119);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 lean_ctor_release(x_70, 2);
 lean_ctor_release(x_70, 3);
 lean_ctor_release(x_70, 4);
 lean_ctor_release(x_70, 5);
 x_120 = x_70;
} else {
 lean_dec_ref(x_70);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_71, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_71, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 x_123 = x_71;
} else {
 lean_dec_ref(x_71);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(0, 3, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
lean_ctor_set(x_124, 2, x_6);
if (lean_is_scalar(x_120)) {
 x_125 = lean_alloc_ctor(0, 6, 0);
} else {
 x_125 = x_120;
}
lean_ctor_set(x_125, 0, x_115);
lean_ctor_set(x_125, 1, x_116);
lean_ctor_set(x_125, 2, x_124);
lean_ctor_set(x_125, 3, x_117);
lean_ctor_set(x_125, 4, x_118);
lean_ctor_set(x_125, 5, x_119);
if (lean_is_scalar(x_114)) {
 x_126 = lean_alloc_ctor(0, 5, 0);
} else {
 x_126 = x_114;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_110);
lean_ctor_set(x_126, 2, x_111);
lean_ctor_set(x_126, 3, x_112);
lean_ctor_set(x_126, 4, x_113);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_109);
lean_ctor_set(x_127, 1, x_126);
return x_127;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_4);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_2, x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_11, 1);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_13, 2);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_14, 2);
lean_dec(x_22);
lean_ctor_set(x_14, 2, x_8);
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_8);
lean_ctor_set(x_13, 2, x_25);
return x_11;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
x_28 = lean_ctor_get(x_13, 3);
x_29 = lean_ctor_get(x_13, 4);
x_30 = lean_ctor_get(x_13, 5);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_33 = x_14;
} else {
 lean_dec_ref(x_14);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 3, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_8);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_27);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_28);
lean_ctor_set(x_35, 4, x_29);
lean_ctor_set(x_35, 5, x_30);
lean_ctor_set(x_12, 0, x_35);
return x_11;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_36 = lean_ctor_get(x_12, 1);
x_37 = lean_ctor_get(x_12, 2);
x_38 = lean_ctor_get(x_12, 3);
x_39 = lean_ctor_get(x_12, 4);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_12);
x_40 = lean_ctor_get(x_13, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_13, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_13, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_13, 4);
lean_inc(x_43);
x_44 = lean_ctor_get(x_13, 5);
lean_inc(x_44);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 x_45 = x_13;
} else {
 lean_dec_ref(x_13);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_14, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_14, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_48 = x_14;
} else {
 lean_dec_ref(x_14);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 3, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_8);
if (lean_is_scalar(x_45)) {
 x_50 = lean_alloc_ctor(0, 6, 0);
} else {
 x_50 = x_45;
}
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_41);
lean_ctor_set(x_50, 2, x_49);
lean_ctor_set(x_50, 3, x_42);
lean_ctor_set(x_50, 4, x_43);
lean_ctor_set(x_50, 5, x_44);
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_36);
lean_ctor_set(x_51, 2, x_37);
lean_ctor_set(x_51, 3, x_38);
lean_ctor_set(x_51, 4, x_39);
lean_ctor_set(x_11, 1, x_51);
return x_11;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_52 = lean_ctor_get(x_11, 0);
lean_inc(x_52);
lean_dec(x_11);
x_53 = lean_ctor_get(x_12, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_12, 2);
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
x_58 = lean_ctor_get(x_13, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_13, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_13, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_13, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_13, 5);
lean_inc(x_62);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 x_63 = x_13;
} else {
 lean_dec_ref(x_13);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_14, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_14, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_66 = x_14;
} else {
 lean_dec_ref(x_14);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 3, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set(x_67, 2, x_8);
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
 x_69 = lean_alloc_ctor(0, 5, 0);
} else {
 x_69 = x_57;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_53);
lean_ctor_set(x_69, 2, x_54);
lean_ctor_set(x_69, 3, x_55);
lean_ctor_set(x_69, 4, x_56);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_52);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_11, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 2);
lean_inc(x_73);
x_74 = !lean_is_exclusive(x_11);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_11, 1);
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
lean_ctor_set(x_73, 2, x_8);
return x_11;
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
lean_ctor_set(x_84, 2, x_8);
lean_ctor_set(x_72, 2, x_84);
return x_11;
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
lean_ctor_set(x_93, 2, x_8);
x_94 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_94, 0, x_85);
lean_ctor_set(x_94, 1, x_86);
lean_ctor_set(x_94, 2, x_93);
lean_ctor_set(x_94, 3, x_87);
lean_ctor_set(x_94, 4, x_88);
lean_ctor_set(x_94, 5, x_89);
lean_ctor_set(x_71, 0, x_94);
return x_11;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_95 = lean_ctor_get(x_71, 1);
x_96 = lean_ctor_get(x_71, 2);
x_97 = lean_ctor_get(x_71, 3);
x_98 = lean_ctor_get(x_71, 4);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_71);
x_99 = lean_ctor_get(x_72, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_72, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_72, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_72, 4);
lean_inc(x_102);
x_103 = lean_ctor_get(x_72, 5);
lean_inc(x_103);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 lean_ctor_release(x_72, 5);
 x_104 = x_72;
} else {
 lean_dec_ref(x_72);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_73, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_73, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_107 = x_73;
} else {
 lean_dec_ref(x_73);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 3, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
lean_ctor_set(x_108, 2, x_8);
if (lean_is_scalar(x_104)) {
 x_109 = lean_alloc_ctor(0, 6, 0);
} else {
 x_109 = x_104;
}
lean_ctor_set(x_109, 0, x_99);
lean_ctor_set(x_109, 1, x_100);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set(x_109, 3, x_101);
lean_ctor_set(x_109, 4, x_102);
lean_ctor_set(x_109, 5, x_103);
x_110 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_95);
lean_ctor_set(x_110, 2, x_96);
lean_ctor_set(x_110, 3, x_97);
lean_ctor_set(x_110, 4, x_98);
lean_ctor_set(x_11, 1, x_110);
return x_11;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_111 = lean_ctor_get(x_11, 0);
lean_inc(x_111);
lean_dec(x_11);
x_112 = lean_ctor_get(x_71, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_71, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_71, 3);
lean_inc(x_114);
x_115 = lean_ctor_get(x_71, 4);
lean_inc(x_115);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 x_116 = x_71;
} else {
 lean_dec_ref(x_71);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_72, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_72, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_72, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_72, 4);
lean_inc(x_120);
x_121 = lean_ctor_get(x_72, 5);
lean_inc(x_121);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 lean_ctor_release(x_72, 5);
 x_122 = x_72;
} else {
 lean_dec_ref(x_72);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_73, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_73, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_125 = x_73;
} else {
 lean_dec_ref(x_73);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(0, 3, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
lean_ctor_set(x_126, 2, x_8);
if (lean_is_scalar(x_122)) {
 x_127 = lean_alloc_ctor(0, 6, 0);
} else {
 x_127 = x_122;
}
lean_ctor_set(x_127, 0, x_117);
lean_ctor_set(x_127, 1, x_118);
lean_ctor_set(x_127, 2, x_126);
lean_ctor_set(x_127, 3, x_119);
lean_ctor_set(x_127, 4, x_120);
lean_ctor_set(x_127, 5, x_121);
if (lean_is_scalar(x_116)) {
 x_128 = lean_alloc_ctor(0, 5, 0);
} else {
 x_128 = x_116;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_112);
lean_ctor_set(x_128, 2, x_113);
lean_ctor_set(x_128, 3, x_114);
lean_ctor_set(x_128, 4, x_115);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_111);
lean_ctor_set(x_129, 1, x_128);
return x_129;
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
lean_object* l_Lean_Elab_Term_mkFreshId___rarg(lean_object* x_1) {
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = lean_ctor_get(x_1, 4);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_1);
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 4);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 5);
lean_inc(x_44);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_45 = x_2;
} else {
 lean_dec_ref(x_2);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_48 = x_3;
} else {
 lean_dec_ref(x_3);
 x_48 = lean_box(0);
}
lean_inc(x_47);
lean_inc(x_46);
x_49 = lean_name_mk_numeral(x_46, x_47);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_47, x_50);
lean_dec(x_47);
if (lean_is_scalar(x_48)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_48;
}
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_51);
if (lean_is_scalar(x_45)) {
 x_53 = lean_alloc_ctor(0, 6, 0);
} else {
 x_53 = x_45;
}
lean_ctor_set(x_53, 0, x_40);
lean_ctor_set(x_53, 1, x_41);
lean_ctor_set(x_53, 2, x_42);
lean_ctor_set(x_53, 3, x_52);
lean_ctor_set(x_53, 4, x_43);
lean_ctor_set(x_53, 5, x_44);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_36);
lean_ctor_set(x_54, 2, x_37);
lean_ctor_set(x_54, 3, x_38);
lean_ctor_set(x_54, 4, x_39);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_mkFreshId___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_mkFreshId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_mkFreshId(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_7__elabBinderViews___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_fget(x_1, x_2);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_6, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_14, 1);
lean_dec(x_20);
lean_inc(x_5);
lean_inc(x_4);
lean_ctor_set(x_14, 2, x_5);
lean_ctor_set(x_14, 1, x_4);
lean_inc(x_6);
x_21 = l_Lean_Elab_Term_elabType(x_15, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Term_mkFreshId___rarg(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_25);
x_27 = l_Lean_mkFVar(x_25);
lean_inc(x_27);
x_28 = lean_array_push(x_3, x_27);
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
x_30 = l_Lean_Syntax_getId(x_29);
lean_dec(x_29);
x_31 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
lean_inc(x_22);
x_32 = lean_local_ctx_mk_local_decl(x_4, x_25, x_30, x_22, x_31);
lean_inc(x_6);
x_33 = l_Lean_Elab_Term_isClass(x_22, x_6, x_26);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_27);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_2, x_36);
lean_dec(x_2);
x_2 = x_37;
x_3 = x_28;
x_4 = x_32;
x_7 = x_35;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
x_41 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_39);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_27);
x_44 = lean_array_push(x_5, x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_2, x_45);
lean_dec(x_2);
x_2 = x_46;
x_3 = x_28;
x_4 = x_32;
x_5 = x_44;
x_7 = x_42;
goto _start;
}
}
else
{
uint8_t x_48; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_33);
if (x_48 == 0)
{
return x_33;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_33, 0);
x_50 = lean_ctor_get(x_33, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_33);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_6);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_21);
if (x_52 == 0)
{
return x_21;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_21, 0);
x_54 = lean_ctor_get(x_21, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_21);
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
x_56 = lean_ctor_get(x_14, 0);
lean_inc(x_56);
lean_dec(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_4);
lean_ctor_set(x_57, 2, x_5);
lean_ctor_set(x_6, 0, x_57);
lean_inc(x_6);
x_58 = l_Lean_Elab_Term_elabType(x_15, x_6, x_7);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Elab_Term_mkFreshId___rarg(x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_62);
x_64 = l_Lean_mkFVar(x_62);
lean_inc(x_64);
x_65 = lean_array_push(x_3, x_64);
x_66 = lean_ctor_get(x_13, 0);
lean_inc(x_66);
x_67 = l_Lean_Syntax_getId(x_66);
lean_dec(x_66);
x_68 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
lean_inc(x_59);
x_69 = lean_local_ctx_mk_local_decl(x_4, x_62, x_67, x_59, x_68);
lean_inc(x_6);
x_70 = l_Lean_Elab_Term_isClass(x_59, x_6, x_63);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_add(x_2, x_73);
lean_dec(x_2);
x_2 = x_74;
x_3 = x_65;
x_4 = x_69;
x_7 = x_72;
goto _start;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_dec(x_70);
x_77 = lean_ctor_get(x_71, 0);
lean_inc(x_77);
lean_dec(x_71);
x_78 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_76);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_64);
x_81 = lean_array_push(x_5, x_80);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_2, x_82);
lean_dec(x_2);
x_2 = x_83;
x_3 = x_65;
x_4 = x_69;
x_5 = x_81;
x_7 = x_79;
goto _start;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_69);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_85 = lean_ctor_get(x_70, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_70, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_87 = x_70;
} else {
 lean_dec_ref(x_70);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_6);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_89 = lean_ctor_get(x_58, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_58, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_91 = x_58;
} else {
 lean_dec_ref(x_58);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_93 = lean_ctor_get(x_6, 1);
x_94 = lean_ctor_get(x_6, 2);
x_95 = lean_ctor_get(x_6, 3);
x_96 = lean_ctor_get(x_6, 4);
x_97 = lean_ctor_get(x_6, 5);
x_98 = lean_ctor_get(x_6, 6);
x_99 = lean_ctor_get(x_6, 7);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_6);
x_100 = lean_ctor_get(x_14, 0);
lean_inc(x_100);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_101 = x_14;
} else {
 lean_dec_ref(x_14);
 x_101 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_4);
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 3, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_4);
lean_ctor_set(x_102, 2, x_5);
x_103 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_93);
lean_ctor_set(x_103, 2, x_94);
lean_ctor_set(x_103, 3, x_95);
lean_ctor_set(x_103, 4, x_96);
lean_ctor_set(x_103, 5, x_97);
lean_ctor_set(x_103, 6, x_98);
lean_ctor_set(x_103, 7, x_99);
lean_inc(x_103);
x_104 = l_Lean_Elab_Term_elabType(x_15, x_103, x_7);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Elab_Term_mkFreshId___rarg(x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
lean_inc(x_108);
x_110 = l_Lean_mkFVar(x_108);
lean_inc(x_110);
x_111 = lean_array_push(x_3, x_110);
x_112 = lean_ctor_get(x_13, 0);
lean_inc(x_112);
x_113 = l_Lean_Syntax_getId(x_112);
lean_dec(x_112);
x_114 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
lean_inc(x_105);
x_115 = lean_local_ctx_mk_local_decl(x_4, x_108, x_113, x_105, x_114);
lean_inc(x_103);
x_116 = l_Lean_Elab_Term_isClass(x_105, x_103, x_109);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_110);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_nat_add(x_2, x_119);
lean_dec(x_2);
x_2 = x_120;
x_3 = x_111;
x_4 = x_115;
x_6 = x_103;
x_7 = x_118;
goto _start;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_122 = lean_ctor_get(x_116, 1);
lean_inc(x_122);
lean_dec(x_116);
x_123 = lean_ctor_get(x_117, 0);
lean_inc(x_123);
lean_dec(x_117);
x_124 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_122);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_110);
x_127 = lean_array_push(x_5, x_126);
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_nat_add(x_2, x_128);
lean_dec(x_2);
x_2 = x_129;
x_3 = x_111;
x_4 = x_115;
x_5 = x_127;
x_6 = x_103;
x_7 = x_125;
goto _start;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_115);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_103);
lean_dec(x_5);
lean_dec(x_2);
x_131 = lean_ctor_get(x_116, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_116, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_133 = x_116;
} else {
 lean_dec_ref(x_116);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_103);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_135 = lean_ctor_get(x_104, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_104, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_137 = x_104;
} else {
 lean_dec_ref(x_104);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_7__elabBinderViews___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Term_7__elabBinderViews___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Term_7__elabBinderViews(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Term_7__elabBinderViews___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Term_7__elabBinderViews___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Term_7__elabBinderViews(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Term_8__elabBindersAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_1, x_2);
x_14 = l___private_Init_Lean_Elab_Term_6__matchBinder(x_13, x_6, x_7);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_18 = l___private_Init_Lean_Elab_Term_7__elabBinderViews___main(x_15, x_17, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_2, x_25);
lean_dec(x_2);
x_2 = x_26;
x_3 = x_22;
x_4 = x_23;
x_5 = x_24;
x_7 = x_21;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_6);
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
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_8__elabBindersAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Term_8__elabBindersAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Term_8__elabBindersAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Term_8__elabBindersAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Term_8__elabBindersAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Term_8__elabBindersAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Lean_Elab_Term_getLCtx(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Term_getLocalInsts(x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_empty___closed__1;
lean_inc(x_3);
lean_inc(x_9);
x_13 = l___private_Init_Lean_Elab_Term_8__elabBindersAux___main(x_1, x_11, x_12, x_6, x_9, x_3, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_array_get_size(x_9);
lean_dec(x_9);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 2);
lean_dec(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_dec(x_27);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 1, x_18);
x_28 = lean_apply_3(x_2, x_17, x_3, x_16);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_18);
lean_ctor_set(x_30, 2, x_19);
lean_ctor_set(x_3, 0, x_30);
x_31 = lean_apply_3(x_2, x_17, x_3, x_16);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_32 = lean_ctor_get(x_3, 0);
x_33 = lean_ctor_get(x_3, 1);
x_34 = lean_ctor_get(x_3, 2);
x_35 = lean_ctor_get(x_3, 3);
x_36 = lean_ctor_get(x_3, 4);
x_37 = lean_ctor_get(x_3, 5);
x_38 = lean_ctor_get(x_3, 6);
x_39 = lean_ctor_get(x_3, 7);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_3);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 x_41 = x_32;
} else {
 lean_dec_ref(x_32);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 3, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_18);
lean_ctor_set(x_42, 2, x_19);
x_43 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
lean_ctor_set(x_43, 2, x_34);
lean_ctor_set(x_43, 3, x_35);
lean_ctor_set(x_43, 4, x_36);
lean_ctor_set(x_43, 5, x_37);
lean_ctor_set(x_43, 6, x_38);
lean_ctor_set(x_43, 7, x_39);
x_44 = lean_apply_3(x_2, x_17, x_43, x_16);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_16, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 2);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_46, 2);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_16);
x_49 = lean_ctor_get(x_3, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_3);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_3, 0);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_49, 1);
lean_dec(x_55);
lean_ctor_set(x_49, 2, x_19);
lean_ctor_set(x_49, 1, x_18);
x_56 = lean_apply_3(x_2, x_17, x_3, x_50);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 2);
lean_inc(x_59);
x_60 = !lean_is_exclusive(x_56);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_56, 1);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_57, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_58);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_58, 2);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_59);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_59, 2);
lean_dec(x_67);
lean_ctor_set(x_59, 2, x_47);
return x_56;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_59, 0);
x_69 = lean_ctor_get(x_59, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_59);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_47);
lean_ctor_set(x_58, 2, x_70);
return x_56;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_71 = lean_ctor_get(x_58, 0);
x_72 = lean_ctor_get(x_58, 1);
x_73 = lean_ctor_get(x_58, 3);
x_74 = lean_ctor_get(x_58, 4);
x_75 = lean_ctor_get(x_58, 5);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_58);
x_76 = lean_ctor_get(x_59, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_59, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 x_78 = x_59;
} else {
 lean_dec_ref(x_59);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 3, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_79, 2, x_47);
x_80 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_80, 0, x_71);
lean_ctor_set(x_80, 1, x_72);
lean_ctor_set(x_80, 2, x_79);
lean_ctor_set(x_80, 3, x_73);
lean_ctor_set(x_80, 4, x_74);
lean_ctor_set(x_80, 5, x_75);
lean_ctor_set(x_57, 0, x_80);
return x_56;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_81 = lean_ctor_get(x_57, 1);
x_82 = lean_ctor_get(x_57, 2);
x_83 = lean_ctor_get(x_57, 3);
x_84 = lean_ctor_get(x_57, 4);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_57);
x_85 = lean_ctor_get(x_58, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_58, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_58, 3);
lean_inc(x_87);
x_88 = lean_ctor_get(x_58, 4);
lean_inc(x_88);
x_89 = lean_ctor_get(x_58, 5);
lean_inc(x_89);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 lean_ctor_release(x_58, 4);
 lean_ctor_release(x_58, 5);
 x_90 = x_58;
} else {
 lean_dec_ref(x_58);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_59, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_59, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 x_93 = x_59;
} else {
 lean_dec_ref(x_59);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 3, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
lean_ctor_set(x_94, 2, x_47);
if (lean_is_scalar(x_90)) {
 x_95 = lean_alloc_ctor(0, 6, 0);
} else {
 x_95 = x_90;
}
lean_ctor_set(x_95, 0, x_85);
lean_ctor_set(x_95, 1, x_86);
lean_ctor_set(x_95, 2, x_94);
lean_ctor_set(x_95, 3, x_87);
lean_ctor_set(x_95, 4, x_88);
lean_ctor_set(x_95, 5, x_89);
x_96 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_81);
lean_ctor_set(x_96, 2, x_82);
lean_ctor_set(x_96, 3, x_83);
lean_ctor_set(x_96, 4, x_84);
lean_ctor_set(x_56, 1, x_96);
return x_56;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_97 = lean_ctor_get(x_56, 0);
lean_inc(x_97);
lean_dec(x_56);
x_98 = lean_ctor_get(x_57, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_57, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_57, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_57, 4);
lean_inc(x_101);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 lean_ctor_release(x_57, 4);
 x_102 = x_57;
} else {
 lean_dec_ref(x_57);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_58, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_58, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_58, 3);
lean_inc(x_105);
x_106 = lean_ctor_get(x_58, 4);
lean_inc(x_106);
x_107 = lean_ctor_get(x_58, 5);
lean_inc(x_107);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 lean_ctor_release(x_58, 4);
 lean_ctor_release(x_58, 5);
 x_108 = x_58;
} else {
 lean_dec_ref(x_58);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_59, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_59, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 x_111 = x_59;
} else {
 lean_dec_ref(x_59);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 3, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
lean_ctor_set(x_112, 2, x_47);
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
if (lean_is_scalar(x_102)) {
 x_114 = lean_alloc_ctor(0, 5, 0);
} else {
 x_114 = x_102;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_98);
lean_ctor_set(x_114, 2, x_99);
lean_ctor_set(x_114, 3, x_100);
lean_ctor_set(x_114, 4, x_101);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_97);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = lean_ctor_get(x_56, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_117, 2);
lean_inc(x_118);
x_119 = !lean_is_exclusive(x_56);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_56, 1);
lean_dec(x_120);
x_121 = !lean_is_exclusive(x_116);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_116, 0);
lean_dec(x_122);
x_123 = !lean_is_exclusive(x_117);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_117, 2);
lean_dec(x_124);
x_125 = !lean_is_exclusive(x_118);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_118, 2);
lean_dec(x_126);
lean_ctor_set(x_118, 2, x_47);
return x_56;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_118, 0);
x_128 = lean_ctor_get(x_118, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_118);
x_129 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_47);
lean_ctor_set(x_117, 2, x_129);
return x_56;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_130 = lean_ctor_get(x_117, 0);
x_131 = lean_ctor_get(x_117, 1);
x_132 = lean_ctor_get(x_117, 3);
x_133 = lean_ctor_get(x_117, 4);
x_134 = lean_ctor_get(x_117, 5);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_117);
x_135 = lean_ctor_get(x_118, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_118, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 x_137 = x_118;
} else {
 lean_dec_ref(x_118);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 3, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
lean_ctor_set(x_138, 2, x_47);
x_139 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_139, 0, x_130);
lean_ctor_set(x_139, 1, x_131);
lean_ctor_set(x_139, 2, x_138);
lean_ctor_set(x_139, 3, x_132);
lean_ctor_set(x_139, 4, x_133);
lean_ctor_set(x_139, 5, x_134);
lean_ctor_set(x_116, 0, x_139);
return x_56;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_140 = lean_ctor_get(x_116, 1);
x_141 = lean_ctor_get(x_116, 2);
x_142 = lean_ctor_get(x_116, 3);
x_143 = lean_ctor_get(x_116, 4);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_116);
x_144 = lean_ctor_get(x_117, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_117, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_117, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_117, 4);
lean_inc(x_147);
x_148 = lean_ctor_get(x_117, 5);
lean_inc(x_148);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 lean_ctor_release(x_117, 4);
 lean_ctor_release(x_117, 5);
 x_149 = x_117;
} else {
 lean_dec_ref(x_117);
 x_149 = lean_box(0);
}
x_150 = lean_ctor_get(x_118, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_118, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 x_152 = x_118;
} else {
 lean_dec_ref(x_118);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(0, 3, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
lean_ctor_set(x_153, 2, x_47);
if (lean_is_scalar(x_149)) {
 x_154 = lean_alloc_ctor(0, 6, 0);
} else {
 x_154 = x_149;
}
lean_ctor_set(x_154, 0, x_144);
lean_ctor_set(x_154, 1, x_145);
lean_ctor_set(x_154, 2, x_153);
lean_ctor_set(x_154, 3, x_146);
lean_ctor_set(x_154, 4, x_147);
lean_ctor_set(x_154, 5, x_148);
x_155 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_140);
lean_ctor_set(x_155, 2, x_141);
lean_ctor_set(x_155, 3, x_142);
lean_ctor_set(x_155, 4, x_143);
lean_ctor_set(x_56, 1, x_155);
return x_56;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_156 = lean_ctor_get(x_56, 0);
lean_inc(x_156);
lean_dec(x_56);
x_157 = lean_ctor_get(x_116, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_116, 2);
lean_inc(x_158);
x_159 = lean_ctor_get(x_116, 3);
lean_inc(x_159);
x_160 = lean_ctor_get(x_116, 4);
lean_inc(x_160);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 lean_ctor_release(x_116, 2);
 lean_ctor_release(x_116, 3);
 lean_ctor_release(x_116, 4);
 x_161 = x_116;
} else {
 lean_dec_ref(x_116);
 x_161 = lean_box(0);
}
x_162 = lean_ctor_get(x_117, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_117, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_117, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_117, 4);
lean_inc(x_165);
x_166 = lean_ctor_get(x_117, 5);
lean_inc(x_166);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 lean_ctor_release(x_117, 4);
 lean_ctor_release(x_117, 5);
 x_167 = x_117;
} else {
 lean_dec_ref(x_117);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_118, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_118, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 x_170 = x_118;
} else {
 lean_dec_ref(x_118);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(0, 3, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
lean_ctor_set(x_171, 2, x_47);
if (lean_is_scalar(x_167)) {
 x_172 = lean_alloc_ctor(0, 6, 0);
} else {
 x_172 = x_167;
}
lean_ctor_set(x_172, 0, x_162);
lean_ctor_set(x_172, 1, x_163);
lean_ctor_set(x_172, 2, x_171);
lean_ctor_set(x_172, 3, x_164);
lean_ctor_set(x_172, 4, x_165);
lean_ctor_set(x_172, 5, x_166);
if (lean_is_scalar(x_161)) {
 x_173 = lean_alloc_ctor(0, 5, 0);
} else {
 x_173 = x_161;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_157);
lean_ctor_set(x_173, 2, x_158);
lean_ctor_set(x_173, 3, x_159);
lean_ctor_set(x_173, 4, x_160);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_156);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_49, 0);
lean_inc(x_175);
lean_dec(x_49);
x_176 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_18);
lean_ctor_set(x_176, 2, x_19);
lean_ctor_set(x_3, 0, x_176);
x_177 = lean_apply_3(x_2, x_17, x_3, x_50);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_179, 2);
lean_inc(x_180);
x_181 = lean_ctor_get(x_177, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_182 = x_177;
} else {
 lean_dec_ref(x_177);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_178, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_178, 2);
lean_inc(x_184);
x_185 = lean_ctor_get(x_178, 3);
lean_inc(x_185);
x_186 = lean_ctor_get(x_178, 4);
lean_inc(x_186);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 lean_ctor_release(x_178, 2);
 lean_ctor_release(x_178, 3);
 lean_ctor_release(x_178, 4);
 x_187 = x_178;
} else {
 lean_dec_ref(x_178);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_179, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_179, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_179, 3);
lean_inc(x_190);
x_191 = lean_ctor_get(x_179, 4);
lean_inc(x_191);
x_192 = lean_ctor_get(x_179, 5);
lean_inc(x_192);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 lean_ctor_release(x_179, 2);
 lean_ctor_release(x_179, 3);
 lean_ctor_release(x_179, 4);
 lean_ctor_release(x_179, 5);
 x_193 = x_179;
} else {
 lean_dec_ref(x_179);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_180, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_180, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 lean_ctor_release(x_180, 2);
 x_196 = x_180;
} else {
 lean_dec_ref(x_180);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 3, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
lean_ctor_set(x_197, 2, x_47);
if (lean_is_scalar(x_193)) {
 x_198 = lean_alloc_ctor(0, 6, 0);
} else {
 x_198 = x_193;
}
lean_ctor_set(x_198, 0, x_188);
lean_ctor_set(x_198, 1, x_189);
lean_ctor_set(x_198, 2, x_197);
lean_ctor_set(x_198, 3, x_190);
lean_ctor_set(x_198, 4, x_191);
lean_ctor_set(x_198, 5, x_192);
if (lean_is_scalar(x_187)) {
 x_199 = lean_alloc_ctor(0, 5, 0);
} else {
 x_199 = x_187;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_183);
lean_ctor_set(x_199, 2, x_184);
lean_ctor_set(x_199, 3, x_185);
lean_ctor_set(x_199, 4, x_186);
if (lean_is_scalar(x_182)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_182;
}
lean_ctor_set(x_200, 0, x_181);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_201 = lean_ctor_get(x_177, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_202, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_177, 0);
lean_inc(x_204);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_205 = x_177;
} else {
 lean_dec_ref(x_177);
 x_205 = lean_box(0);
}
x_206 = lean_ctor_get(x_201, 1);
lean_inc(x_206);
x_207 = lean_ctor_get(x_201, 2);
lean_inc(x_207);
x_208 = lean_ctor_get(x_201, 3);
lean_inc(x_208);
x_209 = lean_ctor_get(x_201, 4);
lean_inc(x_209);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 lean_ctor_release(x_201, 2);
 lean_ctor_release(x_201, 3);
 lean_ctor_release(x_201, 4);
 x_210 = x_201;
} else {
 lean_dec_ref(x_201);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_202, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_202, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_202, 3);
lean_inc(x_213);
x_214 = lean_ctor_get(x_202, 4);
lean_inc(x_214);
x_215 = lean_ctor_get(x_202, 5);
lean_inc(x_215);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 lean_ctor_release(x_202, 2);
 lean_ctor_release(x_202, 3);
 lean_ctor_release(x_202, 4);
 lean_ctor_release(x_202, 5);
 x_216 = x_202;
} else {
 lean_dec_ref(x_202);
 x_216 = lean_box(0);
}
x_217 = lean_ctor_get(x_203, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_203, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 lean_ctor_release(x_203, 2);
 x_219 = x_203;
} else {
 lean_dec_ref(x_203);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(0, 3, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_218);
lean_ctor_set(x_220, 2, x_47);
if (lean_is_scalar(x_216)) {
 x_221 = lean_alloc_ctor(0, 6, 0);
} else {
 x_221 = x_216;
}
lean_ctor_set(x_221, 0, x_211);
lean_ctor_set(x_221, 1, x_212);
lean_ctor_set(x_221, 2, x_220);
lean_ctor_set(x_221, 3, x_213);
lean_ctor_set(x_221, 4, x_214);
lean_ctor_set(x_221, 5, x_215);
if (lean_is_scalar(x_210)) {
 x_222 = lean_alloc_ctor(0, 5, 0);
} else {
 x_222 = x_210;
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_206);
lean_ctor_set(x_222, 2, x_207);
lean_ctor_set(x_222, 3, x_208);
lean_ctor_set(x_222, 4, x_209);
if (lean_is_scalar(x_205)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_205;
}
lean_ctor_set(x_223, 0, x_204);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_224 = lean_ctor_get(x_3, 1);
x_225 = lean_ctor_get(x_3, 2);
x_226 = lean_ctor_get(x_3, 3);
x_227 = lean_ctor_get(x_3, 4);
x_228 = lean_ctor_get(x_3, 5);
x_229 = lean_ctor_get(x_3, 6);
x_230 = lean_ctor_get(x_3, 7);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_3);
x_231 = lean_ctor_get(x_49, 0);
lean_inc(x_231);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 lean_ctor_release(x_49, 2);
 x_232 = x_49;
} else {
 lean_dec_ref(x_49);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(0, 3, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_18);
lean_ctor_set(x_233, 2, x_19);
x_234 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_224);
lean_ctor_set(x_234, 2, x_225);
lean_ctor_set(x_234, 3, x_226);
lean_ctor_set(x_234, 4, x_227);
lean_ctor_set(x_234, 5, x_228);
lean_ctor_set(x_234, 6, x_229);
lean_ctor_set(x_234, 7, x_230);
x_235 = lean_apply_3(x_2, x_17, x_234, x_50);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_237, 2);
lean_inc(x_238);
x_239 = lean_ctor_get(x_235, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_240 = x_235;
} else {
 lean_dec_ref(x_235);
 x_240 = lean_box(0);
}
x_241 = lean_ctor_get(x_236, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_236, 2);
lean_inc(x_242);
x_243 = lean_ctor_get(x_236, 3);
lean_inc(x_243);
x_244 = lean_ctor_get(x_236, 4);
lean_inc(x_244);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 lean_ctor_release(x_236, 2);
 lean_ctor_release(x_236, 3);
 lean_ctor_release(x_236, 4);
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
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 lean_ctor_release(x_238, 2);
 x_254 = x_238;
} else {
 lean_dec_ref(x_238);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(0, 3, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_253);
lean_ctor_set(x_255, 2, x_47);
if (lean_is_scalar(x_251)) {
 x_256 = lean_alloc_ctor(0, 6, 0);
} else {
 x_256 = x_251;
}
lean_ctor_set(x_256, 0, x_246);
lean_ctor_set(x_256, 1, x_247);
lean_ctor_set(x_256, 2, x_255);
lean_ctor_set(x_256, 3, x_248);
lean_ctor_set(x_256, 4, x_249);
lean_ctor_set(x_256, 5, x_250);
if (lean_is_scalar(x_245)) {
 x_257 = lean_alloc_ctor(0, 5, 0);
} else {
 x_257 = x_245;
}
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_241);
lean_ctor_set(x_257, 2, x_242);
lean_ctor_set(x_257, 3, x_243);
lean_ctor_set(x_257, 4, x_244);
if (lean_is_scalar(x_240)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_240;
}
lean_ctor_set(x_258, 0, x_239);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_259 = lean_ctor_get(x_235, 1);
lean_inc(x_259);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_260, 2);
lean_inc(x_261);
x_262 = lean_ctor_get(x_235, 0);
lean_inc(x_262);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_263 = x_235;
} else {
 lean_dec_ref(x_235);
 x_263 = lean_box(0);
}
x_264 = lean_ctor_get(x_259, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_259, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_259, 3);
lean_inc(x_266);
x_267 = lean_ctor_get(x_259, 4);
lean_inc(x_267);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 lean_ctor_release(x_259, 2);
 lean_ctor_release(x_259, 3);
 lean_ctor_release(x_259, 4);
 x_268 = x_259;
} else {
 lean_dec_ref(x_259);
 x_268 = lean_box(0);
}
x_269 = lean_ctor_get(x_260, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_260, 1);
lean_inc(x_270);
x_271 = lean_ctor_get(x_260, 3);
lean_inc(x_271);
x_272 = lean_ctor_get(x_260, 4);
lean_inc(x_272);
x_273 = lean_ctor_get(x_260, 5);
lean_inc(x_273);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 lean_ctor_release(x_260, 2);
 lean_ctor_release(x_260, 3);
 lean_ctor_release(x_260, 4);
 lean_ctor_release(x_260, 5);
 x_274 = x_260;
} else {
 lean_dec_ref(x_260);
 x_274 = lean_box(0);
}
x_275 = lean_ctor_get(x_261, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_261, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 x_277 = x_261;
} else {
 lean_dec_ref(x_261);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(0, 3, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
lean_ctor_set(x_278, 2, x_47);
if (lean_is_scalar(x_274)) {
 x_279 = lean_alloc_ctor(0, 6, 0);
} else {
 x_279 = x_274;
}
lean_ctor_set(x_279, 0, x_269);
lean_ctor_set(x_279, 1, x_270);
lean_ctor_set(x_279, 2, x_278);
lean_ctor_set(x_279, 3, x_271);
lean_ctor_set(x_279, 4, x_272);
lean_ctor_set(x_279, 5, x_273);
if (lean_is_scalar(x_268)) {
 x_280 = lean_alloc_ctor(0, 5, 0);
} else {
 x_280 = x_268;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_264);
lean_ctor_set(x_280, 2, x_265);
lean_ctor_set(x_280, 3, x_266);
lean_ctor_set(x_280, 4, x_267);
if (lean_is_scalar(x_263)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_263;
}
lean_ctor_set(x_281, 0, x_262);
lean_ctor_set(x_281, 1, x_280);
return x_281;
}
}
}
}
else
{
uint8_t x_282; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_282 = !lean_is_exclusive(x_13);
if (x_282 == 0)
{
return x_13;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_13, 0);
x_284 = lean_ctor_get(x_13, 1);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_13);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
return x_285;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabBinders(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabBinders___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabBinders___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabBinder___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = l_Lean_FileMap_ofString___closed__1;
x_6 = lean_array_push(x_5, x_1);
x_7 = l_Lean_Elab_Term_getLCtx(x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Term_getLocalInsts(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_empty___closed__1;
lean_inc(x_3);
lean_inc(x_11);
x_15 = l___private_Init_Lean_Elab_Term_8__elabBindersAux___main(x_6, x_13, x_14, x_8, x_11, x_3, x_12);
lean_dec(x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_array_get_size(x_11);
lean_dec(x_11);
x_23 = lean_array_get_size(x_21);
x_24 = lean_nat_dec_lt(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_26, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_dec(x_29);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 1, x_20);
x_30 = l_Lean_Expr_Inhabited;
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_array_get(x_30, x_19, x_31);
lean_dec(x_19);
x_33 = lean_apply_3(x_2, x_32, x_3, x_18);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
lean_dec(x_26);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_20);
lean_ctor_set(x_35, 2, x_21);
lean_ctor_set(x_3, 0, x_35);
x_36 = l_Lean_Expr_Inhabited;
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_array_get(x_36, x_19, x_37);
lean_dec(x_19);
x_39 = lean_apply_3(x_2, x_38, x_3, x_18);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_40 = lean_ctor_get(x_3, 0);
x_41 = lean_ctor_get(x_3, 1);
x_42 = lean_ctor_get(x_3, 2);
x_43 = lean_ctor_get(x_3, 3);
x_44 = lean_ctor_get(x_3, 4);
x_45 = lean_ctor_get(x_3, 5);
x_46 = lean_ctor_get(x_3, 6);
x_47 = lean_ctor_get(x_3, 7);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_3);
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 x_49 = x_40;
} else {
 lean_dec_ref(x_40);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 3, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_20);
lean_ctor_set(x_50, 2, x_21);
x_51 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_41);
lean_ctor_set(x_51, 2, x_42);
lean_ctor_set(x_51, 3, x_43);
lean_ctor_set(x_51, 4, x_44);
lean_ctor_set(x_51, 5, x_45);
lean_ctor_set(x_51, 6, x_46);
lean_ctor_set(x_51, 7, x_47);
x_52 = l_Lean_Expr_Inhabited;
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_array_get(x_52, x_19, x_53);
lean_dec(x_19);
x_55 = lean_apply_3(x_2, x_54, x_51, x_18);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_56 = lean_ctor_get(x_18, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 2);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_ctor_get(x_57, 2);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_18);
x_60 = lean_ctor_get(x_3, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = !lean_is_exclusive(x_3);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_3, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_60);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_60, 2);
lean_dec(x_65);
x_66 = lean_ctor_get(x_60, 1);
lean_dec(x_66);
lean_ctor_set(x_60, 2, x_21);
lean_ctor_set(x_60, 1, x_20);
x_67 = l_Lean_Expr_Inhabited;
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_array_get(x_67, x_19, x_68);
lean_dec(x_19);
x_70 = lean_apply_3(x_2, x_69, x_3, x_61);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 2);
lean_inc(x_73);
x_74 = !lean_is_exclusive(x_70);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_70, 1);
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
lean_ctor_set(x_73, 2, x_58);
return x_70;
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
lean_ctor_set(x_84, 2, x_58);
lean_ctor_set(x_72, 2, x_84);
return x_70;
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
lean_ctor_set(x_93, 2, x_58);
x_94 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_94, 0, x_85);
lean_ctor_set(x_94, 1, x_86);
lean_ctor_set(x_94, 2, x_93);
lean_ctor_set(x_94, 3, x_87);
lean_ctor_set(x_94, 4, x_88);
lean_ctor_set(x_94, 5, x_89);
lean_ctor_set(x_71, 0, x_94);
return x_70;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_95 = lean_ctor_get(x_71, 1);
x_96 = lean_ctor_get(x_71, 2);
x_97 = lean_ctor_get(x_71, 3);
x_98 = lean_ctor_get(x_71, 4);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_71);
x_99 = lean_ctor_get(x_72, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_72, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_72, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_72, 4);
lean_inc(x_102);
x_103 = lean_ctor_get(x_72, 5);
lean_inc(x_103);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 lean_ctor_release(x_72, 5);
 x_104 = x_72;
} else {
 lean_dec_ref(x_72);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_73, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_73, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_107 = x_73;
} else {
 lean_dec_ref(x_73);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 3, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
lean_ctor_set(x_108, 2, x_58);
if (lean_is_scalar(x_104)) {
 x_109 = lean_alloc_ctor(0, 6, 0);
} else {
 x_109 = x_104;
}
lean_ctor_set(x_109, 0, x_99);
lean_ctor_set(x_109, 1, x_100);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set(x_109, 3, x_101);
lean_ctor_set(x_109, 4, x_102);
lean_ctor_set(x_109, 5, x_103);
x_110 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_95);
lean_ctor_set(x_110, 2, x_96);
lean_ctor_set(x_110, 3, x_97);
lean_ctor_set(x_110, 4, x_98);
lean_ctor_set(x_70, 1, x_110);
return x_70;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_111 = lean_ctor_get(x_70, 0);
lean_inc(x_111);
lean_dec(x_70);
x_112 = lean_ctor_get(x_71, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_71, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_71, 3);
lean_inc(x_114);
x_115 = lean_ctor_get(x_71, 4);
lean_inc(x_115);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 x_116 = x_71;
} else {
 lean_dec_ref(x_71);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_72, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_72, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_72, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_72, 4);
lean_inc(x_120);
x_121 = lean_ctor_get(x_72, 5);
lean_inc(x_121);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 lean_ctor_release(x_72, 5);
 x_122 = x_72;
} else {
 lean_dec_ref(x_72);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_73, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_73, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_125 = x_73;
} else {
 lean_dec_ref(x_73);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(0, 3, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
lean_ctor_set(x_126, 2, x_58);
if (lean_is_scalar(x_122)) {
 x_127 = lean_alloc_ctor(0, 6, 0);
} else {
 x_127 = x_122;
}
lean_ctor_set(x_127, 0, x_117);
lean_ctor_set(x_127, 1, x_118);
lean_ctor_set(x_127, 2, x_126);
lean_ctor_set(x_127, 3, x_119);
lean_ctor_set(x_127, 4, x_120);
lean_ctor_set(x_127, 5, x_121);
if (lean_is_scalar(x_116)) {
 x_128 = lean_alloc_ctor(0, 5, 0);
} else {
 x_128 = x_116;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_112);
lean_ctor_set(x_128, 2, x_113);
lean_ctor_set(x_128, 3, x_114);
lean_ctor_set(x_128, 4, x_115);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_111);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_70, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 2);
lean_inc(x_132);
x_133 = !lean_is_exclusive(x_70);
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_70, 1);
lean_dec(x_134);
x_135 = !lean_is_exclusive(x_130);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_130, 0);
lean_dec(x_136);
x_137 = !lean_is_exclusive(x_131);
if (x_137 == 0)
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_131, 2);
lean_dec(x_138);
x_139 = !lean_is_exclusive(x_132);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_132, 2);
lean_dec(x_140);
lean_ctor_set(x_132, 2, x_58);
return x_70;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_132, 0);
x_142 = lean_ctor_get(x_132, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_132);
x_143 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_143, 2, x_58);
lean_ctor_set(x_131, 2, x_143);
return x_70;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_144 = lean_ctor_get(x_131, 0);
x_145 = lean_ctor_get(x_131, 1);
x_146 = lean_ctor_get(x_131, 3);
x_147 = lean_ctor_get(x_131, 4);
x_148 = lean_ctor_get(x_131, 5);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_131);
x_149 = lean_ctor_get(x_132, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_132, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 lean_ctor_release(x_132, 2);
 x_151 = x_132;
} else {
 lean_dec_ref(x_132);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(0, 3, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
lean_ctor_set(x_152, 2, x_58);
x_153 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_153, 0, x_144);
lean_ctor_set(x_153, 1, x_145);
lean_ctor_set(x_153, 2, x_152);
lean_ctor_set(x_153, 3, x_146);
lean_ctor_set(x_153, 4, x_147);
lean_ctor_set(x_153, 5, x_148);
lean_ctor_set(x_130, 0, x_153);
return x_70;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_154 = lean_ctor_get(x_130, 1);
x_155 = lean_ctor_get(x_130, 2);
x_156 = lean_ctor_get(x_130, 3);
x_157 = lean_ctor_get(x_130, 4);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_130);
x_158 = lean_ctor_get(x_131, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_131, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_131, 3);
lean_inc(x_160);
x_161 = lean_ctor_get(x_131, 4);
lean_inc(x_161);
x_162 = lean_ctor_get(x_131, 5);
lean_inc(x_162);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 lean_ctor_release(x_131, 4);
 lean_ctor_release(x_131, 5);
 x_163 = x_131;
} else {
 lean_dec_ref(x_131);
 x_163 = lean_box(0);
}
x_164 = lean_ctor_get(x_132, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_132, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 lean_ctor_release(x_132, 2);
 x_166 = x_132;
} else {
 lean_dec_ref(x_132);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 3, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
lean_ctor_set(x_167, 2, x_58);
if (lean_is_scalar(x_163)) {
 x_168 = lean_alloc_ctor(0, 6, 0);
} else {
 x_168 = x_163;
}
lean_ctor_set(x_168, 0, x_158);
lean_ctor_set(x_168, 1, x_159);
lean_ctor_set(x_168, 2, x_167);
lean_ctor_set(x_168, 3, x_160);
lean_ctor_set(x_168, 4, x_161);
lean_ctor_set(x_168, 5, x_162);
x_169 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_154);
lean_ctor_set(x_169, 2, x_155);
lean_ctor_set(x_169, 3, x_156);
lean_ctor_set(x_169, 4, x_157);
lean_ctor_set(x_70, 1, x_169);
return x_70;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_170 = lean_ctor_get(x_70, 0);
lean_inc(x_170);
lean_dec(x_70);
x_171 = lean_ctor_get(x_130, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_130, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_130, 3);
lean_inc(x_173);
x_174 = lean_ctor_get(x_130, 4);
lean_inc(x_174);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 lean_ctor_release(x_130, 3);
 lean_ctor_release(x_130, 4);
 x_175 = x_130;
} else {
 lean_dec_ref(x_130);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_131, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_131, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_131, 3);
lean_inc(x_178);
x_179 = lean_ctor_get(x_131, 4);
lean_inc(x_179);
x_180 = lean_ctor_get(x_131, 5);
lean_inc(x_180);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 lean_ctor_release(x_131, 4);
 lean_ctor_release(x_131, 5);
 x_181 = x_131;
} else {
 lean_dec_ref(x_131);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_132, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_132, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 lean_ctor_release(x_132, 2);
 x_184 = x_132;
} else {
 lean_dec_ref(x_132);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(0, 3, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
lean_ctor_set(x_185, 2, x_58);
if (lean_is_scalar(x_181)) {
 x_186 = lean_alloc_ctor(0, 6, 0);
} else {
 x_186 = x_181;
}
lean_ctor_set(x_186, 0, x_176);
lean_ctor_set(x_186, 1, x_177);
lean_ctor_set(x_186, 2, x_185);
lean_ctor_set(x_186, 3, x_178);
lean_ctor_set(x_186, 4, x_179);
lean_ctor_set(x_186, 5, x_180);
if (lean_is_scalar(x_175)) {
 x_187 = lean_alloc_ctor(0, 5, 0);
} else {
 x_187 = x_175;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_171);
lean_ctor_set(x_187, 2, x_172);
lean_ctor_set(x_187, 3, x_173);
lean_ctor_set(x_187, 4, x_174);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_170);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_189 = lean_ctor_get(x_60, 0);
lean_inc(x_189);
lean_dec(x_60);
x_190 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_20);
lean_ctor_set(x_190, 2, x_21);
lean_ctor_set(x_3, 0, x_190);
x_191 = l_Lean_Expr_Inhabited;
x_192 = lean_unsigned_to_nat(1u);
x_193 = lean_array_get(x_191, x_19, x_192);
lean_dec(x_19);
x_194 = lean_apply_3(x_2, x_193, x_3, x_61);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_196, 2);
lean_inc(x_197);
x_198 = lean_ctor_get(x_194, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_199 = x_194;
} else {
 lean_dec_ref(x_194);
 x_199 = lean_box(0);
}
x_200 = lean_ctor_get(x_195, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_195, 2);
lean_inc(x_201);
x_202 = lean_ctor_get(x_195, 3);
lean_inc(x_202);
x_203 = lean_ctor_get(x_195, 4);
lean_inc(x_203);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 lean_ctor_release(x_195, 4);
 x_204 = x_195;
} else {
 lean_dec_ref(x_195);
 x_204 = lean_box(0);
}
x_205 = lean_ctor_get(x_196, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_196, 1);
lean_inc(x_206);
x_207 = lean_ctor_get(x_196, 3);
lean_inc(x_207);
x_208 = lean_ctor_get(x_196, 4);
lean_inc(x_208);
x_209 = lean_ctor_get(x_196, 5);
lean_inc(x_209);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 lean_ctor_release(x_196, 4);
 lean_ctor_release(x_196, 5);
 x_210 = x_196;
} else {
 lean_dec_ref(x_196);
 x_210 = lean_box(0);
}
x_211 = lean_ctor_get(x_197, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_197, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 lean_ctor_release(x_197, 2);
 x_213 = x_197;
} else {
 lean_dec_ref(x_197);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(0, 3, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
lean_ctor_set(x_214, 2, x_58);
if (lean_is_scalar(x_210)) {
 x_215 = lean_alloc_ctor(0, 6, 0);
} else {
 x_215 = x_210;
}
lean_ctor_set(x_215, 0, x_205);
lean_ctor_set(x_215, 1, x_206);
lean_ctor_set(x_215, 2, x_214);
lean_ctor_set(x_215, 3, x_207);
lean_ctor_set(x_215, 4, x_208);
lean_ctor_set(x_215, 5, x_209);
if (lean_is_scalar(x_204)) {
 x_216 = lean_alloc_ctor(0, 5, 0);
} else {
 x_216 = x_204;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_200);
lean_ctor_set(x_216, 2, x_201);
lean_ctor_set(x_216, 3, x_202);
lean_ctor_set(x_216, 4, x_203);
if (lean_is_scalar(x_199)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_199;
}
lean_ctor_set(x_217, 0, x_198);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_218 = lean_ctor_get(x_194, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_219, 2);
lean_inc(x_220);
x_221 = lean_ctor_get(x_194, 0);
lean_inc(x_221);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_222 = x_194;
} else {
 lean_dec_ref(x_194);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_218, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_218, 2);
lean_inc(x_224);
x_225 = lean_ctor_get(x_218, 3);
lean_inc(x_225);
x_226 = lean_ctor_get(x_218, 4);
lean_inc(x_226);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 lean_ctor_release(x_218, 2);
 lean_ctor_release(x_218, 3);
 lean_ctor_release(x_218, 4);
 x_227 = x_218;
} else {
 lean_dec_ref(x_218);
 x_227 = lean_box(0);
}
x_228 = lean_ctor_get(x_219, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_219, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_219, 3);
lean_inc(x_230);
x_231 = lean_ctor_get(x_219, 4);
lean_inc(x_231);
x_232 = lean_ctor_get(x_219, 5);
lean_inc(x_232);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 lean_ctor_release(x_219, 2);
 lean_ctor_release(x_219, 3);
 lean_ctor_release(x_219, 4);
 lean_ctor_release(x_219, 5);
 x_233 = x_219;
} else {
 lean_dec_ref(x_219);
 x_233 = lean_box(0);
}
x_234 = lean_ctor_get(x_220, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_220, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 lean_ctor_release(x_220, 2);
 x_236 = x_220;
} else {
 lean_dec_ref(x_220);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(0, 3, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
lean_ctor_set(x_237, 2, x_58);
if (lean_is_scalar(x_233)) {
 x_238 = lean_alloc_ctor(0, 6, 0);
} else {
 x_238 = x_233;
}
lean_ctor_set(x_238, 0, x_228);
lean_ctor_set(x_238, 1, x_229);
lean_ctor_set(x_238, 2, x_237);
lean_ctor_set(x_238, 3, x_230);
lean_ctor_set(x_238, 4, x_231);
lean_ctor_set(x_238, 5, x_232);
if (lean_is_scalar(x_227)) {
 x_239 = lean_alloc_ctor(0, 5, 0);
} else {
 x_239 = x_227;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_223);
lean_ctor_set(x_239, 2, x_224);
lean_ctor_set(x_239, 3, x_225);
lean_ctor_set(x_239, 4, x_226);
if (lean_is_scalar(x_222)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_222;
}
lean_ctor_set(x_240, 0, x_221);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_241 = lean_ctor_get(x_3, 1);
x_242 = lean_ctor_get(x_3, 2);
x_243 = lean_ctor_get(x_3, 3);
x_244 = lean_ctor_get(x_3, 4);
x_245 = lean_ctor_get(x_3, 5);
x_246 = lean_ctor_get(x_3, 6);
x_247 = lean_ctor_get(x_3, 7);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_3);
x_248 = lean_ctor_get(x_60, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 lean_ctor_release(x_60, 2);
 x_249 = x_60;
} else {
 lean_dec_ref(x_60);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(0, 3, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_20);
lean_ctor_set(x_250, 2, x_21);
x_251 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_241);
lean_ctor_set(x_251, 2, x_242);
lean_ctor_set(x_251, 3, x_243);
lean_ctor_set(x_251, 4, x_244);
lean_ctor_set(x_251, 5, x_245);
lean_ctor_set(x_251, 6, x_246);
lean_ctor_set(x_251, 7, x_247);
x_252 = l_Lean_Expr_Inhabited;
x_253 = lean_unsigned_to_nat(1u);
x_254 = lean_array_get(x_252, x_19, x_253);
lean_dec(x_19);
x_255 = lean_apply_3(x_2, x_254, x_251, x_61);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_257, 2);
lean_inc(x_258);
x_259 = lean_ctor_get(x_255, 0);
lean_inc(x_259);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_260 = x_255;
} else {
 lean_dec_ref(x_255);
 x_260 = lean_box(0);
}
x_261 = lean_ctor_get(x_256, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_256, 2);
lean_inc(x_262);
x_263 = lean_ctor_get(x_256, 3);
lean_inc(x_263);
x_264 = lean_ctor_get(x_256, 4);
lean_inc(x_264);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 lean_ctor_release(x_256, 2);
 lean_ctor_release(x_256, 3);
 lean_ctor_release(x_256, 4);
 x_265 = x_256;
} else {
 lean_dec_ref(x_256);
 x_265 = lean_box(0);
}
x_266 = lean_ctor_get(x_257, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_257, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_257, 3);
lean_inc(x_268);
x_269 = lean_ctor_get(x_257, 4);
lean_inc(x_269);
x_270 = lean_ctor_get(x_257, 5);
lean_inc(x_270);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 lean_ctor_release(x_257, 2);
 lean_ctor_release(x_257, 3);
 lean_ctor_release(x_257, 4);
 lean_ctor_release(x_257, 5);
 x_271 = x_257;
} else {
 lean_dec_ref(x_257);
 x_271 = lean_box(0);
}
x_272 = lean_ctor_get(x_258, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_258, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 lean_ctor_release(x_258, 2);
 x_274 = x_258;
} else {
 lean_dec_ref(x_258);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(0, 3, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
lean_ctor_set(x_275, 2, x_58);
if (lean_is_scalar(x_271)) {
 x_276 = lean_alloc_ctor(0, 6, 0);
} else {
 x_276 = x_271;
}
lean_ctor_set(x_276, 0, x_266);
lean_ctor_set(x_276, 1, x_267);
lean_ctor_set(x_276, 2, x_275);
lean_ctor_set(x_276, 3, x_268);
lean_ctor_set(x_276, 4, x_269);
lean_ctor_set(x_276, 5, x_270);
if (lean_is_scalar(x_265)) {
 x_277 = lean_alloc_ctor(0, 5, 0);
} else {
 x_277 = x_265;
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_261);
lean_ctor_set(x_277, 2, x_262);
lean_ctor_set(x_277, 3, x_263);
lean_ctor_set(x_277, 4, x_264);
if (lean_is_scalar(x_260)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_260;
}
lean_ctor_set(x_278, 0, x_259);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_279 = lean_ctor_get(x_255, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_280, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_255, 0);
lean_inc(x_282);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_283 = x_255;
} else {
 lean_dec_ref(x_255);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_279, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_279, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_279, 3);
lean_inc(x_286);
x_287 = lean_ctor_get(x_279, 4);
lean_inc(x_287);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 lean_ctor_release(x_279, 2);
 lean_ctor_release(x_279, 3);
 lean_ctor_release(x_279, 4);
 x_288 = x_279;
} else {
 lean_dec_ref(x_279);
 x_288 = lean_box(0);
}
x_289 = lean_ctor_get(x_280, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_280, 1);
lean_inc(x_290);
x_291 = lean_ctor_get(x_280, 3);
lean_inc(x_291);
x_292 = lean_ctor_get(x_280, 4);
lean_inc(x_292);
x_293 = lean_ctor_get(x_280, 5);
lean_inc(x_293);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 lean_ctor_release(x_280, 2);
 lean_ctor_release(x_280, 3);
 lean_ctor_release(x_280, 4);
 lean_ctor_release(x_280, 5);
 x_294 = x_280;
} else {
 lean_dec_ref(x_280);
 x_294 = lean_box(0);
}
x_295 = lean_ctor_get(x_281, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_281, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 lean_ctor_release(x_281, 2);
 x_297 = x_281;
} else {
 lean_dec_ref(x_281);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(0, 3, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_295);
lean_ctor_set(x_298, 1, x_296);
lean_ctor_set(x_298, 2, x_58);
if (lean_is_scalar(x_294)) {
 x_299 = lean_alloc_ctor(0, 6, 0);
} else {
 x_299 = x_294;
}
lean_ctor_set(x_299, 0, x_289);
lean_ctor_set(x_299, 1, x_290);
lean_ctor_set(x_299, 2, x_298);
lean_ctor_set(x_299, 3, x_291);
lean_ctor_set(x_299, 4, x_292);
lean_ctor_set(x_299, 5, x_293);
if (lean_is_scalar(x_288)) {
 x_300 = lean_alloc_ctor(0, 5, 0);
} else {
 x_300 = x_288;
}
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_284);
lean_ctor_set(x_300, 2, x_285);
lean_ctor_set(x_300, 3, x_286);
lean_ctor_set(x_300, 4, x_287);
if (lean_is_scalar(x_283)) {
 x_301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_301 = x_283;
}
lean_ctor_set(x_301, 0, x_282);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
}
else
{
uint8_t x_302; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_302 = !lean_is_exclusive(x_15);
if (x_302 == 0)
{
return x_15;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_15, 0);
x_304 = lean_ctor_get(x_15, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_15);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabBinder(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinder___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Elab_Term_getLCtx(x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_stxInh;
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_array_get(x_9, x_5, x_10);
x_12 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = lean_array_get(x_9, x_5, x_13);
x_15 = l_Lean_Elab_Term_getLocalInsts(x_3, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Array_empty___closed__1;
lean_inc(x_3);
lean_inc(x_16);
x_20 = l___private_Init_Lean_Elab_Term_8__elabBindersAux___main(x_12, x_18, x_19, x_7, x_16, x_3, x_17);
lean_dec(x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_array_get_size(x_16);
lean_dec(x_16);
x_28 = lean_array_get_size(x_26);
x_29 = lean_nat_dec_lt(x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_3);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_3, 0);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 2);
lean_dec(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_dec(x_34);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 1, x_25);
lean_inc(x_3);
x_35 = l_Lean_Elab_Term_elabType(x_14, x_3, x_23);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Term_mkForall(x_24, x_36, x_3, x_37);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_3);
lean_dec(x_24);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 0);
lean_inc(x_43);
lean_dec(x_31);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_25);
lean_ctor_set(x_44, 2, x_26);
lean_ctor_set(x_3, 0, x_44);
lean_inc(x_3);
x_45 = l_Lean_Elab_Term_elabType(x_14, x_3, x_23);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Elab_Term_mkForall(x_24, x_46, x_3, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_3);
lean_dec(x_24);
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_51 = x_45;
} else {
 lean_dec_ref(x_45);
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
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_53 = lean_ctor_get(x_3, 0);
x_54 = lean_ctor_get(x_3, 1);
x_55 = lean_ctor_get(x_3, 2);
x_56 = lean_ctor_get(x_3, 3);
x_57 = lean_ctor_get(x_3, 4);
x_58 = lean_ctor_get(x_3, 5);
x_59 = lean_ctor_get(x_3, 6);
x_60 = lean_ctor_get(x_3, 7);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_3);
x_61 = lean_ctor_get(x_53, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 x_62 = x_53;
} else {
 lean_dec_ref(x_53);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 3, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_25);
lean_ctor_set(x_63, 2, x_26);
x_64 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_54);
lean_ctor_set(x_64, 2, x_55);
lean_ctor_set(x_64, 3, x_56);
lean_ctor_set(x_64, 4, x_57);
lean_ctor_set(x_64, 5, x_58);
lean_ctor_set(x_64, 6, x_59);
lean_ctor_set(x_64, 7, x_60);
lean_inc(x_64);
x_65 = l_Lean_Elab_Term_elabType(x_14, x_64, x_23);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Elab_Term_mkForall(x_24, x_66, x_64, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_64);
lean_dec(x_24);
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_71 = x_65;
} else {
 lean_dec_ref(x_65);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_73 = lean_ctor_get(x_23, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 2);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_ctor_get(x_74, 2);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_23);
x_77 = lean_ctor_get(x_3, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = !lean_is_exclusive(x_3);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_3, 0);
lean_dec(x_80);
x_81 = !lean_is_exclusive(x_77);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_77, 2);
lean_dec(x_82);
x_83 = lean_ctor_get(x_77, 1);
lean_dec(x_83);
lean_ctor_set(x_77, 2, x_26);
lean_ctor_set(x_77, 1, x_25);
lean_inc(x_3);
x_84 = l_Lean_Elab_Term_elabType(x_14, x_3, x_78);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Elab_Term_mkForall(x_24, x_85, x_3, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 2);
lean_inc(x_90);
x_91 = !lean_is_exclusive(x_87);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_87, 1);
lean_dec(x_92);
x_93 = !lean_is_exclusive(x_88);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_88, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_89);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_89, 2);
lean_dec(x_96);
x_97 = !lean_is_exclusive(x_90);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_90, 2);
lean_dec(x_98);
lean_ctor_set(x_90, 2, x_75);
return x_87;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_90, 0);
x_100 = lean_ctor_get(x_90, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_90);
x_101 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_101, 2, x_75);
lean_ctor_set(x_89, 2, x_101);
return x_87;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_102 = lean_ctor_get(x_89, 0);
x_103 = lean_ctor_get(x_89, 1);
x_104 = lean_ctor_get(x_89, 3);
x_105 = lean_ctor_get(x_89, 4);
x_106 = lean_ctor_get(x_89, 5);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_89);
x_107 = lean_ctor_get(x_90, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_90, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 x_109 = x_90;
} else {
 lean_dec_ref(x_90);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(0, 3, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
lean_ctor_set(x_110, 2, x_75);
x_111 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_111, 0, x_102);
lean_ctor_set(x_111, 1, x_103);
lean_ctor_set(x_111, 2, x_110);
lean_ctor_set(x_111, 3, x_104);
lean_ctor_set(x_111, 4, x_105);
lean_ctor_set(x_111, 5, x_106);
lean_ctor_set(x_88, 0, x_111);
return x_87;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_112 = lean_ctor_get(x_88, 1);
x_113 = lean_ctor_get(x_88, 2);
x_114 = lean_ctor_get(x_88, 3);
x_115 = lean_ctor_get(x_88, 4);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_88);
x_116 = lean_ctor_get(x_89, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_89, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_89, 3);
lean_inc(x_118);
x_119 = lean_ctor_get(x_89, 4);
lean_inc(x_119);
x_120 = lean_ctor_get(x_89, 5);
lean_inc(x_120);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 lean_ctor_release(x_89, 4);
 lean_ctor_release(x_89, 5);
 x_121 = x_89;
} else {
 lean_dec_ref(x_89);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_90, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_90, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 x_124 = x_90;
} else {
 lean_dec_ref(x_90);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 3, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
lean_ctor_set(x_125, 2, x_75);
if (lean_is_scalar(x_121)) {
 x_126 = lean_alloc_ctor(0, 6, 0);
} else {
 x_126 = x_121;
}
lean_ctor_set(x_126, 0, x_116);
lean_ctor_set(x_126, 1, x_117);
lean_ctor_set(x_126, 2, x_125);
lean_ctor_set(x_126, 3, x_118);
lean_ctor_set(x_126, 4, x_119);
lean_ctor_set(x_126, 5, x_120);
x_127 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_112);
lean_ctor_set(x_127, 2, x_113);
lean_ctor_set(x_127, 3, x_114);
lean_ctor_set(x_127, 4, x_115);
lean_ctor_set(x_87, 1, x_127);
return x_87;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_128 = lean_ctor_get(x_87, 0);
lean_inc(x_128);
lean_dec(x_87);
x_129 = lean_ctor_get(x_88, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_88, 2);
lean_inc(x_130);
x_131 = lean_ctor_get(x_88, 3);
lean_inc(x_131);
x_132 = lean_ctor_get(x_88, 4);
lean_inc(x_132);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 lean_ctor_release(x_88, 4);
 x_133 = x_88;
} else {
 lean_dec_ref(x_88);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_89, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_89, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_89, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_89, 4);
lean_inc(x_137);
x_138 = lean_ctor_get(x_89, 5);
lean_inc(x_138);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 lean_ctor_release(x_89, 4);
 lean_ctor_release(x_89, 5);
 x_139 = x_89;
} else {
 lean_dec_ref(x_89);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_90, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_90, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 x_142 = x_90;
} else {
 lean_dec_ref(x_90);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 3, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
lean_ctor_set(x_143, 2, x_75);
if (lean_is_scalar(x_139)) {
 x_144 = lean_alloc_ctor(0, 6, 0);
} else {
 x_144 = x_139;
}
lean_ctor_set(x_144, 0, x_134);
lean_ctor_set(x_144, 1, x_135);
lean_ctor_set(x_144, 2, x_143);
lean_ctor_set(x_144, 3, x_136);
lean_ctor_set(x_144, 4, x_137);
lean_ctor_set(x_144, 5, x_138);
if (lean_is_scalar(x_133)) {
 x_145 = lean_alloc_ctor(0, 5, 0);
} else {
 x_145 = x_133;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_129);
lean_ctor_set(x_145, 2, x_130);
lean_ctor_set(x_145, 3, x_131);
lean_ctor_set(x_145, 4, x_132);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_128);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_147 = lean_ctor_get(x_87, 1);
lean_inc(x_147);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_148, 2);
lean_inc(x_149);
x_150 = !lean_is_exclusive(x_87);
if (x_150 == 0)
{
lean_object* x_151; uint8_t x_152; 
x_151 = lean_ctor_get(x_87, 1);
lean_dec(x_151);
x_152 = !lean_is_exclusive(x_147);
if (x_152 == 0)
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_ctor_get(x_147, 0);
lean_dec(x_153);
x_154 = !lean_is_exclusive(x_148);
if (x_154 == 0)
{
lean_object* x_155; uint8_t x_156; 
x_155 = lean_ctor_get(x_148, 2);
lean_dec(x_155);
x_156 = !lean_is_exclusive(x_149);
if (x_156 == 0)
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_149, 2);
lean_dec(x_157);
lean_ctor_set(x_149, 2, x_75);
return x_87;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_149, 0);
x_159 = lean_ctor_get(x_149, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_149);
x_160 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set(x_160, 2, x_75);
lean_ctor_set(x_148, 2, x_160);
return x_87;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_161 = lean_ctor_get(x_148, 0);
x_162 = lean_ctor_get(x_148, 1);
x_163 = lean_ctor_get(x_148, 3);
x_164 = lean_ctor_get(x_148, 4);
x_165 = lean_ctor_get(x_148, 5);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_148);
x_166 = lean_ctor_get(x_149, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_149, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 lean_ctor_release(x_149, 2);
 x_168 = x_149;
} else {
 lean_dec_ref(x_149);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(0, 3, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
lean_ctor_set(x_169, 2, x_75);
x_170 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_170, 0, x_161);
lean_ctor_set(x_170, 1, x_162);
lean_ctor_set(x_170, 2, x_169);
lean_ctor_set(x_170, 3, x_163);
lean_ctor_set(x_170, 4, x_164);
lean_ctor_set(x_170, 5, x_165);
lean_ctor_set(x_147, 0, x_170);
return x_87;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_171 = lean_ctor_get(x_147, 1);
x_172 = lean_ctor_get(x_147, 2);
x_173 = lean_ctor_get(x_147, 3);
x_174 = lean_ctor_get(x_147, 4);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_147);
x_175 = lean_ctor_get(x_148, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_148, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_148, 3);
lean_inc(x_177);
x_178 = lean_ctor_get(x_148, 4);
lean_inc(x_178);
x_179 = lean_ctor_get(x_148, 5);
lean_inc(x_179);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 lean_ctor_release(x_148, 2);
 lean_ctor_release(x_148, 3);
 lean_ctor_release(x_148, 4);
 lean_ctor_release(x_148, 5);
 x_180 = x_148;
} else {
 lean_dec_ref(x_148);
 x_180 = lean_box(0);
}
x_181 = lean_ctor_get(x_149, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_149, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 lean_ctor_release(x_149, 2);
 x_183 = x_149;
} else {
 lean_dec_ref(x_149);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(0, 3, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
lean_ctor_set(x_184, 2, x_75);
if (lean_is_scalar(x_180)) {
 x_185 = lean_alloc_ctor(0, 6, 0);
} else {
 x_185 = x_180;
}
lean_ctor_set(x_185, 0, x_175);
lean_ctor_set(x_185, 1, x_176);
lean_ctor_set(x_185, 2, x_184);
lean_ctor_set(x_185, 3, x_177);
lean_ctor_set(x_185, 4, x_178);
lean_ctor_set(x_185, 5, x_179);
x_186 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_171);
lean_ctor_set(x_186, 2, x_172);
lean_ctor_set(x_186, 3, x_173);
lean_ctor_set(x_186, 4, x_174);
lean_ctor_set(x_87, 1, x_186);
return x_87;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_187 = lean_ctor_get(x_87, 0);
lean_inc(x_187);
lean_dec(x_87);
x_188 = lean_ctor_get(x_147, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_147, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_147, 3);
lean_inc(x_190);
x_191 = lean_ctor_get(x_147, 4);
lean_inc(x_191);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 lean_ctor_release(x_147, 2);
 lean_ctor_release(x_147, 3);
 lean_ctor_release(x_147, 4);
 x_192 = x_147;
} else {
 lean_dec_ref(x_147);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_148, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_148, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_148, 3);
lean_inc(x_195);
x_196 = lean_ctor_get(x_148, 4);
lean_inc(x_196);
x_197 = lean_ctor_get(x_148, 5);
lean_inc(x_197);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 lean_ctor_release(x_148, 2);
 lean_ctor_release(x_148, 3);
 lean_ctor_release(x_148, 4);
 lean_ctor_release(x_148, 5);
 x_198 = x_148;
} else {
 lean_dec_ref(x_148);
 x_198 = lean_box(0);
}
x_199 = lean_ctor_get(x_149, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_149, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 lean_ctor_release(x_149, 2);
 x_201 = x_149;
} else {
 lean_dec_ref(x_149);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 3, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
lean_ctor_set(x_202, 2, x_75);
if (lean_is_scalar(x_198)) {
 x_203 = lean_alloc_ctor(0, 6, 0);
} else {
 x_203 = x_198;
}
lean_ctor_set(x_203, 0, x_193);
lean_ctor_set(x_203, 1, x_194);
lean_ctor_set(x_203, 2, x_202);
lean_ctor_set(x_203, 3, x_195);
lean_ctor_set(x_203, 4, x_196);
lean_ctor_set(x_203, 5, x_197);
if (lean_is_scalar(x_192)) {
 x_204 = lean_alloc_ctor(0, 5, 0);
} else {
 x_204 = x_192;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_188);
lean_ctor_set(x_204, 2, x_189);
lean_ctor_set(x_204, 3, x_190);
lean_ctor_set(x_204, 4, x_191);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_187);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
lean_dec(x_3);
lean_dec(x_24);
x_206 = lean_ctor_get(x_84, 1);
lean_inc(x_206);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_207, 2);
lean_inc(x_208);
x_209 = !lean_is_exclusive(x_84);
if (x_209 == 0)
{
lean_object* x_210; uint8_t x_211; 
x_210 = lean_ctor_get(x_84, 1);
lean_dec(x_210);
x_211 = !lean_is_exclusive(x_206);
if (x_211 == 0)
{
lean_object* x_212; uint8_t x_213; 
x_212 = lean_ctor_get(x_206, 0);
lean_dec(x_212);
x_213 = !lean_is_exclusive(x_207);
if (x_213 == 0)
{
lean_object* x_214; uint8_t x_215; 
x_214 = lean_ctor_get(x_207, 2);
lean_dec(x_214);
x_215 = !lean_is_exclusive(x_208);
if (x_215 == 0)
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_208, 2);
lean_dec(x_216);
lean_ctor_set(x_208, 2, x_75);
return x_84;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_208, 0);
x_218 = lean_ctor_get(x_208, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_208);
x_219 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
lean_ctor_set(x_219, 2, x_75);
lean_ctor_set(x_207, 2, x_219);
return x_84;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_220 = lean_ctor_get(x_207, 0);
x_221 = lean_ctor_get(x_207, 1);
x_222 = lean_ctor_get(x_207, 3);
x_223 = lean_ctor_get(x_207, 4);
x_224 = lean_ctor_get(x_207, 5);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_207);
x_225 = lean_ctor_get(x_208, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_208, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 x_227 = x_208;
} else {
 lean_dec_ref(x_208);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(0, 3, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
lean_ctor_set(x_228, 2, x_75);
x_229 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_229, 0, x_220);
lean_ctor_set(x_229, 1, x_221);
lean_ctor_set(x_229, 2, x_228);
lean_ctor_set(x_229, 3, x_222);
lean_ctor_set(x_229, 4, x_223);
lean_ctor_set(x_229, 5, x_224);
lean_ctor_set(x_206, 0, x_229);
return x_84;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_230 = lean_ctor_get(x_206, 1);
x_231 = lean_ctor_get(x_206, 2);
x_232 = lean_ctor_get(x_206, 3);
x_233 = lean_ctor_get(x_206, 4);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_206);
x_234 = lean_ctor_get(x_207, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_207, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_207, 3);
lean_inc(x_236);
x_237 = lean_ctor_get(x_207, 4);
lean_inc(x_237);
x_238 = lean_ctor_get(x_207, 5);
lean_inc(x_238);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 lean_ctor_release(x_207, 4);
 lean_ctor_release(x_207, 5);
 x_239 = x_207;
} else {
 lean_dec_ref(x_207);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_208, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_208, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 x_242 = x_208;
} else {
 lean_dec_ref(x_208);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(0, 3, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
lean_ctor_set(x_243, 2, x_75);
if (lean_is_scalar(x_239)) {
 x_244 = lean_alloc_ctor(0, 6, 0);
} else {
 x_244 = x_239;
}
lean_ctor_set(x_244, 0, x_234);
lean_ctor_set(x_244, 1, x_235);
lean_ctor_set(x_244, 2, x_243);
lean_ctor_set(x_244, 3, x_236);
lean_ctor_set(x_244, 4, x_237);
lean_ctor_set(x_244, 5, x_238);
x_245 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_230);
lean_ctor_set(x_245, 2, x_231);
lean_ctor_set(x_245, 3, x_232);
lean_ctor_set(x_245, 4, x_233);
lean_ctor_set(x_84, 1, x_245);
return x_84;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_246 = lean_ctor_get(x_84, 0);
lean_inc(x_246);
lean_dec(x_84);
x_247 = lean_ctor_get(x_206, 1);
lean_inc(x_247);
x_248 = lean_ctor_get(x_206, 2);
lean_inc(x_248);
x_249 = lean_ctor_get(x_206, 3);
lean_inc(x_249);
x_250 = lean_ctor_get(x_206, 4);
lean_inc(x_250);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 lean_ctor_release(x_206, 2);
 lean_ctor_release(x_206, 3);
 lean_ctor_release(x_206, 4);
 x_251 = x_206;
} else {
 lean_dec_ref(x_206);
 x_251 = lean_box(0);
}
x_252 = lean_ctor_get(x_207, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_207, 1);
lean_inc(x_253);
x_254 = lean_ctor_get(x_207, 3);
lean_inc(x_254);
x_255 = lean_ctor_get(x_207, 4);
lean_inc(x_255);
x_256 = lean_ctor_get(x_207, 5);
lean_inc(x_256);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 lean_ctor_release(x_207, 4);
 lean_ctor_release(x_207, 5);
 x_257 = x_207;
} else {
 lean_dec_ref(x_207);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_208, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_208, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 x_260 = x_208;
} else {
 lean_dec_ref(x_208);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(0, 3, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
lean_ctor_set(x_261, 2, x_75);
if (lean_is_scalar(x_257)) {
 x_262 = lean_alloc_ctor(0, 6, 0);
} else {
 x_262 = x_257;
}
lean_ctor_set(x_262, 0, x_252);
lean_ctor_set(x_262, 1, x_253);
lean_ctor_set(x_262, 2, x_261);
lean_ctor_set(x_262, 3, x_254);
lean_ctor_set(x_262, 4, x_255);
lean_ctor_set(x_262, 5, x_256);
if (lean_is_scalar(x_251)) {
 x_263 = lean_alloc_ctor(0, 5, 0);
} else {
 x_263 = x_251;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_247);
lean_ctor_set(x_263, 2, x_248);
lean_ctor_set(x_263, 3, x_249);
lean_ctor_set(x_263, 4, x_250);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_246);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_77, 0);
lean_inc(x_265);
lean_dec(x_77);
x_266 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_25);
lean_ctor_set(x_266, 2, x_26);
lean_ctor_set(x_3, 0, x_266);
lean_inc(x_3);
x_267 = l_Lean_Elab_Term_elabType(x_14, x_3, x_78);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
x_270 = l_Lean_Elab_Term_mkForall(x_24, x_268, x_3, x_269);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_272, 2);
lean_inc(x_273);
x_274 = lean_ctor_get(x_270, 0);
lean_inc(x_274);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_275 = x_270;
} else {
 lean_dec_ref(x_270);
 x_275 = lean_box(0);
}
x_276 = lean_ctor_get(x_271, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_271, 2);
lean_inc(x_277);
x_278 = lean_ctor_get(x_271, 3);
lean_inc(x_278);
x_279 = lean_ctor_get(x_271, 4);
lean_inc(x_279);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 lean_ctor_release(x_271, 3);
 lean_ctor_release(x_271, 4);
 x_280 = x_271;
} else {
 lean_dec_ref(x_271);
 x_280 = lean_box(0);
}
x_281 = lean_ctor_get(x_272, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_272, 1);
lean_inc(x_282);
x_283 = lean_ctor_get(x_272, 3);
lean_inc(x_283);
x_284 = lean_ctor_get(x_272, 4);
lean_inc(x_284);
x_285 = lean_ctor_get(x_272, 5);
lean_inc(x_285);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 lean_ctor_release(x_272, 3);
 lean_ctor_release(x_272, 4);
 lean_ctor_release(x_272, 5);
 x_286 = x_272;
} else {
 lean_dec_ref(x_272);
 x_286 = lean_box(0);
}
x_287 = lean_ctor_get(x_273, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_273, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 lean_ctor_release(x_273, 2);
 x_289 = x_273;
} else {
 lean_dec_ref(x_273);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(0, 3, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_288);
lean_ctor_set(x_290, 2, x_75);
if (lean_is_scalar(x_286)) {
 x_291 = lean_alloc_ctor(0, 6, 0);
} else {
 x_291 = x_286;
}
lean_ctor_set(x_291, 0, x_281);
lean_ctor_set(x_291, 1, x_282);
lean_ctor_set(x_291, 2, x_290);
lean_ctor_set(x_291, 3, x_283);
lean_ctor_set(x_291, 4, x_284);
lean_ctor_set(x_291, 5, x_285);
if (lean_is_scalar(x_280)) {
 x_292 = lean_alloc_ctor(0, 5, 0);
} else {
 x_292 = x_280;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_276);
lean_ctor_set(x_292, 2, x_277);
lean_ctor_set(x_292, 3, x_278);
lean_ctor_set(x_292, 4, x_279);
if (lean_is_scalar(x_275)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_275;
}
lean_ctor_set(x_293, 0, x_274);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_294 = lean_ctor_get(x_270, 1);
lean_inc(x_294);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_295, 2);
lean_inc(x_296);
x_297 = lean_ctor_get(x_270, 0);
lean_inc(x_297);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_298 = x_270;
} else {
 lean_dec_ref(x_270);
 x_298 = lean_box(0);
}
x_299 = lean_ctor_get(x_294, 1);
lean_inc(x_299);
x_300 = lean_ctor_get(x_294, 2);
lean_inc(x_300);
x_301 = lean_ctor_get(x_294, 3);
lean_inc(x_301);
x_302 = lean_ctor_get(x_294, 4);
lean_inc(x_302);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 lean_ctor_release(x_294, 2);
 lean_ctor_release(x_294, 3);
 lean_ctor_release(x_294, 4);
 x_303 = x_294;
} else {
 lean_dec_ref(x_294);
 x_303 = lean_box(0);
}
x_304 = lean_ctor_get(x_295, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_295, 1);
lean_inc(x_305);
x_306 = lean_ctor_get(x_295, 3);
lean_inc(x_306);
x_307 = lean_ctor_get(x_295, 4);
lean_inc(x_307);
x_308 = lean_ctor_get(x_295, 5);
lean_inc(x_308);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 lean_ctor_release(x_295, 2);
 lean_ctor_release(x_295, 3);
 lean_ctor_release(x_295, 4);
 lean_ctor_release(x_295, 5);
 x_309 = x_295;
} else {
 lean_dec_ref(x_295);
 x_309 = lean_box(0);
}
x_310 = lean_ctor_get(x_296, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_296, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 lean_ctor_release(x_296, 2);
 x_312 = x_296;
} else {
 lean_dec_ref(x_296);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(0, 3, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_311);
lean_ctor_set(x_313, 2, x_75);
if (lean_is_scalar(x_309)) {
 x_314 = lean_alloc_ctor(0, 6, 0);
} else {
 x_314 = x_309;
}
lean_ctor_set(x_314, 0, x_304);
lean_ctor_set(x_314, 1, x_305);
lean_ctor_set(x_314, 2, x_313);
lean_ctor_set(x_314, 3, x_306);
lean_ctor_set(x_314, 4, x_307);
lean_ctor_set(x_314, 5, x_308);
if (lean_is_scalar(x_303)) {
 x_315 = lean_alloc_ctor(0, 5, 0);
} else {
 x_315 = x_303;
}
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_299);
lean_ctor_set(x_315, 2, x_300);
lean_ctor_set(x_315, 3, x_301);
lean_ctor_set(x_315, 4, x_302);
if (lean_is_scalar(x_298)) {
 x_316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_316 = x_298;
}
lean_ctor_set(x_316, 0, x_297);
lean_ctor_set(x_316, 1, x_315);
return x_316;
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_3);
lean_dec(x_24);
x_317 = lean_ctor_get(x_267, 1);
lean_inc(x_317);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_318, 2);
lean_inc(x_319);
x_320 = lean_ctor_get(x_267, 0);
lean_inc(x_320);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_321 = x_267;
} else {
 lean_dec_ref(x_267);
 x_321 = lean_box(0);
}
x_322 = lean_ctor_get(x_317, 1);
lean_inc(x_322);
x_323 = lean_ctor_get(x_317, 2);
lean_inc(x_323);
x_324 = lean_ctor_get(x_317, 3);
lean_inc(x_324);
x_325 = lean_ctor_get(x_317, 4);
lean_inc(x_325);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 lean_ctor_release(x_317, 2);
 lean_ctor_release(x_317, 3);
 lean_ctor_release(x_317, 4);
 x_326 = x_317;
} else {
 lean_dec_ref(x_317);
 x_326 = lean_box(0);
}
x_327 = lean_ctor_get(x_318, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_318, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_318, 3);
lean_inc(x_329);
x_330 = lean_ctor_get(x_318, 4);
lean_inc(x_330);
x_331 = lean_ctor_get(x_318, 5);
lean_inc(x_331);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 lean_ctor_release(x_318, 2);
 lean_ctor_release(x_318, 3);
 lean_ctor_release(x_318, 4);
 lean_ctor_release(x_318, 5);
 x_332 = x_318;
} else {
 lean_dec_ref(x_318);
 x_332 = lean_box(0);
}
x_333 = lean_ctor_get(x_319, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_319, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 lean_ctor_release(x_319, 2);
 x_335 = x_319;
} else {
 lean_dec_ref(x_319);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(0, 3, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_333);
lean_ctor_set(x_336, 1, x_334);
lean_ctor_set(x_336, 2, x_75);
if (lean_is_scalar(x_332)) {
 x_337 = lean_alloc_ctor(0, 6, 0);
} else {
 x_337 = x_332;
}
lean_ctor_set(x_337, 0, x_327);
lean_ctor_set(x_337, 1, x_328);
lean_ctor_set(x_337, 2, x_336);
lean_ctor_set(x_337, 3, x_329);
lean_ctor_set(x_337, 4, x_330);
lean_ctor_set(x_337, 5, x_331);
if (lean_is_scalar(x_326)) {
 x_338 = lean_alloc_ctor(0, 5, 0);
} else {
 x_338 = x_326;
}
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_322);
lean_ctor_set(x_338, 2, x_323);
lean_ctor_set(x_338, 3, x_324);
lean_ctor_set(x_338, 4, x_325);
if (lean_is_scalar(x_321)) {
 x_339 = lean_alloc_ctor(1, 2, 0);
} else {
 x_339 = x_321;
}
lean_ctor_set(x_339, 0, x_320);
lean_ctor_set(x_339, 1, x_338);
return x_339;
}
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_340 = lean_ctor_get(x_3, 1);
x_341 = lean_ctor_get(x_3, 2);
x_342 = lean_ctor_get(x_3, 3);
x_343 = lean_ctor_get(x_3, 4);
x_344 = lean_ctor_get(x_3, 5);
x_345 = lean_ctor_get(x_3, 6);
x_346 = lean_ctor_get(x_3, 7);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_3);
x_347 = lean_ctor_get(x_77, 0);
lean_inc(x_347);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 x_348 = x_77;
} else {
 lean_dec_ref(x_77);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(0, 3, 0);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_25);
lean_ctor_set(x_349, 2, x_26);
x_350 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_340);
lean_ctor_set(x_350, 2, x_341);
lean_ctor_set(x_350, 3, x_342);
lean_ctor_set(x_350, 4, x_343);
lean_ctor_set(x_350, 5, x_344);
lean_ctor_set(x_350, 6, x_345);
lean_ctor_set(x_350, 7, x_346);
lean_inc(x_350);
x_351 = l_Lean_Elab_Term_elabType(x_14, x_350, x_78);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = l_Lean_Elab_Term_mkForall(x_24, x_352, x_350, x_353);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_355 = lean_ctor_get(x_354, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_356, 2);
lean_inc(x_357);
x_358 = lean_ctor_get(x_354, 0);
lean_inc(x_358);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_359 = x_354;
} else {
 lean_dec_ref(x_354);
 x_359 = lean_box(0);
}
x_360 = lean_ctor_get(x_355, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_355, 2);
lean_inc(x_361);
x_362 = lean_ctor_get(x_355, 3);
lean_inc(x_362);
x_363 = lean_ctor_get(x_355, 4);
lean_inc(x_363);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 lean_ctor_release(x_355, 2);
 lean_ctor_release(x_355, 3);
 lean_ctor_release(x_355, 4);
 x_364 = x_355;
} else {
 lean_dec_ref(x_355);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_356, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_356, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_356, 3);
lean_inc(x_367);
x_368 = lean_ctor_get(x_356, 4);
lean_inc(x_368);
x_369 = lean_ctor_get(x_356, 5);
lean_inc(x_369);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 lean_ctor_release(x_356, 2);
 lean_ctor_release(x_356, 3);
 lean_ctor_release(x_356, 4);
 lean_ctor_release(x_356, 5);
 x_370 = x_356;
} else {
 lean_dec_ref(x_356);
 x_370 = lean_box(0);
}
x_371 = lean_ctor_get(x_357, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_357, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 x_373 = x_357;
} else {
 lean_dec_ref(x_357);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(0, 3, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_372);
lean_ctor_set(x_374, 2, x_75);
if (lean_is_scalar(x_370)) {
 x_375 = lean_alloc_ctor(0, 6, 0);
} else {
 x_375 = x_370;
}
lean_ctor_set(x_375, 0, x_365);
lean_ctor_set(x_375, 1, x_366);
lean_ctor_set(x_375, 2, x_374);
lean_ctor_set(x_375, 3, x_367);
lean_ctor_set(x_375, 4, x_368);
lean_ctor_set(x_375, 5, x_369);
if (lean_is_scalar(x_364)) {
 x_376 = lean_alloc_ctor(0, 5, 0);
} else {
 x_376 = x_364;
}
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_360);
lean_ctor_set(x_376, 2, x_361);
lean_ctor_set(x_376, 3, x_362);
lean_ctor_set(x_376, 4, x_363);
if (lean_is_scalar(x_359)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_359;
}
lean_ctor_set(x_377, 0, x_358);
lean_ctor_set(x_377, 1, x_376);
return x_377;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_378 = lean_ctor_get(x_354, 1);
lean_inc(x_378);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_379, 2);
lean_inc(x_380);
x_381 = lean_ctor_get(x_354, 0);
lean_inc(x_381);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_382 = x_354;
} else {
 lean_dec_ref(x_354);
 x_382 = lean_box(0);
}
x_383 = lean_ctor_get(x_378, 1);
lean_inc(x_383);
x_384 = lean_ctor_get(x_378, 2);
lean_inc(x_384);
x_385 = lean_ctor_get(x_378, 3);
lean_inc(x_385);
x_386 = lean_ctor_get(x_378, 4);
lean_inc(x_386);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 lean_ctor_release(x_378, 4);
 x_387 = x_378;
} else {
 lean_dec_ref(x_378);
 x_387 = lean_box(0);
}
x_388 = lean_ctor_get(x_379, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_379, 1);
lean_inc(x_389);
x_390 = lean_ctor_get(x_379, 3);
lean_inc(x_390);
x_391 = lean_ctor_get(x_379, 4);
lean_inc(x_391);
x_392 = lean_ctor_get(x_379, 5);
lean_inc(x_392);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 lean_ctor_release(x_379, 2);
 lean_ctor_release(x_379, 3);
 lean_ctor_release(x_379, 4);
 lean_ctor_release(x_379, 5);
 x_393 = x_379;
} else {
 lean_dec_ref(x_379);
 x_393 = lean_box(0);
}
x_394 = lean_ctor_get(x_380, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_380, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 lean_ctor_release(x_380, 2);
 x_396 = x_380;
} else {
 lean_dec_ref(x_380);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(0, 3, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_394);
lean_ctor_set(x_397, 1, x_395);
lean_ctor_set(x_397, 2, x_75);
if (lean_is_scalar(x_393)) {
 x_398 = lean_alloc_ctor(0, 6, 0);
} else {
 x_398 = x_393;
}
lean_ctor_set(x_398, 0, x_388);
lean_ctor_set(x_398, 1, x_389);
lean_ctor_set(x_398, 2, x_397);
lean_ctor_set(x_398, 3, x_390);
lean_ctor_set(x_398, 4, x_391);
lean_ctor_set(x_398, 5, x_392);
if (lean_is_scalar(x_387)) {
 x_399 = lean_alloc_ctor(0, 5, 0);
} else {
 x_399 = x_387;
}
lean_ctor_set(x_399, 0, x_398);
lean_ctor_set(x_399, 1, x_383);
lean_ctor_set(x_399, 2, x_384);
lean_ctor_set(x_399, 3, x_385);
lean_ctor_set(x_399, 4, x_386);
if (lean_is_scalar(x_382)) {
 x_400 = lean_alloc_ctor(1, 2, 0);
} else {
 x_400 = x_382;
}
lean_ctor_set(x_400, 0, x_381);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_350);
lean_dec(x_24);
x_401 = lean_ctor_get(x_351, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_402, 2);
lean_inc(x_403);
x_404 = lean_ctor_get(x_351, 0);
lean_inc(x_404);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_405 = x_351;
} else {
 lean_dec_ref(x_351);
 x_405 = lean_box(0);
}
x_406 = lean_ctor_get(x_401, 1);
lean_inc(x_406);
x_407 = lean_ctor_get(x_401, 2);
lean_inc(x_407);
x_408 = lean_ctor_get(x_401, 3);
lean_inc(x_408);
x_409 = lean_ctor_get(x_401, 4);
lean_inc(x_409);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 lean_ctor_release(x_401, 2);
 lean_ctor_release(x_401, 3);
 lean_ctor_release(x_401, 4);
 x_410 = x_401;
} else {
 lean_dec_ref(x_401);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_402, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_402, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_402, 3);
lean_inc(x_413);
x_414 = lean_ctor_get(x_402, 4);
lean_inc(x_414);
x_415 = lean_ctor_get(x_402, 5);
lean_inc(x_415);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 lean_ctor_release(x_402, 2);
 lean_ctor_release(x_402, 3);
 lean_ctor_release(x_402, 4);
 lean_ctor_release(x_402, 5);
 x_416 = x_402;
} else {
 lean_dec_ref(x_402);
 x_416 = lean_box(0);
}
x_417 = lean_ctor_get(x_403, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_403, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 x_419 = x_403;
} else {
 lean_dec_ref(x_403);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(0, 3, 0);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_418);
lean_ctor_set(x_420, 2, x_75);
if (lean_is_scalar(x_416)) {
 x_421 = lean_alloc_ctor(0, 6, 0);
} else {
 x_421 = x_416;
}
lean_ctor_set(x_421, 0, x_411);
lean_ctor_set(x_421, 1, x_412);
lean_ctor_set(x_421, 2, x_420);
lean_ctor_set(x_421, 3, x_413);
lean_ctor_set(x_421, 4, x_414);
lean_ctor_set(x_421, 5, x_415);
if (lean_is_scalar(x_410)) {
 x_422 = lean_alloc_ctor(0, 5, 0);
} else {
 x_422 = x_410;
}
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_406);
lean_ctor_set(x_422, 2, x_407);
lean_ctor_set(x_422, 3, x_408);
lean_ctor_set(x_422, 4, x_409);
if (lean_is_scalar(x_405)) {
 x_423 = lean_alloc_ctor(1, 2, 0);
} else {
 x_423 = x_405;
}
lean_ctor_set(x_423, 0, x_404);
lean_ctor_set(x_423, 1, x_422);
return x_423;
}
}
}
}
else
{
uint8_t x_424; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_3);
x_424 = !lean_is_exclusive(x_20);
if (x_424 == 0)
{
return x_20;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_20, 0);
x_426 = lean_ctor_get(x_20, 1);
lean_inc(x_426);
lean_inc(x_425);
lean_dec(x_20);
x_427 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set(x_427, 1, x_426);
return x_427;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabForall(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabForall");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabForall(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
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
x_1 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
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
x_3 = l_Lean_FileMap_ofString___closed__1;
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
x_13 = l_Lean_Syntax_asNode___closed__1;
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
lean_object* _init_l_Lean_Elab_Term_elabArrow___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_forall___elambda__1___closed__1;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrow___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_List_format___rarg___closed__2;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrow___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_2 = l_Lean_Elab_Term_elabArrow___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___rarg(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_Lean_mkIdentFrom(x_1, x_6);
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
x_13 = l_Lean_stxInh;
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get(x_13, x_8, x_14);
x_16 = l_Lean_Elab_Term_mkExplicitBinder(x_9, x_15);
x_17 = l_Lean_FileMap_ofString___closed__1;
x_18 = lean_array_push(x_17, x_16);
x_19 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_19);
x_20 = l_Lean_Elab_Term_elabArrow___closed__3;
x_21 = lean_array_push(x_20, x_1);
x_22 = l_Lean_Elab_Term_elabArrow___closed__2;
x_23 = lean_array_push(x_21, x_22);
x_24 = lean_unsigned_to_nat(2u);
x_25 = lean_array_get(x_13, x_8, x_24);
lean_dec(x_8);
x_26 = lean_array_push(x_23, x_25);
x_27 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Elab_Term_elabTerm(x_28, x_2, x_3, x_7);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_1);
x_30 = l_Lean_stxInh;
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_array_get(x_30, x_8, x_31);
x_33 = l_Lean_Elab_Term_mkExplicitBinder(x_9, x_32);
x_34 = l_Lean_FileMap_ofString___closed__1;
x_35 = lean_array_push(x_34, x_33);
x_36 = l_Lean_nullKind;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Elab_Term_elabArrow___closed__3;
x_39 = lean_array_push(x_38, x_37);
x_40 = l_Lean_Elab_Term_elabArrow___closed__2;
x_41 = lean_array_push(x_39, x_40);
x_42 = lean_unsigned_to_nat(2u);
x_43 = lean_array_get(x_30, x_8, x_42);
lean_dec(x_8);
x_44 = lean_array_push(x_41, x_43);
x_45 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_Elab_Term_elabTerm(x_46, x_2, x_3, x_7);
return x_47;
}
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabArrow");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabArrow), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrow(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabDepArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Elab_Term_getLCtx(x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_stxInh;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_9, x_5, x_10);
x_12 = l_Lean_FileMap_ofString___closed__1;
x_13 = lean_array_push(x_12, x_11);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_array_get(x_9, x_5, x_14);
x_16 = l_Lean_Elab_Term_getLocalInsts(x_3, x_8);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Array_empty___closed__1;
lean_inc(x_3);
lean_inc(x_17);
x_20 = l___private_Init_Lean_Elab_Term_8__elabBindersAux___main(x_13, x_10, x_19, x_7, x_17, x_3, x_18);
lean_dec(x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_array_get_size(x_17);
lean_dec(x_17);
x_28 = lean_array_get_size(x_26);
x_29 = lean_nat_dec_lt(x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_3);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_3, 0);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 2);
lean_dec(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_dec(x_34);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 1, x_25);
lean_inc(x_3);
x_35 = l_Lean_Elab_Term_elabType(x_15, x_3, x_23);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Term_mkForall(x_24, x_36, x_3, x_37);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_3);
lean_dec(x_24);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 0);
lean_inc(x_43);
lean_dec(x_31);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_25);
lean_ctor_set(x_44, 2, x_26);
lean_ctor_set(x_3, 0, x_44);
lean_inc(x_3);
x_45 = l_Lean_Elab_Term_elabType(x_15, x_3, x_23);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Elab_Term_mkForall(x_24, x_46, x_3, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_3);
lean_dec(x_24);
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_51 = x_45;
} else {
 lean_dec_ref(x_45);
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
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_53 = lean_ctor_get(x_3, 0);
x_54 = lean_ctor_get(x_3, 1);
x_55 = lean_ctor_get(x_3, 2);
x_56 = lean_ctor_get(x_3, 3);
x_57 = lean_ctor_get(x_3, 4);
x_58 = lean_ctor_get(x_3, 5);
x_59 = lean_ctor_get(x_3, 6);
x_60 = lean_ctor_get(x_3, 7);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_3);
x_61 = lean_ctor_get(x_53, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 x_62 = x_53;
} else {
 lean_dec_ref(x_53);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 3, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_25);
lean_ctor_set(x_63, 2, x_26);
x_64 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_54);
lean_ctor_set(x_64, 2, x_55);
lean_ctor_set(x_64, 3, x_56);
lean_ctor_set(x_64, 4, x_57);
lean_ctor_set(x_64, 5, x_58);
lean_ctor_set(x_64, 6, x_59);
lean_ctor_set(x_64, 7, x_60);
lean_inc(x_64);
x_65 = l_Lean_Elab_Term_elabType(x_15, x_64, x_23);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Elab_Term_mkForall(x_24, x_66, x_64, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_64);
lean_dec(x_24);
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_71 = x_65;
} else {
 lean_dec_ref(x_65);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_73 = lean_ctor_get(x_23, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 2);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_ctor_get(x_74, 2);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_23);
x_77 = lean_ctor_get(x_3, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = !lean_is_exclusive(x_3);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_3, 0);
lean_dec(x_80);
x_81 = !lean_is_exclusive(x_77);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_77, 2);
lean_dec(x_82);
x_83 = lean_ctor_get(x_77, 1);
lean_dec(x_83);
lean_ctor_set(x_77, 2, x_26);
lean_ctor_set(x_77, 1, x_25);
lean_inc(x_3);
x_84 = l_Lean_Elab_Term_elabType(x_15, x_3, x_78);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Elab_Term_mkForall(x_24, x_85, x_3, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 2);
lean_inc(x_90);
x_91 = !lean_is_exclusive(x_87);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_87, 1);
lean_dec(x_92);
x_93 = !lean_is_exclusive(x_88);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_88, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_89);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_89, 2);
lean_dec(x_96);
x_97 = !lean_is_exclusive(x_90);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_90, 2);
lean_dec(x_98);
lean_ctor_set(x_90, 2, x_75);
return x_87;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_90, 0);
x_100 = lean_ctor_get(x_90, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_90);
x_101 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_101, 2, x_75);
lean_ctor_set(x_89, 2, x_101);
return x_87;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_102 = lean_ctor_get(x_89, 0);
x_103 = lean_ctor_get(x_89, 1);
x_104 = lean_ctor_get(x_89, 3);
x_105 = lean_ctor_get(x_89, 4);
x_106 = lean_ctor_get(x_89, 5);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_89);
x_107 = lean_ctor_get(x_90, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_90, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 x_109 = x_90;
} else {
 lean_dec_ref(x_90);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(0, 3, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
lean_ctor_set(x_110, 2, x_75);
x_111 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_111, 0, x_102);
lean_ctor_set(x_111, 1, x_103);
lean_ctor_set(x_111, 2, x_110);
lean_ctor_set(x_111, 3, x_104);
lean_ctor_set(x_111, 4, x_105);
lean_ctor_set(x_111, 5, x_106);
lean_ctor_set(x_88, 0, x_111);
return x_87;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_112 = lean_ctor_get(x_88, 1);
x_113 = lean_ctor_get(x_88, 2);
x_114 = lean_ctor_get(x_88, 3);
x_115 = lean_ctor_get(x_88, 4);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_88);
x_116 = lean_ctor_get(x_89, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_89, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_89, 3);
lean_inc(x_118);
x_119 = lean_ctor_get(x_89, 4);
lean_inc(x_119);
x_120 = lean_ctor_get(x_89, 5);
lean_inc(x_120);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 lean_ctor_release(x_89, 4);
 lean_ctor_release(x_89, 5);
 x_121 = x_89;
} else {
 lean_dec_ref(x_89);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_90, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_90, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 x_124 = x_90;
} else {
 lean_dec_ref(x_90);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 3, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
lean_ctor_set(x_125, 2, x_75);
if (lean_is_scalar(x_121)) {
 x_126 = lean_alloc_ctor(0, 6, 0);
} else {
 x_126 = x_121;
}
lean_ctor_set(x_126, 0, x_116);
lean_ctor_set(x_126, 1, x_117);
lean_ctor_set(x_126, 2, x_125);
lean_ctor_set(x_126, 3, x_118);
lean_ctor_set(x_126, 4, x_119);
lean_ctor_set(x_126, 5, x_120);
x_127 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_112);
lean_ctor_set(x_127, 2, x_113);
lean_ctor_set(x_127, 3, x_114);
lean_ctor_set(x_127, 4, x_115);
lean_ctor_set(x_87, 1, x_127);
return x_87;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_128 = lean_ctor_get(x_87, 0);
lean_inc(x_128);
lean_dec(x_87);
x_129 = lean_ctor_get(x_88, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_88, 2);
lean_inc(x_130);
x_131 = lean_ctor_get(x_88, 3);
lean_inc(x_131);
x_132 = lean_ctor_get(x_88, 4);
lean_inc(x_132);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 lean_ctor_release(x_88, 4);
 x_133 = x_88;
} else {
 lean_dec_ref(x_88);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_89, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_89, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_89, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_89, 4);
lean_inc(x_137);
x_138 = lean_ctor_get(x_89, 5);
lean_inc(x_138);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 lean_ctor_release(x_89, 4);
 lean_ctor_release(x_89, 5);
 x_139 = x_89;
} else {
 lean_dec_ref(x_89);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_90, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_90, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 x_142 = x_90;
} else {
 lean_dec_ref(x_90);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 3, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
lean_ctor_set(x_143, 2, x_75);
if (lean_is_scalar(x_139)) {
 x_144 = lean_alloc_ctor(0, 6, 0);
} else {
 x_144 = x_139;
}
lean_ctor_set(x_144, 0, x_134);
lean_ctor_set(x_144, 1, x_135);
lean_ctor_set(x_144, 2, x_143);
lean_ctor_set(x_144, 3, x_136);
lean_ctor_set(x_144, 4, x_137);
lean_ctor_set(x_144, 5, x_138);
if (lean_is_scalar(x_133)) {
 x_145 = lean_alloc_ctor(0, 5, 0);
} else {
 x_145 = x_133;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_129);
lean_ctor_set(x_145, 2, x_130);
lean_ctor_set(x_145, 3, x_131);
lean_ctor_set(x_145, 4, x_132);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_128);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_147 = lean_ctor_get(x_87, 1);
lean_inc(x_147);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_148, 2);
lean_inc(x_149);
x_150 = !lean_is_exclusive(x_87);
if (x_150 == 0)
{
lean_object* x_151; uint8_t x_152; 
x_151 = lean_ctor_get(x_87, 1);
lean_dec(x_151);
x_152 = !lean_is_exclusive(x_147);
if (x_152 == 0)
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_ctor_get(x_147, 0);
lean_dec(x_153);
x_154 = !lean_is_exclusive(x_148);
if (x_154 == 0)
{
lean_object* x_155; uint8_t x_156; 
x_155 = lean_ctor_get(x_148, 2);
lean_dec(x_155);
x_156 = !lean_is_exclusive(x_149);
if (x_156 == 0)
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_149, 2);
lean_dec(x_157);
lean_ctor_set(x_149, 2, x_75);
return x_87;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_149, 0);
x_159 = lean_ctor_get(x_149, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_149);
x_160 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set(x_160, 2, x_75);
lean_ctor_set(x_148, 2, x_160);
return x_87;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_161 = lean_ctor_get(x_148, 0);
x_162 = lean_ctor_get(x_148, 1);
x_163 = lean_ctor_get(x_148, 3);
x_164 = lean_ctor_get(x_148, 4);
x_165 = lean_ctor_get(x_148, 5);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_148);
x_166 = lean_ctor_get(x_149, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_149, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 lean_ctor_release(x_149, 2);
 x_168 = x_149;
} else {
 lean_dec_ref(x_149);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(0, 3, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
lean_ctor_set(x_169, 2, x_75);
x_170 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_170, 0, x_161);
lean_ctor_set(x_170, 1, x_162);
lean_ctor_set(x_170, 2, x_169);
lean_ctor_set(x_170, 3, x_163);
lean_ctor_set(x_170, 4, x_164);
lean_ctor_set(x_170, 5, x_165);
lean_ctor_set(x_147, 0, x_170);
return x_87;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_171 = lean_ctor_get(x_147, 1);
x_172 = lean_ctor_get(x_147, 2);
x_173 = lean_ctor_get(x_147, 3);
x_174 = lean_ctor_get(x_147, 4);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_147);
x_175 = lean_ctor_get(x_148, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_148, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_148, 3);
lean_inc(x_177);
x_178 = lean_ctor_get(x_148, 4);
lean_inc(x_178);
x_179 = lean_ctor_get(x_148, 5);
lean_inc(x_179);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 lean_ctor_release(x_148, 2);
 lean_ctor_release(x_148, 3);
 lean_ctor_release(x_148, 4);
 lean_ctor_release(x_148, 5);
 x_180 = x_148;
} else {
 lean_dec_ref(x_148);
 x_180 = lean_box(0);
}
x_181 = lean_ctor_get(x_149, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_149, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 lean_ctor_release(x_149, 2);
 x_183 = x_149;
} else {
 lean_dec_ref(x_149);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(0, 3, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
lean_ctor_set(x_184, 2, x_75);
if (lean_is_scalar(x_180)) {
 x_185 = lean_alloc_ctor(0, 6, 0);
} else {
 x_185 = x_180;
}
lean_ctor_set(x_185, 0, x_175);
lean_ctor_set(x_185, 1, x_176);
lean_ctor_set(x_185, 2, x_184);
lean_ctor_set(x_185, 3, x_177);
lean_ctor_set(x_185, 4, x_178);
lean_ctor_set(x_185, 5, x_179);
x_186 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_171);
lean_ctor_set(x_186, 2, x_172);
lean_ctor_set(x_186, 3, x_173);
lean_ctor_set(x_186, 4, x_174);
lean_ctor_set(x_87, 1, x_186);
return x_87;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_187 = lean_ctor_get(x_87, 0);
lean_inc(x_187);
lean_dec(x_87);
x_188 = lean_ctor_get(x_147, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_147, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_147, 3);
lean_inc(x_190);
x_191 = lean_ctor_get(x_147, 4);
lean_inc(x_191);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 lean_ctor_release(x_147, 2);
 lean_ctor_release(x_147, 3);
 lean_ctor_release(x_147, 4);
 x_192 = x_147;
} else {
 lean_dec_ref(x_147);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_148, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_148, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_148, 3);
lean_inc(x_195);
x_196 = lean_ctor_get(x_148, 4);
lean_inc(x_196);
x_197 = lean_ctor_get(x_148, 5);
lean_inc(x_197);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 lean_ctor_release(x_148, 2);
 lean_ctor_release(x_148, 3);
 lean_ctor_release(x_148, 4);
 lean_ctor_release(x_148, 5);
 x_198 = x_148;
} else {
 lean_dec_ref(x_148);
 x_198 = lean_box(0);
}
x_199 = lean_ctor_get(x_149, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_149, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 lean_ctor_release(x_149, 2);
 x_201 = x_149;
} else {
 lean_dec_ref(x_149);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 3, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
lean_ctor_set(x_202, 2, x_75);
if (lean_is_scalar(x_198)) {
 x_203 = lean_alloc_ctor(0, 6, 0);
} else {
 x_203 = x_198;
}
lean_ctor_set(x_203, 0, x_193);
lean_ctor_set(x_203, 1, x_194);
lean_ctor_set(x_203, 2, x_202);
lean_ctor_set(x_203, 3, x_195);
lean_ctor_set(x_203, 4, x_196);
lean_ctor_set(x_203, 5, x_197);
if (lean_is_scalar(x_192)) {
 x_204 = lean_alloc_ctor(0, 5, 0);
} else {
 x_204 = x_192;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_188);
lean_ctor_set(x_204, 2, x_189);
lean_ctor_set(x_204, 3, x_190);
lean_ctor_set(x_204, 4, x_191);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_187);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
lean_dec(x_3);
lean_dec(x_24);
x_206 = lean_ctor_get(x_84, 1);
lean_inc(x_206);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_207, 2);
lean_inc(x_208);
x_209 = !lean_is_exclusive(x_84);
if (x_209 == 0)
{
lean_object* x_210; uint8_t x_211; 
x_210 = lean_ctor_get(x_84, 1);
lean_dec(x_210);
x_211 = !lean_is_exclusive(x_206);
if (x_211 == 0)
{
lean_object* x_212; uint8_t x_213; 
x_212 = lean_ctor_get(x_206, 0);
lean_dec(x_212);
x_213 = !lean_is_exclusive(x_207);
if (x_213 == 0)
{
lean_object* x_214; uint8_t x_215; 
x_214 = lean_ctor_get(x_207, 2);
lean_dec(x_214);
x_215 = !lean_is_exclusive(x_208);
if (x_215 == 0)
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_208, 2);
lean_dec(x_216);
lean_ctor_set(x_208, 2, x_75);
return x_84;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_208, 0);
x_218 = lean_ctor_get(x_208, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_208);
x_219 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
lean_ctor_set(x_219, 2, x_75);
lean_ctor_set(x_207, 2, x_219);
return x_84;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_220 = lean_ctor_get(x_207, 0);
x_221 = lean_ctor_get(x_207, 1);
x_222 = lean_ctor_get(x_207, 3);
x_223 = lean_ctor_get(x_207, 4);
x_224 = lean_ctor_get(x_207, 5);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_207);
x_225 = lean_ctor_get(x_208, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_208, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 x_227 = x_208;
} else {
 lean_dec_ref(x_208);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(0, 3, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
lean_ctor_set(x_228, 2, x_75);
x_229 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_229, 0, x_220);
lean_ctor_set(x_229, 1, x_221);
lean_ctor_set(x_229, 2, x_228);
lean_ctor_set(x_229, 3, x_222);
lean_ctor_set(x_229, 4, x_223);
lean_ctor_set(x_229, 5, x_224);
lean_ctor_set(x_206, 0, x_229);
return x_84;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_230 = lean_ctor_get(x_206, 1);
x_231 = lean_ctor_get(x_206, 2);
x_232 = lean_ctor_get(x_206, 3);
x_233 = lean_ctor_get(x_206, 4);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_206);
x_234 = lean_ctor_get(x_207, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_207, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_207, 3);
lean_inc(x_236);
x_237 = lean_ctor_get(x_207, 4);
lean_inc(x_237);
x_238 = lean_ctor_get(x_207, 5);
lean_inc(x_238);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 lean_ctor_release(x_207, 4);
 lean_ctor_release(x_207, 5);
 x_239 = x_207;
} else {
 lean_dec_ref(x_207);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_208, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_208, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 x_242 = x_208;
} else {
 lean_dec_ref(x_208);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(0, 3, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
lean_ctor_set(x_243, 2, x_75);
if (lean_is_scalar(x_239)) {
 x_244 = lean_alloc_ctor(0, 6, 0);
} else {
 x_244 = x_239;
}
lean_ctor_set(x_244, 0, x_234);
lean_ctor_set(x_244, 1, x_235);
lean_ctor_set(x_244, 2, x_243);
lean_ctor_set(x_244, 3, x_236);
lean_ctor_set(x_244, 4, x_237);
lean_ctor_set(x_244, 5, x_238);
x_245 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_230);
lean_ctor_set(x_245, 2, x_231);
lean_ctor_set(x_245, 3, x_232);
lean_ctor_set(x_245, 4, x_233);
lean_ctor_set(x_84, 1, x_245);
return x_84;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_246 = lean_ctor_get(x_84, 0);
lean_inc(x_246);
lean_dec(x_84);
x_247 = lean_ctor_get(x_206, 1);
lean_inc(x_247);
x_248 = lean_ctor_get(x_206, 2);
lean_inc(x_248);
x_249 = lean_ctor_get(x_206, 3);
lean_inc(x_249);
x_250 = lean_ctor_get(x_206, 4);
lean_inc(x_250);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 lean_ctor_release(x_206, 2);
 lean_ctor_release(x_206, 3);
 lean_ctor_release(x_206, 4);
 x_251 = x_206;
} else {
 lean_dec_ref(x_206);
 x_251 = lean_box(0);
}
x_252 = lean_ctor_get(x_207, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_207, 1);
lean_inc(x_253);
x_254 = lean_ctor_get(x_207, 3);
lean_inc(x_254);
x_255 = lean_ctor_get(x_207, 4);
lean_inc(x_255);
x_256 = lean_ctor_get(x_207, 5);
lean_inc(x_256);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 lean_ctor_release(x_207, 4);
 lean_ctor_release(x_207, 5);
 x_257 = x_207;
} else {
 lean_dec_ref(x_207);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_208, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_208, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 x_260 = x_208;
} else {
 lean_dec_ref(x_208);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(0, 3, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
lean_ctor_set(x_261, 2, x_75);
if (lean_is_scalar(x_257)) {
 x_262 = lean_alloc_ctor(0, 6, 0);
} else {
 x_262 = x_257;
}
lean_ctor_set(x_262, 0, x_252);
lean_ctor_set(x_262, 1, x_253);
lean_ctor_set(x_262, 2, x_261);
lean_ctor_set(x_262, 3, x_254);
lean_ctor_set(x_262, 4, x_255);
lean_ctor_set(x_262, 5, x_256);
if (lean_is_scalar(x_251)) {
 x_263 = lean_alloc_ctor(0, 5, 0);
} else {
 x_263 = x_251;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_247);
lean_ctor_set(x_263, 2, x_248);
lean_ctor_set(x_263, 3, x_249);
lean_ctor_set(x_263, 4, x_250);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_246);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_77, 0);
lean_inc(x_265);
lean_dec(x_77);
x_266 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_25);
lean_ctor_set(x_266, 2, x_26);
lean_ctor_set(x_3, 0, x_266);
lean_inc(x_3);
x_267 = l_Lean_Elab_Term_elabType(x_15, x_3, x_78);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
x_270 = l_Lean_Elab_Term_mkForall(x_24, x_268, x_3, x_269);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_272, 2);
lean_inc(x_273);
x_274 = lean_ctor_get(x_270, 0);
lean_inc(x_274);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_275 = x_270;
} else {
 lean_dec_ref(x_270);
 x_275 = lean_box(0);
}
x_276 = lean_ctor_get(x_271, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_271, 2);
lean_inc(x_277);
x_278 = lean_ctor_get(x_271, 3);
lean_inc(x_278);
x_279 = lean_ctor_get(x_271, 4);
lean_inc(x_279);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 lean_ctor_release(x_271, 3);
 lean_ctor_release(x_271, 4);
 x_280 = x_271;
} else {
 lean_dec_ref(x_271);
 x_280 = lean_box(0);
}
x_281 = lean_ctor_get(x_272, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_272, 1);
lean_inc(x_282);
x_283 = lean_ctor_get(x_272, 3);
lean_inc(x_283);
x_284 = lean_ctor_get(x_272, 4);
lean_inc(x_284);
x_285 = lean_ctor_get(x_272, 5);
lean_inc(x_285);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 lean_ctor_release(x_272, 3);
 lean_ctor_release(x_272, 4);
 lean_ctor_release(x_272, 5);
 x_286 = x_272;
} else {
 lean_dec_ref(x_272);
 x_286 = lean_box(0);
}
x_287 = lean_ctor_get(x_273, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_273, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 lean_ctor_release(x_273, 2);
 x_289 = x_273;
} else {
 lean_dec_ref(x_273);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(0, 3, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_288);
lean_ctor_set(x_290, 2, x_75);
if (lean_is_scalar(x_286)) {
 x_291 = lean_alloc_ctor(0, 6, 0);
} else {
 x_291 = x_286;
}
lean_ctor_set(x_291, 0, x_281);
lean_ctor_set(x_291, 1, x_282);
lean_ctor_set(x_291, 2, x_290);
lean_ctor_set(x_291, 3, x_283);
lean_ctor_set(x_291, 4, x_284);
lean_ctor_set(x_291, 5, x_285);
if (lean_is_scalar(x_280)) {
 x_292 = lean_alloc_ctor(0, 5, 0);
} else {
 x_292 = x_280;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_276);
lean_ctor_set(x_292, 2, x_277);
lean_ctor_set(x_292, 3, x_278);
lean_ctor_set(x_292, 4, x_279);
if (lean_is_scalar(x_275)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_275;
}
lean_ctor_set(x_293, 0, x_274);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_294 = lean_ctor_get(x_270, 1);
lean_inc(x_294);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_295, 2);
lean_inc(x_296);
x_297 = lean_ctor_get(x_270, 0);
lean_inc(x_297);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_298 = x_270;
} else {
 lean_dec_ref(x_270);
 x_298 = lean_box(0);
}
x_299 = lean_ctor_get(x_294, 1);
lean_inc(x_299);
x_300 = lean_ctor_get(x_294, 2);
lean_inc(x_300);
x_301 = lean_ctor_get(x_294, 3);
lean_inc(x_301);
x_302 = lean_ctor_get(x_294, 4);
lean_inc(x_302);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 lean_ctor_release(x_294, 2);
 lean_ctor_release(x_294, 3);
 lean_ctor_release(x_294, 4);
 x_303 = x_294;
} else {
 lean_dec_ref(x_294);
 x_303 = lean_box(0);
}
x_304 = lean_ctor_get(x_295, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_295, 1);
lean_inc(x_305);
x_306 = lean_ctor_get(x_295, 3);
lean_inc(x_306);
x_307 = lean_ctor_get(x_295, 4);
lean_inc(x_307);
x_308 = lean_ctor_get(x_295, 5);
lean_inc(x_308);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 lean_ctor_release(x_295, 2);
 lean_ctor_release(x_295, 3);
 lean_ctor_release(x_295, 4);
 lean_ctor_release(x_295, 5);
 x_309 = x_295;
} else {
 lean_dec_ref(x_295);
 x_309 = lean_box(0);
}
x_310 = lean_ctor_get(x_296, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_296, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 lean_ctor_release(x_296, 2);
 x_312 = x_296;
} else {
 lean_dec_ref(x_296);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(0, 3, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_311);
lean_ctor_set(x_313, 2, x_75);
if (lean_is_scalar(x_309)) {
 x_314 = lean_alloc_ctor(0, 6, 0);
} else {
 x_314 = x_309;
}
lean_ctor_set(x_314, 0, x_304);
lean_ctor_set(x_314, 1, x_305);
lean_ctor_set(x_314, 2, x_313);
lean_ctor_set(x_314, 3, x_306);
lean_ctor_set(x_314, 4, x_307);
lean_ctor_set(x_314, 5, x_308);
if (lean_is_scalar(x_303)) {
 x_315 = lean_alloc_ctor(0, 5, 0);
} else {
 x_315 = x_303;
}
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_299);
lean_ctor_set(x_315, 2, x_300);
lean_ctor_set(x_315, 3, x_301);
lean_ctor_set(x_315, 4, x_302);
if (lean_is_scalar(x_298)) {
 x_316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_316 = x_298;
}
lean_ctor_set(x_316, 0, x_297);
lean_ctor_set(x_316, 1, x_315);
return x_316;
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_3);
lean_dec(x_24);
x_317 = lean_ctor_get(x_267, 1);
lean_inc(x_317);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_318, 2);
lean_inc(x_319);
x_320 = lean_ctor_get(x_267, 0);
lean_inc(x_320);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_321 = x_267;
} else {
 lean_dec_ref(x_267);
 x_321 = lean_box(0);
}
x_322 = lean_ctor_get(x_317, 1);
lean_inc(x_322);
x_323 = lean_ctor_get(x_317, 2);
lean_inc(x_323);
x_324 = lean_ctor_get(x_317, 3);
lean_inc(x_324);
x_325 = lean_ctor_get(x_317, 4);
lean_inc(x_325);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 lean_ctor_release(x_317, 2);
 lean_ctor_release(x_317, 3);
 lean_ctor_release(x_317, 4);
 x_326 = x_317;
} else {
 lean_dec_ref(x_317);
 x_326 = lean_box(0);
}
x_327 = lean_ctor_get(x_318, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_318, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_318, 3);
lean_inc(x_329);
x_330 = lean_ctor_get(x_318, 4);
lean_inc(x_330);
x_331 = lean_ctor_get(x_318, 5);
lean_inc(x_331);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 lean_ctor_release(x_318, 2);
 lean_ctor_release(x_318, 3);
 lean_ctor_release(x_318, 4);
 lean_ctor_release(x_318, 5);
 x_332 = x_318;
} else {
 lean_dec_ref(x_318);
 x_332 = lean_box(0);
}
x_333 = lean_ctor_get(x_319, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_319, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 lean_ctor_release(x_319, 2);
 x_335 = x_319;
} else {
 lean_dec_ref(x_319);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(0, 3, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_333);
lean_ctor_set(x_336, 1, x_334);
lean_ctor_set(x_336, 2, x_75);
if (lean_is_scalar(x_332)) {
 x_337 = lean_alloc_ctor(0, 6, 0);
} else {
 x_337 = x_332;
}
lean_ctor_set(x_337, 0, x_327);
lean_ctor_set(x_337, 1, x_328);
lean_ctor_set(x_337, 2, x_336);
lean_ctor_set(x_337, 3, x_329);
lean_ctor_set(x_337, 4, x_330);
lean_ctor_set(x_337, 5, x_331);
if (lean_is_scalar(x_326)) {
 x_338 = lean_alloc_ctor(0, 5, 0);
} else {
 x_338 = x_326;
}
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_322);
lean_ctor_set(x_338, 2, x_323);
lean_ctor_set(x_338, 3, x_324);
lean_ctor_set(x_338, 4, x_325);
if (lean_is_scalar(x_321)) {
 x_339 = lean_alloc_ctor(1, 2, 0);
} else {
 x_339 = x_321;
}
lean_ctor_set(x_339, 0, x_320);
lean_ctor_set(x_339, 1, x_338);
return x_339;
}
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_340 = lean_ctor_get(x_3, 1);
x_341 = lean_ctor_get(x_3, 2);
x_342 = lean_ctor_get(x_3, 3);
x_343 = lean_ctor_get(x_3, 4);
x_344 = lean_ctor_get(x_3, 5);
x_345 = lean_ctor_get(x_3, 6);
x_346 = lean_ctor_get(x_3, 7);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_3);
x_347 = lean_ctor_get(x_77, 0);
lean_inc(x_347);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 x_348 = x_77;
} else {
 lean_dec_ref(x_77);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(0, 3, 0);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_25);
lean_ctor_set(x_349, 2, x_26);
x_350 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_340);
lean_ctor_set(x_350, 2, x_341);
lean_ctor_set(x_350, 3, x_342);
lean_ctor_set(x_350, 4, x_343);
lean_ctor_set(x_350, 5, x_344);
lean_ctor_set(x_350, 6, x_345);
lean_ctor_set(x_350, 7, x_346);
lean_inc(x_350);
x_351 = l_Lean_Elab_Term_elabType(x_15, x_350, x_78);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = l_Lean_Elab_Term_mkForall(x_24, x_352, x_350, x_353);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_355 = lean_ctor_get(x_354, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_356, 2);
lean_inc(x_357);
x_358 = lean_ctor_get(x_354, 0);
lean_inc(x_358);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_359 = x_354;
} else {
 lean_dec_ref(x_354);
 x_359 = lean_box(0);
}
x_360 = lean_ctor_get(x_355, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_355, 2);
lean_inc(x_361);
x_362 = lean_ctor_get(x_355, 3);
lean_inc(x_362);
x_363 = lean_ctor_get(x_355, 4);
lean_inc(x_363);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 lean_ctor_release(x_355, 2);
 lean_ctor_release(x_355, 3);
 lean_ctor_release(x_355, 4);
 x_364 = x_355;
} else {
 lean_dec_ref(x_355);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_356, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_356, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_356, 3);
lean_inc(x_367);
x_368 = lean_ctor_get(x_356, 4);
lean_inc(x_368);
x_369 = lean_ctor_get(x_356, 5);
lean_inc(x_369);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 lean_ctor_release(x_356, 2);
 lean_ctor_release(x_356, 3);
 lean_ctor_release(x_356, 4);
 lean_ctor_release(x_356, 5);
 x_370 = x_356;
} else {
 lean_dec_ref(x_356);
 x_370 = lean_box(0);
}
x_371 = lean_ctor_get(x_357, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_357, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 x_373 = x_357;
} else {
 lean_dec_ref(x_357);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(0, 3, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_372);
lean_ctor_set(x_374, 2, x_75);
if (lean_is_scalar(x_370)) {
 x_375 = lean_alloc_ctor(0, 6, 0);
} else {
 x_375 = x_370;
}
lean_ctor_set(x_375, 0, x_365);
lean_ctor_set(x_375, 1, x_366);
lean_ctor_set(x_375, 2, x_374);
lean_ctor_set(x_375, 3, x_367);
lean_ctor_set(x_375, 4, x_368);
lean_ctor_set(x_375, 5, x_369);
if (lean_is_scalar(x_364)) {
 x_376 = lean_alloc_ctor(0, 5, 0);
} else {
 x_376 = x_364;
}
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_360);
lean_ctor_set(x_376, 2, x_361);
lean_ctor_set(x_376, 3, x_362);
lean_ctor_set(x_376, 4, x_363);
if (lean_is_scalar(x_359)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_359;
}
lean_ctor_set(x_377, 0, x_358);
lean_ctor_set(x_377, 1, x_376);
return x_377;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_378 = lean_ctor_get(x_354, 1);
lean_inc(x_378);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_379, 2);
lean_inc(x_380);
x_381 = lean_ctor_get(x_354, 0);
lean_inc(x_381);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_382 = x_354;
} else {
 lean_dec_ref(x_354);
 x_382 = lean_box(0);
}
x_383 = lean_ctor_get(x_378, 1);
lean_inc(x_383);
x_384 = lean_ctor_get(x_378, 2);
lean_inc(x_384);
x_385 = lean_ctor_get(x_378, 3);
lean_inc(x_385);
x_386 = lean_ctor_get(x_378, 4);
lean_inc(x_386);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 lean_ctor_release(x_378, 4);
 x_387 = x_378;
} else {
 lean_dec_ref(x_378);
 x_387 = lean_box(0);
}
x_388 = lean_ctor_get(x_379, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_379, 1);
lean_inc(x_389);
x_390 = lean_ctor_get(x_379, 3);
lean_inc(x_390);
x_391 = lean_ctor_get(x_379, 4);
lean_inc(x_391);
x_392 = lean_ctor_get(x_379, 5);
lean_inc(x_392);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 lean_ctor_release(x_379, 2);
 lean_ctor_release(x_379, 3);
 lean_ctor_release(x_379, 4);
 lean_ctor_release(x_379, 5);
 x_393 = x_379;
} else {
 lean_dec_ref(x_379);
 x_393 = lean_box(0);
}
x_394 = lean_ctor_get(x_380, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_380, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 lean_ctor_release(x_380, 2);
 x_396 = x_380;
} else {
 lean_dec_ref(x_380);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(0, 3, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_394);
lean_ctor_set(x_397, 1, x_395);
lean_ctor_set(x_397, 2, x_75);
if (lean_is_scalar(x_393)) {
 x_398 = lean_alloc_ctor(0, 6, 0);
} else {
 x_398 = x_393;
}
lean_ctor_set(x_398, 0, x_388);
lean_ctor_set(x_398, 1, x_389);
lean_ctor_set(x_398, 2, x_397);
lean_ctor_set(x_398, 3, x_390);
lean_ctor_set(x_398, 4, x_391);
lean_ctor_set(x_398, 5, x_392);
if (lean_is_scalar(x_387)) {
 x_399 = lean_alloc_ctor(0, 5, 0);
} else {
 x_399 = x_387;
}
lean_ctor_set(x_399, 0, x_398);
lean_ctor_set(x_399, 1, x_383);
lean_ctor_set(x_399, 2, x_384);
lean_ctor_set(x_399, 3, x_385);
lean_ctor_set(x_399, 4, x_386);
if (lean_is_scalar(x_382)) {
 x_400 = lean_alloc_ctor(1, 2, 0);
} else {
 x_400 = x_382;
}
lean_ctor_set(x_400, 0, x_381);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_350);
lean_dec(x_24);
x_401 = lean_ctor_get(x_351, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_402, 2);
lean_inc(x_403);
x_404 = lean_ctor_get(x_351, 0);
lean_inc(x_404);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_405 = x_351;
} else {
 lean_dec_ref(x_351);
 x_405 = lean_box(0);
}
x_406 = lean_ctor_get(x_401, 1);
lean_inc(x_406);
x_407 = lean_ctor_get(x_401, 2);
lean_inc(x_407);
x_408 = lean_ctor_get(x_401, 3);
lean_inc(x_408);
x_409 = lean_ctor_get(x_401, 4);
lean_inc(x_409);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 lean_ctor_release(x_401, 2);
 lean_ctor_release(x_401, 3);
 lean_ctor_release(x_401, 4);
 x_410 = x_401;
} else {
 lean_dec_ref(x_401);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_402, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_402, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_402, 3);
lean_inc(x_413);
x_414 = lean_ctor_get(x_402, 4);
lean_inc(x_414);
x_415 = lean_ctor_get(x_402, 5);
lean_inc(x_415);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 lean_ctor_release(x_402, 2);
 lean_ctor_release(x_402, 3);
 lean_ctor_release(x_402, 4);
 lean_ctor_release(x_402, 5);
 x_416 = x_402;
} else {
 lean_dec_ref(x_402);
 x_416 = lean_box(0);
}
x_417 = lean_ctor_get(x_403, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_403, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 lean_ctor_release(x_403, 2);
 x_419 = x_403;
} else {
 lean_dec_ref(x_403);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(0, 3, 0);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_418);
lean_ctor_set(x_420, 2, x_75);
if (lean_is_scalar(x_416)) {
 x_421 = lean_alloc_ctor(0, 6, 0);
} else {
 x_421 = x_416;
}
lean_ctor_set(x_421, 0, x_411);
lean_ctor_set(x_421, 1, x_412);
lean_ctor_set(x_421, 2, x_420);
lean_ctor_set(x_421, 3, x_413);
lean_ctor_set(x_421, 4, x_414);
lean_ctor_set(x_421, 5, x_415);
if (lean_is_scalar(x_410)) {
 x_422 = lean_alloc_ctor(0, 5, 0);
} else {
 x_422 = x_410;
}
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_406);
lean_ctor_set(x_422, 2, x_407);
lean_ctor_set(x_422, 3, x_408);
lean_ctor_set(x_422, 4, x_409);
if (lean_is_scalar(x_405)) {
 x_423 = lean_alloc_ctor(1, 2, 0);
} else {
 x_423 = x_405;
}
lean_ctor_set(x_423, 0, x_404);
lean_ctor_set(x_423, 1, x_422);
return x_423;
}
}
}
}
else
{
uint8_t x_424; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_3);
x_424 = !lean_is_exclusive(x_20);
if (x_424 == 0)
{
return x_20;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_20, 0);
x_426 = lean_ctor_get(x_20, 1);
lean_inc(x_426);
lean_inc(x_425);
lean_dec(x_20);
x_427 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set(x_427, 1, x_426);
return x_427;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabDepArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabDepArrow(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabDepArrow");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDepArrow___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_elabParen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unit");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabParen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareBuiltinParser___closed__5;
x_2 = l_Lean_Elab_Term_elabParen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabParen___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabParen___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabParen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_stxInh;
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_array_get(x_6, x_5, x_7);
x_9 = l_Lean_Syntax_isNone(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_8, x_10);
lean_dec(x_8);
x_12 = l_Lean_Elab_Term_elabTerm(x_11, x_2, x_3, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_13 = l_Lean_Elab_Term_elabParen___closed__3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
}
}
lean_object* l_Lean_Elab_Term_elabParen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabParen(x_1, x_2, x_3, x_4);
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
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParen___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabParen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_paren___elambda__1___closed__1;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Term_elabListLit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_10 = lean_array_push(x_9, x_8);
x_11 = lean_array_push(x_10, x_5);
x_12 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_13 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1(x_11, x_11, x_12, x_1);
lean_dec(x_11);
x_14 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_4 = x_14;
x_5 = x_13;
goto _start;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_stxInh;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get(x_6, x_5, x_7);
x_9 = l_Lean_Elab_Term_elabListLit___closed__3;
x_10 = l_Lean_mkIdentFrom(x_8, x_9);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_array_get(x_6, x_5, x_11);
x_13 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_array_get(x_6, x_5, x_14);
x_16 = l_Lean_Elab_Term_elabListLit___closed__5;
x_17 = l_Lean_mkIdentFrom(x_15, x_16);
lean_dec(x_15);
x_18 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Term_elabListLit___spec__1(x_10, x_14, x_13, x_7, x_17);
lean_dec(x_13);
x_19 = l_Lean_Elab_Term_elabTerm(x_18, x_2, x_3, x_4);
return x_19;
}
}
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Term_elabListLit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Term_elabListLit___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
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
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
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
lean_object* l_Lean_Elab_Term_elabExplicitUniv___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabExplicitUniv___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabExplicitUniv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_elabExplicitUniv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_NamedArg_hasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_System_FilePath_dirName___closed__1;
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_2);
x_5 = l_Prod_HasRepr___rarg___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Lean_formatEntry___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Syntax_formatStx___main(x_9);
x_11 = l_Lean_Options_empty;
x_12 = l_Lean_Format_pretty(x_10, x_11);
x_13 = lean_string_append(x_8, x_12);
lean_dec(x_12);
x_14 = l_Option_HasRepr___rarg___closed__3;
x_15 = lean_string_append(x_13, x_14);
return x_15;
}
}
lean_object* l___private_Init_Lean_Elab_Term_9__resolveLocalNameAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_1);
x_6 = lean_local_ctx_find_from_user_name(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_3);
x_2 = x_4;
x_3 = x_7;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = l_Lean_LocalDecl_toExpr(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = l_Lean_LocalDecl_toExpr(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
return x_17;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_9__resolveLocalNameAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Term_9__resolveLocalNameAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Term_10__resolveLocalName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l___private_Init_Lean_Elab_Term_9__resolveLocalNameAux___main(x_6, x_1, x_7);
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
x_12 = l___private_Init_Lean_Elab_Term_9__resolveLocalNameAux___main(x_9, x_1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_10__resolveLocalName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Term_10__resolveLocalName(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Term_11__mkFreshLevelMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_Elab_Term_mkFreshLevelMVar___rarg(x_5);
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
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_11__mkFreshLevelMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
lean_inc(x_1);
x_5 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Term_11__mkFreshLevelMVars___spec__1(x_1, x_1, x_4, x_2, x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Term_11__mkFreshLevelMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Term_11__mkFreshLevelMVars___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Term_11__mkFreshLevelMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Term_11__mkFreshLevelMVars(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_Monad;
x_2 = l_String_Inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_Inhabited;
x_2 = l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_Monad;
x_2 = l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__2;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_11 = lean_environment_find(x_2, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_1);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_12 = l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__3;
x_13 = l_monadInhabited___rarg(x_3, x_12);
x_14 = l_unreachable_x21___rarg(x_13);
x_15 = lean_apply_2(x_14, x_6, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_3);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l_Lean_ConstantInfo_lparams(x_16);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_List_lengthAux___main___rarg(x_17, x_18);
lean_dec(x_17);
x_20 = l_List_lengthAux___main___rarg(x_4, x_18);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_nat_sub(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
x_23 = l___private_Init_Lean_Elab_Term_11__mkFreshLevelMVars(x_22, x_6, x_7);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_List_append___rarg(x_4, x_25);
x_27 = l_Lean_mkConst(x_9, x_26);
lean_ctor_set(x_1, 0, x_27);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_5);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = l_List_append___rarg(x_4, x_29);
x_32 = l_Lean_mkConst(x_9, x_31);
lean_ctor_set(x_1, 0, x_32);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_5);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_20);
lean_dec(x_19);
lean_free_object(x_1);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_7);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_1, 0);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_1);
lean_inc(x_36);
x_38 = lean_environment_find(x_2, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_5);
lean_dec(x_4);
x_39 = l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__3;
x_40 = l_monadInhabited___rarg(x_3, x_39);
x_41 = l_unreachable_x21___rarg(x_40);
x_42 = lean_apply_2(x_41, x_6, x_7);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_3);
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
lean_dec(x_38);
x_44 = l_Lean_ConstantInfo_lparams(x_43);
lean_dec(x_43);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_List_lengthAux___main___rarg(x_44, x_45);
lean_dec(x_44);
x_47 = l_List_lengthAux___main___rarg(x_4, x_45);
x_48 = lean_nat_dec_lt(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_nat_sub(x_46, x_47);
lean_dec(x_47);
lean_dec(x_46);
x_50 = l___private_Init_Lean_Elab_Term_11__mkFreshLevelMVars(x_49, x_6, x_7);
lean_dec(x_6);
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
x_54 = l_List_append___rarg(x_4, x_51);
x_55 = l_Lean_mkConst(x_36, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_37);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_5);
if (lean_is_scalar(x_53)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_53;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_52);
return x_58;
}
else
{
lean_object* x_59; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_4);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_5);
lean_ctor_set(x_59, 1, x_7);
return x_59;
}
}
}
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1(x_1, x_2, x_3, x_5, x_4, x_6, x_7);
return x_8;
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_4(x_9, lean_box(0), x_4, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_3);
x_14 = lean_alloc_closure((void*)(l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1), 7, 5);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_1);
lean_closure_set(x_14, 4, x_4);
x_15 = lean_alloc_closure((void*)(l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__2), 7, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_12);
x_16 = lean_apply_6(x_13, lean_box(0), lean_box(0), x_14, x_15, x_6, x_7);
return x_16;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_12__mkConsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Elab_Term_getEnv___rarg(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l___private_Init_Lean_Meta_Check_2__checkLambdaLet___lambda__2___closed__1;
x_10 = l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1(x_2, x_9, x_6, x_8, x_1, x_3, x_7);
return x_10;
}
}
lean_object* l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_resolveName___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = 2;
x_8 = l_Lean_Elab_log___at_Lean_Elab_Term_ensureType___spec__2(x_1, x_7, x_6, x_3, x_4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = lean_box(5);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_box(5);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many explicit universe levels");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown identifier '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of explicit universe parameters, '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is a local");
return x_1;
}
}
lean_object* l_Lean_Elab_Term_resolveName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = l___private_Init_Lean_Elab_Term_10__resolveLocalName(x_1, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_List_isEmpty___rarg(x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
lean_inc(x_5);
x_11 = l___private_Init_Lean_Elab_Term_12__mkConsts(x_2, x_3, x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_List_isEmpty___rarg(x_13);
if (x_15 == 0)
{
lean_dec(x_5);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_free_object(x_11);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_resolveName___closed__1;
x_17 = l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_resolveName___spec__1(x_4, x_16, x_5, x_14);
lean_dec(x_5);
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
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = l_List_isEmpty___rarg(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_22);
x_26 = l_Lean_Elab_Term_resolveName___closed__1;
x_27 = l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_resolveName___spec__1(x_4, x_26, x_5, x_23);
lean_dec(x_5);
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
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_2);
x_36 = l_Lean_Elab_Term_getEnv___rarg(x_9);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Elab_Term_getNamespace(x_5, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Elab_Term_getOpenDecls(x_5, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_1);
x_45 = l_Lean_Elab_resolveGlobalName(x_37, x_40, x_43, x_1);
lean_dec(x_40);
lean_dec(x_37);
x_46 = l_List_isEmpty___rarg(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_1);
lean_inc(x_5);
x_47 = l___private_Init_Lean_Elab_Term_12__mkConsts(x_45, x_3, x_5, x_44);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
x_51 = l_List_isEmpty___rarg(x_49);
if (x_51 == 0)
{
lean_dec(x_5);
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_free_object(x_47);
lean_dec(x_49);
x_52 = l_Lean_Elab_Term_resolveName___closed__1;
x_53 = l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_resolveName___spec__1(x_4, x_52, x_5, x_50);
lean_dec(x_5);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
return x_53;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_47, 0);
x_59 = lean_ctor_get(x_47, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_47);
x_60 = l_List_isEmpty___rarg(x_58);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_5);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_58);
x_62 = l_Lean_Elab_Term_resolveName___closed__1;
x_63 = l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_resolveName___spec__1(x_4, x_62, x_5, x_59);
lean_dec(x_5);
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
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_5);
x_68 = !lean_is_exclusive(x_47);
if (x_68 == 0)
{
return x_47;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_47, 0);
x_70 = lean_ctor_get(x_47, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_47);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_45);
lean_dec(x_3);
x_72 = l_System_FilePath_dirName___closed__1;
x_73 = l_Lean_Name_toStringWithSep___main(x_72, x_1);
x_74 = l_Lean_Elab_Term_resolveName___closed__2;
x_75 = lean_string_append(x_74, x_73);
lean_dec(x_73);
x_76 = l_Char_HasRepr___closed__1;
x_77 = lean_string_append(x_75, x_76);
x_78 = l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_resolveName___spec__1(x_4, x_77, x_5, x_44);
lean_dec(x_5);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
return x_78;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_78);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
lean_object* x_83; uint8_t x_84; 
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_ctor_get(x_8, 0);
lean_inc(x_83);
lean_dec(x_8);
x_84 = !lean_is_exclusive(x_7);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_7, 1);
x_86 = lean_ctor_get(x_7, 0);
lean_dec(x_86);
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
x_88 = l_List_isEmpty___rarg(x_3);
lean_dec(x_3);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_free_object(x_7);
lean_dec(x_83);
x_89 = l_Lean_Expr_fvarId_x21(x_87);
lean_dec(x_87);
x_90 = l_System_FilePath_dirName___closed__1;
x_91 = l_Lean_Name_toStringWithSep___main(x_90, x_89);
x_92 = l_Lean_Elab_Term_resolveName___closed__3;
x_93 = lean_string_append(x_92, x_91);
lean_dec(x_91);
x_94 = l_Lean_Elab_Term_resolveName___closed__4;
x_95 = lean_string_append(x_93, x_94);
x_96 = l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_resolveName___spec__1(x_4, x_95, x_5, x_85);
lean_dec(x_5);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
return x_96;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_96);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_87);
lean_dec(x_5);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_83);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_7, 0, x_102);
return x_7;
}
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_7, 1);
lean_inc(x_103);
lean_dec(x_7);
x_104 = lean_ctor_get(x_83, 0);
lean_inc(x_104);
x_105 = l_List_isEmpty___rarg(x_3);
lean_dec(x_3);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_83);
x_106 = l_Lean_Expr_fvarId_x21(x_104);
lean_dec(x_104);
x_107 = l_System_FilePath_dirName___closed__1;
x_108 = l_Lean_Name_toStringWithSep___main(x_107, x_106);
x_109 = l_Lean_Elab_Term_resolveName___closed__3;
x_110 = lean_string_append(x_109, x_108);
lean_dec(x_108);
x_111 = l_Lean_Elab_Term_resolveName___closed__4;
x_112 = lean_string_append(x_110, x_111);
x_113 = l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_resolveName___spec__1(x_4, x_112, x_5, x_103);
lean_dec(x_5);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_104);
lean_dec(x_5);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_83);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_103);
return x_120;
}
}
}
}
}
lean_object* l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_resolveName___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_resolveName___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_resolveName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_resolveName(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_13__elabAppAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TODO");
return x_1;
}
}
lean_object* l___private_Init_Lean_Elab_Term_13__elabAppAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Init_Lean_Elab_Term_13__elabAppAux___closed__1;
x_8 = l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_ensureType___spec__1(x_1, x_7, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Term_13__elabAppAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Elab_Term_13__elabAppAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_Term_14__expandAppAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = l_Lean_Parser_Term_app___elambda__1___closed__2;
x_7 = lean_name_eq(x_4, x_6);
lean_dec(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_10 = l_Lean_stxInh;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get(x_10, x_5, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_array_get(x_10, x_5, x_13);
lean_dec(x_5);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = l_Lean_Parser_Term_namedArgument___elambda__1___rarg___closed__2;
x_18 = lean_name_eq(x_15, x_17);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
x_19 = lean_array_push(x_3, x_14);
x_1 = x_12;
x_3 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_array_get(x_10, x_16, x_13);
x_22 = l_Lean_Syntax_getId(x_21);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(3u);
x_24 = lean_array_get(x_10, x_16, x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_14);
x_26 = lean_array_push(x_2, x_25);
x_1 = x_12;
x_2 = x_26;
goto _start;
}
}
else
{
lean_object* x_28; 
x_28 = lean_array_push(x_3, x_14);
x_1 = x_12;
x_3 = x_28;
goto _start;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_14__expandAppAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Term_14__expandAppAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Term_15__expandApp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = l___private_Init_Lean_Elab_Term_14__expandAppAux___main(x_1, x_2, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l___private_Init_Lean_Elab_Term_15__expandApp(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l___private_Init_Lean_Elab_Term_13__elabAppAux___closed__1;
x_8 = l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_ensureType___spec__1(x_6, x_7, x_3, x_4);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_elabApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabApp(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabApp");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabApp___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_app___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Init_Lean_Elab_Term_13__elabAppAux___closed__1;
x_6 = l_Lean_Elab_logErrorAndThrow___at_Lean_Elab_Term_ensureType___spec__1(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_elabId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabId(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabId");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabId___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_id___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_16__regTraceClasses___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__2;
x_2 = l_Lean_Parser_Term_app___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Term_16__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elab_Term_16__regTraceClasses___closed__1;
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
lean_object* initialize_Init_Lean_Meta(lean_object*);
lean_object* initialize_Init_Lean_Elab_Log(lean_object*);
lean_object* initialize_Init_Lean_Elab_Alias(lean_object*);
lean_object* initialize_Init_Lean_Elab_ResolveName(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Term(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta(lean_io_mk_world());
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
l_Lean_Elab_Term_TermElabM_monadLog___closed__1 = _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog___closed__1);
l_Lean_Elab_Term_TermElabM_monadLog___closed__2 = _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog___closed__2);
l_Lean_Elab_Term_TermElabM_monadLog___closed__3 = _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog___closed__3);
l_Lean_Elab_Term_TermElabM_monadLog___closed__4 = _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog___closed__4);
l_Lean_Elab_Term_TermElabM_monadLog___closed__5 = _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog___closed__5);
l_Lean_Elab_Term_TermElabM_monadLog___closed__6 = _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog___closed__6);
l_Lean_Elab_Term_TermElabM_monadLog___closed__7 = _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog___closed__7);
l_Lean_Elab_Term_TermElabM_monadLog___closed__8 = _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog___closed__8);
l_Lean_Elab_Term_TermElabM_monadLog___closed__9 = _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog___closed__9);
l_Lean_Elab_Term_TermElabM_monadLog = _init_l_Lean_Elab_Term_TermElabM_monadLog();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog);
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
l_Lean_Elab_Term_addBuiltinTermElab___closed__2 = _init_l_Lean_Elab_Term_addBuiltinTermElab___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_addBuiltinTermElab___closed__2);
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
l_Lean_Elab_Term_declareBuiltinTermElab___closed__8 = _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_declareBuiltinTermElab___closed__8);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__1 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__1);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__2 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__2);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__3 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__3);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__4 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__4);
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
l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__6 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__6);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__7 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__7);
res = l_Lean_Elab_Term_registerBuiltinTermElabAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__1();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__1);
l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__2 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__2();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__2);
l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1___closed__1 = _init_l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1___closed__1);
l_Lean_Elab_Term_mkTermElabAttribute___closed__1 = _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkTermElabAttribute___closed__1);
l_Lean_Elab_Term_mkTermElabAttribute___closed__2 = _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkTermElabAttribute___closed__2);
l_Lean_Elab_Term_termElabAttribute___closed__1 = _init_l_Lean_Elab_Term_termElabAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_termElabAttribute___closed__1);
l_Lean_Elab_Term_termElabAttribute___closed__2 = _init_l_Lean_Elab_Term_termElabAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_termElabAttribute___closed__2);
l_Lean_Elab_Term_termElabAttribute___closed__3 = _init_l_Lean_Elab_Term_termElabAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_termElabAttribute___closed__3);
res = l_Lean_Elab_Term_mkTermElabAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_termElabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_termElabAttribute);
lean_dec_ref(res);
l_Lean_Elab_Term_tracer___closed__1 = _init_l_Lean_Elab_Term_tracer___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_tracer___closed__1);
l_Lean_Elab_Term_tracer___closed__2 = _init_l_Lean_Elab_Term_tracer___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_tracer___closed__2);
l_Lean_Elab_Term_tracer___closed__3 = _init_l_Lean_Elab_Term_tracer___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_tracer___closed__3);
l_Lean_Elab_Term_tracer___closed__4 = _init_l_Lean_Elab_Term_tracer___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_tracer___closed__4);
l_Lean_Elab_Term_tracer___closed__5 = _init_l_Lean_Elab_Term_tracer___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_tracer___closed__5);
l_Lean_Elab_Term_tracer = _init_l_Lean_Elab_Term_tracer();
lean_mark_persistent(l_Lean_Elab_Term_tracer);
l_Lean_Elab_Term_withNode___rarg___closed__1 = _init_l_Lean_Elab_Term_withNode___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_withNode___rarg___closed__1);
l_Lean_Elab_Term_withNode___rarg___closed__2 = _init_l_Lean_Elab_Term_withNode___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_withNode___rarg___closed__2);
l_Lean_Elab_Term_elabTerm___closed__1 = _init_l_Lean_Elab_Term_elabTerm___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabTerm___closed__1);
l_Lean_Elab_Term_elabTerm___closed__2 = _init_l_Lean_Elab_Term_elabTerm___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabTerm___closed__2);
l_Lean_Elab_Term_elabTerm___closed__3 = _init_l_Lean_Elab_Term_elabTerm___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabTerm___closed__3);
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
l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___rarg___closed__1 = _init_l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___rarg___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___rarg___closed__1);
l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___rarg___closed__2 = _init_l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___rarg___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_1__mkFreshAnonymousName___rarg___closed__2);
l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___rarg___closed__1 = _init_l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___rarg___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___rarg___closed__1);
l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___rarg___closed__2 = _init_l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___rarg___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_2__mkFreshInstanceName___rarg___closed__2);
l_Lean_Elab_Term_mkHole___closed__1 = _init_l_Lean_Elab_Term_mkHole___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkHole___closed__1);
l_Lean_Elab_Term_mkHole___closed__2 = _init_l_Lean_Elab_Term_mkHole___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkHole___closed__2);
l_Lean_Elab_Term_mkHole___closed__3 = _init_l_Lean_Elab_Term_mkHole___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_mkHole___closed__3);
l_Lean_Elab_Term_mkHole = _init_l_Lean_Elab_Term_mkHole();
lean_mark_persistent(l_Lean_Elab_Term_mkHole);
l___private_Init_Lean_Elab_Term_6__matchBinder___closed__1 = _init_l___private_Init_Lean_Elab_Term_6__matchBinder___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_6__matchBinder___closed__1);
l___private_Init_Lean_Elab_Term_6__matchBinder___closed__2 = _init_l___private_Init_Lean_Elab_Term_6__matchBinder___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_6__matchBinder___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabForall(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Lean_Elab_Term_elabArrow___closed__1 = _init_l_Lean_Elab_Term_elabArrow___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___closed__1);
l_Lean_Elab_Term_elabArrow___closed__2 = _init_l_Lean_Elab_Term_elabArrow___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___closed__2);
l_Lean_Elab_Term_elabArrow___closed__3 = _init_l_Lean_Elab_Term_elabArrow___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___closed__3);
l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabArrow(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabParen___closed__1 = _init_l_Lean_Elab_Term_elabParen___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__1);
l_Lean_Elab_Term_elabParen___closed__2 = _init_l_Lean_Elab_Term_elabParen___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__2);
l_Lean_Elab_Term_elabParen___closed__3 = _init_l_Lean_Elab_Term_elabParen___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__3);
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
l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__1 = _init_l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__1);
l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__2 = _init_l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__2);
l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__3 = _init_l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__3();
lean_mark_persistent(l_List_foldlM___main___at___private_Init_Lean_Elab_Term_12__mkConsts___spec__1___lambda__1___closed__3);
l_Lean_Elab_Term_resolveName___closed__1 = _init_l_Lean_Elab_Term_resolveName___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__1);
l_Lean_Elab_Term_resolveName___closed__2 = _init_l_Lean_Elab_Term_resolveName___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__2);
l_Lean_Elab_Term_resolveName___closed__3 = _init_l_Lean_Elab_Term_resolveName___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__3);
l_Lean_Elab_Term_resolveName___closed__4 = _init_l_Lean_Elab_Term_resolveName___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__4);
l___private_Init_Lean_Elab_Term_13__elabAppAux___closed__1 = _init_l___private_Init_Lean_Elab_Term_13__elabAppAux___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_13__elabAppAux___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabApp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabId(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Elab_Term_16__regTraceClasses___closed__1 = _init_l___private_Init_Lean_Elab_Term_16__regTraceClasses___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_16__regTraceClasses___closed__1);
res = l___private_Init_Lean_Elab_Term_16__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
