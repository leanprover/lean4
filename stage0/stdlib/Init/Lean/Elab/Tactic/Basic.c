// Lean compiler output
// Module: Init.Lean.Elab.Tactic.Basic
// Imports: Init.Lean.Util.CollectMVars Init.Lean.Meta.Tactic.Assumption Init.Lean.Meta.Tactic.Intro Init.Lean.Elab.Util Init.Lean.Elab.Term
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalTraceState___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withIncRecDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro(lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog;
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getLocalInsts___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentHashMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___closed__3;
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__8;
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadQuotation;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabTermAux___main___closed__6;
lean_object* l_List_map___main___at_Lean_Elab_goalsToMessageData___spec__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSkip___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMCtx___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_monadQuotation___closed__4;
extern lean_object* l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Term_assignExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalCase___closed__1;
lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getEnv(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSkip(lean_object*, lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Lean_Elab_Tactic_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_trace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focus(lean_object*);
lean_object* l_Lean_Elab_Tactic_getLCtx___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadQuotation___closed__2;
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCase___closed__1;
lean_object* l_Lean_Elab_Tactic_done(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse___closed__3;
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5___boxed(lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen(lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalCase(lean_object*);
lean_object* l_Lean_Elab_Tactic_monadQuotation___closed__1;
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_restore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ElabFnTable_insert___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_goalsToMessageData___closed__1;
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_3__getIntrosSize___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__1;
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCase___closed__3;
lean_object* l_Lean_Meta_assumption___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_SMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__1(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMCtx___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_getGoals___boxed(lean_object*);
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__2;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Elab_Term_logTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_withFreshMacroScope(lean_object*);
lean_object* l_Lean_MetavarContext_renameMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__3;
lean_object* l_AssocList_find___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock___closed__2;
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__5(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_getLocalInsts(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__10;
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__1;
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__4;
lean_object* l_Lean_Elab_Tactic_restore___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock___closed__1;
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l_Lean_Elab_Term_trace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Tactic_evalTraceState___spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__2;
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_collectMVars___closed__1;
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__1;
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_3__getIntrosSize___main___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___closed__2;
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_3__getIntrosSize(lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__3;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l_Lean_Meta_intro(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalCase___closed__2;
lean_object* l_Lean_Syntax_getTailWithInfo___main(lean_object*);
lean_object* l_List_findM_x3f___main___at_Lean_Elab_Tactic_evalCase___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_3__getIntrosSize___main(lean_object*);
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Tactic_evalTraceState___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic___closed__7;
extern lean_object* l_Lean_Meta_dbgTrace___rarg___closed__1;
lean_object* l_List_findM_x3f___main___at_Lean_Elab_Tactic_evalCase___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___closed__2;
extern lean_object* l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_object* l_Lean_Elab_Tactic_evalCase(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic___closed__5;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute___closed__4;
lean_object* l_Lean_Elab_Term_addContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalParen(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
extern lean_object* l_Lean_Meta_Exception_toMessageData___closed__48;
extern lean_object* l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_focus___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__5;
lean_object* l_Lean_Elab_Term_isExprMVarAssigned___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_dbgTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_seq___elambda__1___closed__3;
lean_object* l_Lean_Elab_Tactic_addContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSeq___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_EStateM_Backtrackable;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState(lean_object*);
lean_object* l_PersistentHashMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__4___boxed(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_4__regTraceClasses___closed__1;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock___closed__3;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftTermElabM(lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getGoals___rarg(lean_object*);
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse___closed__2;
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__2;
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__2;
extern lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse(lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___closed__1;
extern lean_object* l_Lean_Elab_Term_State_inhabited___closed__2;
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Tactic_evalTraceState___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__1;
lean_object* l_Lean_Elab_Tactic_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_resetSynthInstanceCache(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__7;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Syntax_prettyPrint(lean_object*);
lean_object* l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_builtinTacticTable;
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__4;
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_State_inhabited___closed__1;
lean_object* l_Lean_collectMVars(lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__2;
lean_object* l_Lean_Elab_Tactic_evalParen___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__3;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalCase___closed__3;
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__7;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__8;
extern lean_object* l_Lean_Parser_Tactic_skip___elambda__1___closed__2;
extern lean_object* l_Lean_Options_empty;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq(lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__4;
lean_object* l_Lean_Elab_Tactic_getMainModule___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_withLCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTraceState(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Elab_Tactic_monadLog___spec__1(lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly(lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__1;
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__3;
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip___closed__1;
extern lean_object* l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
lean_object* l_Lean_Elab_Tactic_monadLog___closed__1;
lean_object* l_Lean_Elab_Term_ensureHasType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_save___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__5;
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__3;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__3;
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic___closed__6;
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_4__regTraceClasses(lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__4;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__2;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l_Lean_Elab_Tactic_liftMetaM(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalNestedTacticBlock(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_MessageData_joinSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_State_inhabited;
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5(lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__1;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros(lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_evalOrelse(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_case___elambda__1___closed__2;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_setParam___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalAssumption___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse___closed__1;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption(lean_object*);
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__3;
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_declareBuiltinMacro___closed__4;
lean_object* l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_traceAtCmdPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Parser_Parser_15__throwParserCategoryAlreadyDefined___rarg___closed__2;
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_throwUnsupportedSyntax(lean_object*);
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__1;
lean_object* l_Lean_Elab_Tactic_withLCtx(lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTraceState___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__1;
lean_object* l_Lean_Elab_goalsToMessageData(lean_object*);
lean_object* l_Lean_Elab_Term_liftMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_isAnonymousMVar(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__4;
lean_object* l_Lean_Elab_Tactic_evalAssumption___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic___closed__4;
extern lean_object* l_Lean_Elab_Exception_inhabited;
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__3;
lean_object* l_Lean_Elab_Tactic_liftTermElabM___rarg___closed__1;
lean_object* l_Lean_Elab_Tactic_evalAssumption___closed__1;
lean_object* l_Lean_Elab_Tactic_isExprMVarAssigned(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_modifyMCtx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalParen(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Elab_Tactic_liftMetaTactic(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___closed__1;
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__3;
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2;
lean_object* l_Lean_Elab_Tactic_evalNestedTacticBlockCurly(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_nameToExprAux___main(lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip___closed__3;
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic___closed__1;
lean_object* l_Lean_Elab_Term_throwError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__6;
lean_object* l_Lean_Elab_Tactic_evalSeq(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__3;
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1;
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCache(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalAssumption(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_save(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCase___closed__2;
lean_object* l_Lean_Elab_Tactic_monadLog___closed__2;
lean_object* l_Lean_Elab_Tactic_setGoals(lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentHashMap_containsAtAux___main___at_Lean_Parser_isValidSyntaxNodeKind___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_addBuiltinTactic(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_modifyMCtx(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
lean_object* l_Lean_Elab_Tactic_getOptions___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic___closed__2;
lean_object* l_Lean_Elab_Tactic_withMVarContext___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isSuffixOf___main(lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalParen___closed__3;
lean_object* l_Lean_Elab_Tactic_logTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1;
lean_object* l_Lean_Elab_Tactic_throwError(lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkBuiltinTacticTable(lean_object*);
lean_object* l_Lean_Elab_Tactic_addBuiltinTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__1;
lean_object* l_Lean_Elab_Tactic_addBuiltinTactic___closed__1;
lean_object* l_Lean_Elab_Tactic_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalParen___closed__1;
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalIntros___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__2;
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getOptions(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__5;
lean_object* l_Lean_Elab_Tactic_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTraceState___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getEnv___rarg(lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__3;
lean_object* l_Lean_Meta_intro1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__2;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Parser_Parser_26__BuiltinParserAttribute_add___closed__2;
lean_object* l_Lean_Elab_Tactic_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTraceState___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__3;
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock(lean_object*);
lean_object* l_HashMapImp_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__3;
lean_object* l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__3(lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__1;
lean_object* l_Lean_Elab_Tactic_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntros(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___closed__3;
lean_object* l_Lean_Elab_Tactic_getMainGoal___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__1;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip___closed__2;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__2;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__2;
lean_object* l_Lean_Elab_Tactic_monadLog___closed__11;
lean_object* l_Lean_SMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalTraceState___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_collectMVars(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalInstance_beq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMVarContext(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMacroExpansion(lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
uint8_t l_HashMapImp_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_dbgTrace(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__1;
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_EStateM_Backtrackable___closed__3;
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_seq___elambda__1___closed__1;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__2;
lean_object* l_Lean_Elab_Tactic_getMainModule(lean_object*);
extern lean_object* l_HashMap_Inhabited___closed__1;
lean_object* l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg___closed__1;
lean_object* l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainModule___boxed(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_traceState___elambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_monadQuotation___closed__3;
lean_object* l_IO_ofExcept___at___private_Init_Lean_Elab_Util_6__ElabAttribute_add___spec__1(lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getGoals(lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__3;
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__2;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
lean_object* l_Lean_Elab_Tactic_traceAtCmdPos(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_initAttr;
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getLCtx(lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l_Lean_Elab_Tactic_expandTacticMacro(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getEnv___boxed(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalParen___closed__2;
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Tactic_evalTraceState___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__1;
lean_object* l_AssocList_contains___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__4;
lean_object* l_Lean_Elab_Tactic_getMCtx(lean_object*);
lean_object* l_Lean_Elab_Tactic_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__2(lean_object*);
extern lean_object* l_Lean_Elab_declareBuiltinMacro___closed__3;
lean_object* l_Lean_Elab_Tactic_monadLog___closed__9;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSkip___rarg(lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__3;
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
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_5 = l_Lean_Syntax_getTailWithInfo___main(x_1);
x_6 = l_Lean_Elab_goalsToMessageData(x_2);
x_7 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__4;
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_throwError___rarg(x_1, x_8, x_3, x_4);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Lean_Elab_Term_throwError___rarg(x_10, x_8, x_3, x_4);
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
lean_object* l_Lean_Elab_Tactic_liftMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_liftMetaM___rarg___boxed), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 0);
return x_2;
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
lean_object* l_Lean_Elab_Tactic_instantiateMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_instantiateMVars___boxed), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_5, x_3, x_4);
return x_6;
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
lean_object* l_Lean_Elab_Tactic_ensureHasType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ensureHasType___boxed), 5, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
x_7 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Tactic_reportUnsolvedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportUnsolvedGoals), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_5, x_3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Tactic_collectMVars___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_HashMap_Inhabited___closed__1;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_collectMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_instantiateMVars(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_Elab_Tactic_collectMVars___closed__1;
x_9 = l_Lean_collectMVars(x_8, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Array_toList___rarg(x_10);
lean_dec(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = l_Lean_Elab_Tactic_collectMVars___closed__1;
x_15 = l_Lean_collectMVars(x_14, x_12);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Array_toList___rarg(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
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
x_5 = lean_ctor_get(x_4, 3);
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
x_8 = l_PersistentArray_push___rarg(x_7, x_1);
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
x_17 = l_PersistentArray_push___rarg(x_13, x_1);
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
x_30 = l_PersistentArray_push___rarg(x_25, x_1);
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
lean_object* l_Lean_Elab_Tactic_throwError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_getPos(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwError___rarg___boxed), 4, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_2);
x_8 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_7, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwError___rarg___boxed), 4, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_9, x_3, x_4);
return x_10;
}
}
}
lean_object* l_Lean_Elab_Tactic_throwError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_throwError___rarg), 4, 0);
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
lean_object* l_Lean_Elab_Tactic_withIncRecDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_3, 0);
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
lean_dec(x_1);
x_5 = x_4;
goto block_74;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_3);
x_81 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_80, x_3, x_4);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_5 = x_82;
goto block_74;
}
else
{
uint8_t x_83; 
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_13, x_14);
lean_dec(x_13);
lean_ctor_set(x_7, 3, x_15);
x_16 = lean_apply_2(x_2, x_3, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
x_19 = lean_ctor_get(x_7, 2);
x_20 = lean_ctor_get(x_7, 3);
x_21 = lean_ctor_get(x_7, 4);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_20, x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 4, x_21);
lean_ctor_set(x_6, 0, x_24);
x_25 = lean_apply_2(x_2, x_3, x_5);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_26 = lean_ctor_get(x_6, 1);
x_27 = lean_ctor_get(x_6, 2);
x_28 = lean_ctor_get(x_6, 3);
x_29 = lean_ctor_get(x_6, 4);
x_30 = lean_ctor_get(x_6, 5);
x_31 = lean_ctor_get(x_6, 6);
x_32 = lean_ctor_get(x_6, 7);
x_33 = lean_ctor_get(x_6, 8);
x_34 = lean_ctor_get(x_6, 9);
x_35 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_36 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_6);
x_37 = lean_ctor_get(x_7, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_7, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_7, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_7, 4);
lean_inc(x_41);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 x_42 = x_7;
} else {
 lean_dec_ref(x_7);
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
x_46 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_26);
lean_ctor_set(x_46, 2, x_27);
lean_ctor_set(x_46, 3, x_28);
lean_ctor_set(x_46, 4, x_29);
lean_ctor_set(x_46, 5, x_30);
lean_ctor_set(x_46, 6, x_31);
lean_ctor_set(x_46, 7, x_32);
lean_ctor_set(x_46, 8, x_33);
lean_ctor_set(x_46, 9, x_34);
lean_ctor_set_uint8(x_46, sizeof(void*)*10, x_35);
lean_ctor_set_uint8(x_46, sizeof(void*)*10 + 1, x_36);
lean_ctor_set(x_3, 0, x_46);
x_47 = lean_apply_2(x_2, x_3, x_5);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_48 = lean_ctor_get(x_3, 1);
x_49 = lean_ctor_get(x_3, 2);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_3);
x_50 = lean_ctor_get(x_6, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_6, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_6, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_6, 4);
lean_inc(x_53);
x_54 = lean_ctor_get(x_6, 5);
lean_inc(x_54);
x_55 = lean_ctor_get(x_6, 6);
lean_inc(x_55);
x_56 = lean_ctor_get(x_6, 7);
lean_inc(x_56);
x_57 = lean_ctor_get(x_6, 8);
lean_inc(x_57);
x_58 = lean_ctor_get(x_6, 9);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_60 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
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
 x_61 = x_6;
} else {
 lean_dec_ref(x_6);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_7, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_7, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_7, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_7, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_7, 4);
lean_inc(x_66);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 x_67 = x_7;
} else {
 lean_dec_ref(x_7);
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
 x_71 = lean_alloc_ctor(0, 10, 2);
} else {
 x_71 = x_61;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_50);
lean_ctor_set(x_71, 2, x_51);
lean_ctor_set(x_71, 3, x_52);
lean_ctor_set(x_71, 4, x_53);
lean_ctor_set(x_71, 5, x_54);
lean_ctor_set(x_71, 6, x_55);
lean_ctor_set(x_71, 7, x_56);
lean_ctor_set(x_71, 8, x_57);
lean_ctor_set(x_71, 9, x_58);
lean_ctor_set_uint8(x_71, sizeof(void*)*10, x_59);
lean_ctor_set_uint8(x_71, sizeof(void*)*10 + 1, x_60);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_48);
lean_ctor_set(x_72, 2, x_49);
x_73 = lean_apply_2(x_2, x_72, x_5);
return x_73;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_withIncRecDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withIncRecDepth___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 9);
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
x_13 = lean_ctor_get(x_11, 9);
lean_dec(x_13);
lean_ctor_set(x_11, 9, x_7);
x_14 = lean_apply_2(x_1, x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
x_20 = lean_ctor_get(x_11, 5);
x_21 = lean_ctor_get(x_11, 6);
x_22 = lean_ctor_get(x_11, 7);
x_23 = lean_ctor_get(x_11, 8);
x_24 = lean_ctor_get_uint8(x_11, sizeof(void*)*10);
x_25 = lean_ctor_get_uint8(x_11, sizeof(void*)*10 + 1);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_26 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_17);
lean_ctor_set(x_26, 3, x_18);
lean_ctor_set(x_26, 4, x_19);
lean_ctor_set(x_26, 5, x_20);
lean_ctor_set(x_26, 6, x_21);
lean_ctor_set(x_26, 7, x_22);
lean_ctor_set(x_26, 8, x_23);
lean_ctor_set(x_26, 9, x_7);
lean_ctor_set_uint8(x_26, sizeof(void*)*10, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*10 + 1, x_25);
lean_ctor_set(x_2, 0, x_26);
x_27 = lean_apply_2(x_1, x_2, x_3);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_2);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_28, 5);
lean_inc(x_36);
x_37 = lean_ctor_get(x_28, 6);
lean_inc(x_37);
x_38 = lean_ctor_get(x_28, 7);
lean_inc(x_38);
x_39 = lean_ctor_get(x_28, 8);
lean_inc(x_39);
x_40 = lean_ctor_get_uint8(x_28, sizeof(void*)*10);
x_41 = lean_ctor_get_uint8(x_28, sizeof(void*)*10 + 1);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 lean_ctor_release(x_28, 4);
 lean_ctor_release(x_28, 5);
 lean_ctor_release(x_28, 6);
 lean_ctor_release(x_28, 7);
 lean_ctor_release(x_28, 8);
 lean_ctor_release(x_28, 9);
 x_42 = x_28;
} else {
 lean_dec_ref(x_28);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 10, 2);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_31);
lean_ctor_set(x_43, 1, x_32);
lean_ctor_set(x_43, 2, x_33);
lean_ctor_set(x_43, 3, x_34);
lean_ctor_set(x_43, 4, x_35);
lean_ctor_set(x_43, 5, x_36);
lean_ctor_set(x_43, 6, x_37);
lean_ctor_set(x_43, 7, x_38);
lean_ctor_set(x_43, 8, x_39);
lean_ctor_set(x_43, 9, x_7);
lean_ctor_set_uint8(x_43, sizeof(void*)*10, x_40);
lean_ctor_set_uint8(x_43, sizeof(void*)*10 + 1, x_41);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_29);
lean_ctor_set(x_44, 2, x_30);
x_45 = lean_apply_2(x_1, x_44, x_3);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_46 = lean_ctor_get(x_5, 0);
x_47 = lean_ctor_get(x_5, 1);
x_48 = lean_ctor_get(x_5, 2);
x_49 = lean_ctor_get(x_5, 3);
x_50 = lean_ctor_get(x_5, 4);
x_51 = lean_ctor_get(x_5, 5);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_5);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_51, x_52);
x_54 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_54, 0, x_46);
lean_ctor_set(x_54, 1, x_47);
lean_ctor_set(x_54, 2, x_48);
lean_ctor_set(x_54, 3, x_49);
lean_ctor_set(x_54, 4, x_50);
lean_ctor_set(x_54, 5, x_53);
lean_ctor_set(x_3, 0, x_54);
x_55 = lean_ctor_get(x_2, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 2);
lean_inc(x_57);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_58 = x_2;
} else {
 lean_dec_ref(x_2);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_55, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_55, 5);
lean_inc(x_64);
x_65 = lean_ctor_get(x_55, 6);
lean_inc(x_65);
x_66 = lean_ctor_get(x_55, 7);
lean_inc(x_66);
x_67 = lean_ctor_get(x_55, 8);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_55, sizeof(void*)*10);
x_69 = lean_ctor_get_uint8(x_55, sizeof(void*)*10 + 1);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 lean_ctor_release(x_55, 4);
 lean_ctor_release(x_55, 5);
 lean_ctor_release(x_55, 6);
 lean_ctor_release(x_55, 7);
 lean_ctor_release(x_55, 8);
 lean_ctor_release(x_55, 9);
 x_70 = x_55;
} else {
 lean_dec_ref(x_55);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 10, 2);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_59);
lean_ctor_set(x_71, 1, x_60);
lean_ctor_set(x_71, 2, x_61);
lean_ctor_set(x_71, 3, x_62);
lean_ctor_set(x_71, 4, x_63);
lean_ctor_set(x_71, 5, x_64);
lean_ctor_set(x_71, 6, x_65);
lean_ctor_set(x_71, 7, x_66);
lean_ctor_set(x_71, 8, x_67);
lean_ctor_set(x_71, 9, x_51);
lean_ctor_set_uint8(x_71, sizeof(void*)*10, x_68);
lean_ctor_set_uint8(x_71, sizeof(void*)*10 + 1, x_69);
if (lean_is_scalar(x_58)) {
 x_72 = lean_alloc_ctor(0, 3, 0);
} else {
 x_72 = x_58;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_56);
lean_ctor_set(x_72, 2, x_57);
x_73 = lean_apply_2(x_1, x_72, x_3);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_74 = lean_ctor_get(x_3, 0);
x_75 = lean_ctor_get(x_3, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_3);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_74, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_74, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_74, 5);
lean_inc(x_81);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 lean_ctor_release(x_74, 4);
 lean_ctor_release(x_74, 5);
 x_82 = x_74;
} else {
 lean_dec_ref(x_74);
 x_82 = lean_box(0);
}
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_nat_add(x_81, x_83);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(0, 6, 0);
} else {
 x_85 = x_82;
}
lean_ctor_set(x_85, 0, x_76);
lean_ctor_set(x_85, 1, x_77);
lean_ctor_set(x_85, 2, x_78);
lean_ctor_set(x_85, 3, x_79);
lean_ctor_set(x_85, 4, x_80);
lean_ctor_set(x_85, 5, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_75);
x_87 = lean_ctor_get(x_2, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_2, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_2, 2);
lean_inc(x_89);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_90 = x_2;
} else {
 lean_dec_ref(x_2);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_87, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_87, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_87, 4);
lean_inc(x_95);
x_96 = lean_ctor_get(x_87, 5);
lean_inc(x_96);
x_97 = lean_ctor_get(x_87, 6);
lean_inc(x_97);
x_98 = lean_ctor_get(x_87, 7);
lean_inc(x_98);
x_99 = lean_ctor_get(x_87, 8);
lean_inc(x_99);
x_100 = lean_ctor_get_uint8(x_87, sizeof(void*)*10);
x_101 = lean_ctor_get_uint8(x_87, sizeof(void*)*10 + 1);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 lean_ctor_release(x_87, 3);
 lean_ctor_release(x_87, 4);
 lean_ctor_release(x_87, 5);
 lean_ctor_release(x_87, 6);
 lean_ctor_release(x_87, 7);
 lean_ctor_release(x_87, 8);
 lean_ctor_release(x_87, 9);
 x_102 = x_87;
} else {
 lean_dec_ref(x_87);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 10, 2);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_91);
lean_ctor_set(x_103, 1, x_92);
lean_ctor_set(x_103, 2, x_93);
lean_ctor_set(x_103, 3, x_94);
lean_ctor_set(x_103, 4, x_95);
lean_ctor_set(x_103, 5, x_96);
lean_ctor_set(x_103, 6, x_97);
lean_ctor_set(x_103, 7, x_98);
lean_ctor_set(x_103, 8, x_99);
lean_ctor_set(x_103, 9, x_81);
lean_ctor_set_uint8(x_103, sizeof(void*)*10, x_100);
lean_ctor_set_uint8(x_103, sizeof(void*)*10 + 1, x_101);
if (lean_is_scalar(x_90)) {
 x_104 = lean_alloc_ctor(0, 3, 0);
} else {
 x_104 = x_90;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_88);
lean_ctor_set(x_104, 2, x_89);
x_105 = lean_apply_2(x_1, x_104, x_86);
return x_105;
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
lean_object* l_mkHashMap___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_PersistentHashMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__1;
x_3 = l_PersistentHashMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__2;
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_mkBuiltinTacticTable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1;
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
uint8_t l_AssocList_contains___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__3(lean_object* x_1, lean_object* x_2) {
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
uint8_t l_HashMapImp_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_contains___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__3(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__5(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
uint8_t l_PersistentHashMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__5(x_3, x_4, x_2);
return x_5;
}
}
uint8_t l_Lean_SMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_HashMapImp_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__2(x_4, x_2);
lean_dec(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_PersistentHashMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__4(x_5, x_2);
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
x_10 = l_HashMapImp_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__2(x_9, x_2);
lean_dec(x_9);
return x_10;
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_addBuiltinTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid builtin tactic elaborator, elaborator for '");
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_addBuiltinTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_Tactic_builtinTacticTable;
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
x_10 = l_Lean_SMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__1(x_8, x_1);
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
x_16 = l_Lean_Elab_ElabFnTable_insert___rarg(x_12, x_1, x_3);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_3);
x_26 = l_System_FilePath_dirName___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_1);
x_28 = l_Lean_Elab_Tactic_addBuiltinTactic___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l___private_Init_Lean_Parser_Parser_15__throwParserCategoryAlreadyDefined___rarg___closed__2;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_32);
return x_6;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_6, 0);
x_34 = lean_ctor_get(x_6, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_6);
x_35 = l_Lean_SMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__1(x_33, x_1);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_io_ref_get(x_5, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_io_ref_reset(x_5, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Elab_ElabFnTable_insert___rarg(x_37, x_1, x_3);
x_42 = lean_io_ref_set(x_5, x_41, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_1);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_45 = x_39;
} else {
 lean_dec_ref(x_39);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_3);
lean_dec(x_1);
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_49 = x_36;
} else {
 lean_dec_ref(x_36);
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_3);
x_51 = l_System_FilePath_dirName___closed__1;
x_52 = l_Lean_Name_toStringWithSep___main(x_51, x_1);
x_53 = l_Lean_Elab_Tactic_addBuiltinTactic___closed__1;
x_54 = lean_string_append(x_53, x_52);
lean_dec(x_52);
x_55 = l___private_Init_Lean_Parser_Parser_15__throwParserCategoryAlreadyDefined___rarg___closed__2;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_34);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_3);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_6);
if (x_59 == 0)
{
return x_6;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_6, 0);
x_61 = lean_ctor_get(x_6, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_6);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_HashMapImp_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__5(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_PersistentHashMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentHashMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__4(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_SMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_SMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_addBuiltinTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_addBuiltinTactic(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_regBuiltinTactic");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_declareBuiltinMacro___closed__4;
x_2 = l_Lean_Parser_Tactic_seq___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addBuiltinTactic");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__5;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to emit registration code for builtin tactic elaborator '");
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_5 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__2;
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
x_16 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__6;
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
x_26 = l_System_FilePath_dirName___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_3);
x_28 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__7;
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
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid attribute 'builtinTactic', must be persistent");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected tactic elaborator type at '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' `Tactic` expected");
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
if (x_4 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__2;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
lean_inc(x_1);
x_9 = l_Lean_Elab_syntaxNodeKindOfAttrParam(x_1, x_8, x_3);
x_10 = l_IO_ofExcept___at___private_Init_Lean_Elab_Util_6__ElabAttribute_add___spec__1(x_9, x_5);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_24; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_1);
x_24 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_25 = l___private_Init_Lean_Parser_Parser_26__BuiltinParserAttribute_add___closed__2;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Lean_ConstantInfo_type(x_27);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 4)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
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
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = l_Lean_mkAppStx___closed__1;
x_39 = lean_string_dec_eq(x_37, x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_11);
lean_dec(x_1);
x_40 = lean_box(0);
x_14 = x_40;
goto block_23;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_Elab_declareBuiltinMacro___closed__3;
x_42 = lean_string_dec_eq(x_36, x_41);
lean_dec(x_36);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_11);
lean_dec(x_1);
x_43 = lean_box(0);
x_14 = x_43;
goto block_23;
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = l_Lean_Parser_Tactic_seq___elambda__1___closed__1;
x_45 = lean_string_dec_eq(x_35, x_44);
lean_dec(x_35);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_34);
lean_dec(x_11);
lean_dec(x_1);
x_46 = lean_box(0);
x_14 = x_46;
goto block_23;
}
else
{
uint8_t x_47; 
x_47 = lean_string_dec_eq(x_34, x_44);
lean_dec(x_34);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_11);
lean_dec(x_1);
x_48 = lean_box(0);
x_14 = x_48;
goto block_23;
}
else
{
lean_object* x_49; 
lean_dec(x_13);
x_49 = l_Lean_Elab_Tactic_declareBuiltinTactic(x_1, x_11, x_2, x_12);
return x_49;
}
}
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_1);
x_50 = lean_box(0);
x_14 = x_50;
goto block_23;
}
}
else
{
lean_object* x_51; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_1);
x_51 = lean_box(0);
x_14 = x_51;
goto block_23;
}
}
else
{
lean_object* x_52; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_1);
x_52 = lean_box(0);
x_14 = x_52;
goto block_23;
}
}
else
{
lean_object* x_53; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_1);
x_53 = lean_box(0);
x_14 = x_53;
goto block_23;
}
}
else
{
lean_object* x_54; 
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_1);
x_54 = lean_box(0);
x_14 = x_54;
goto block_23;
}
}
else
{
lean_object* x_55; 
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_1);
x_55 = lean_box(0);
x_14 = x_55;
goto block_23;
}
}
block_23:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
x_15 = l_System_FilePath_dirName___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_2);
x_17 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__3;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__4;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
if (lean_is_scalar(x_13)) {
 x_22 = lean_alloc_ctor(1, 2, 0);
} else {
 x_22 = x_13;
 lean_ctor_set_tag(x_22, 1);
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
}
else
{
uint8_t x_56; 
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_10);
if (x_56 == 0)
{
return x_10;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_10, 0);
x_58 = lean_ctor_get(x_10, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_10);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinTactic");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Builtin tactic elaborator");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__2;
x_2 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__3;
x_3 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__4;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__5;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l_Lean_Parser_Tactic_seq___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
x_4 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__1;
x_5 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__3;
x_6 = l_Lean_Elab_Tactic_builtinTacticTable;
x_7 = l_Lean_Elab_mkElabAttribute___rarg(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1;
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
x_4 = l_Lean_Elab_Term_termElabAttribute___closed__4;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_AttributeImpl_inhabited___closed__2;
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__4;
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_logTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Term_logTrace___boxed), 5, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
x_7 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Tactic_trace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
x_7 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Tactic_traceAtCmdPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_traceAtCmdPos___boxed), 4, 2);
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
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = l___private_Init_Lean_Elab_Term_8__elabTermUsing___main___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Tactic_throwError___rarg(x_2, x_13, x_4, x_5);
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
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_1, x_2, x_3, x_4, x_5);
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
x_9 = lean_ctor_get(x_7, 8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_2);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_7, 8, x_11);
x_12 = lean_apply_2(x_3, x_4, x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_ctor_get(x_7, 2);
x_16 = lean_ctor_get(x_7, 3);
x_17 = lean_ctor_get(x_7, 4);
x_18 = lean_ctor_get(x_7, 5);
x_19 = lean_ctor_get(x_7, 6);
x_20 = lean_ctor_get(x_7, 7);
x_21 = lean_ctor_get(x_7, 8);
x_22 = lean_ctor_get(x_7, 9);
x_23 = lean_ctor_get_uint8(x_7, sizeof(void*)*10);
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*10 + 1);
lean_inc(x_22);
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
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_2);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
x_27 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_14);
lean_ctor_set(x_27, 2, x_15);
lean_ctor_set(x_27, 3, x_16);
lean_ctor_set(x_27, 4, x_17);
lean_ctor_set(x_27, 5, x_18);
lean_ctor_set(x_27, 6, x_19);
lean_ctor_set(x_27, 7, x_20);
lean_ctor_set(x_27, 8, x_26);
lean_ctor_set(x_27, 9, x_22);
lean_ctor_set_uint8(x_27, sizeof(void*)*10, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*10 + 1, x_24);
lean_ctor_set(x_4, 0, x_27);
x_28 = lean_apply_2(x_3, x_4, x_5);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
x_31 = lean_ctor_get(x_4, 2);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_4);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_29, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 4);
lean_inc(x_36);
x_37 = lean_ctor_get(x_29, 5);
lean_inc(x_37);
x_38 = lean_ctor_get(x_29, 6);
lean_inc(x_38);
x_39 = lean_ctor_get(x_29, 7);
lean_inc(x_39);
x_40 = lean_ctor_get(x_29, 8);
lean_inc(x_40);
x_41 = lean_ctor_get(x_29, 9);
lean_inc(x_41);
x_42 = lean_ctor_get_uint8(x_29, sizeof(void*)*10);
x_43 = lean_ctor_get_uint8(x_29, sizeof(void*)*10 + 1);
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
 x_44 = x_29;
} else {
 lean_dec_ref(x_29);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_2);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 10, 2);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_32);
lean_ctor_set(x_47, 1, x_33);
lean_ctor_set(x_47, 2, x_34);
lean_ctor_set(x_47, 3, x_35);
lean_ctor_set(x_47, 4, x_36);
lean_ctor_set(x_47, 5, x_37);
lean_ctor_set(x_47, 6, x_38);
lean_ctor_set(x_47, 7, x_39);
lean_ctor_set(x_47, 8, x_46);
lean_ctor_set(x_47, 9, x_41);
lean_ctor_set_uint8(x_47, sizeof(void*)*10, x_42);
lean_ctor_set_uint8(x_47, sizeof(void*)*10 + 1, x_43);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_30);
lean_ctor_set(x_48, 2, x_31);
x_49 = lean_apply_2(x_3, x_48, x_5);
return x_49;
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
lean_object* _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getEnv___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_throwError), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_throwUnsupportedSyntax), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__1;
x_2 = l_Lean_Elab_Tactic_monadQuotation___closed__1;
x_3 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__2;
x_4 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_Lean_Elab_MonadMacroAdapter___closed__4;
return x_1;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
lean_inc(x_2);
x_6 = l_Lean_Syntax_getKind(x_2);
x_7 = l_System_FilePath_dirName___closed__1;
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_6);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_Meta_Exception_toMessageData___closed__48;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Elab_Term_elabTermAux___main___closed__6;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Elab_Tactic_throwError___rarg(x_2, x_14, x_4, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
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
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_environment_main_module(x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
lean_inc(x_2);
x_43 = lean_apply_2(x_16, x_2, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_inc(x_4);
lean_inc(x_2);
x_48 = l_Lean_Elab_Tactic_throwError___rarg(x_2, x_47, x_4, x_40);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_21 = x_49;
x_22 = x_50;
goto block_34;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
x_54 = l_Lean_Elab_Tactic_restore(x_53, x_20);
lean_dec(x_20);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_48, 1, x_54);
return x_48;
}
else
{
lean_free_object(x_48);
lean_dec(x_52);
x_3 = x_17;
x_5 = x_54;
goto _start;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_48);
x_58 = l_Lean_Elab_Tactic_restore(x_57, x_20);
lean_dec(x_20);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_59; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
else
{
lean_dec(x_56);
x_3 = x_17;
x_5 = x_58;
goto _start;
}
}
}
}
else
{
lean_object* x_61; 
lean_inc(x_4);
x_61 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_4, x_40);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_21 = x_62;
x_22 = x_63;
goto block_34;
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_61, 0);
x_66 = lean_ctor_get(x_61, 1);
x_67 = l_Lean_Elab_Tactic_restore(x_66, x_20);
lean_dec(x_20);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_61, 1, x_67);
return x_61;
}
else
{
lean_free_object(x_61);
lean_dec(x_65);
x_3 = x_17;
x_5 = x_67;
goto _start;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_61, 0);
x_70 = lean_ctor_get(x_61, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_61);
x_71 = l_Lean_Elab_Tactic_restore(x_70, x_20);
lean_dec(x_20);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_72; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
else
{
lean_dec(x_69);
x_3 = x_17;
x_5 = x_71;
goto _start;
}
}
}
}
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_43, 0);
lean_inc(x_74);
lean_dec(x_43);
x_21 = x_74;
x_22 = x_40;
goto block_34;
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
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main(x_1, x_2, x_3, x_4, x_5);
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
x_15 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main(x_1, x_2, x_14, x_3, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main(x_1, x_2, x_16, x_3, x_7);
return x_17;
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6(x_2, x_7);
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
x_6 = l_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5(x_4, x_2);
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
x_9 = l_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5(x_8, x_2);
lean_dec(x_8);
return x_9;
}
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_5 = l_Lean_Syntax_getKind(x_1);
x_6 = l_System_FilePath_dirName___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_5);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_Meta_Exception_toMessageData___closed__48;
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Elab_Term_elabTermAux___main___closed__6;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_13, x_3, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
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
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_environment_main_module(x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_35);
lean_inc(x_1);
x_42 = lean_apply_2(x_15, x_1, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_inc(x_3);
lean_inc(x_1);
x_47 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_46, x_3, x_39);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_20 = x_48;
x_21 = x_49;
goto block_33;
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 0);
x_52 = lean_ctor_get(x_47, 1);
x_53 = l_Lean_Elab_Tactic_restore(x_52, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_47, 1, x_53);
return x_47;
}
else
{
lean_free_object(x_47);
lean_dec(x_51);
x_2 = x_16;
x_4 = x_53;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = l_Lean_Elab_Tactic_restore(x_56, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_58; 
lean_dec(x_3);
lean_dec(x_1);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
else
{
lean_dec(x_55);
x_2 = x_16;
x_4 = x_57;
goto _start;
}
}
}
}
else
{
lean_object* x_60; 
lean_inc(x_3);
x_60 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_3, x_39);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_20 = x_61;
x_21 = x_62;
goto block_33;
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
x_66 = l_Lean_Elab_Tactic_restore(x_65, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_60, 1, x_66);
return x_60;
}
else
{
lean_free_object(x_60);
lean_dec(x_64);
x_2 = x_16;
x_4 = x_66;
goto _start;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_60, 0);
x_69 = lean_ctor_get(x_60, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_60);
x_70 = l_Lean_Elab_Tactic_restore(x_69, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_71; 
lean_dec(x_3);
lean_dec(x_1);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
else
{
lean_dec(x_68);
x_2 = x_16;
x_4 = x_70;
goto _start;
}
}
}
}
}
else
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_42, 0);
lean_inc(x_73);
lean_dec(x_42);
x_20 = x_73;
x_21 = x_39;
goto block_33;
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
lean_object* x_4; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; 
x_385 = lean_ctor_get(x_2, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
lean_dec(x_385);
x_387 = lean_ctor_get(x_386, 3);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 4);
lean_inc(x_388);
lean_dec(x_386);
x_389 = lean_nat_dec_eq(x_387, x_388);
lean_dec(x_388);
lean_dec(x_387);
if (x_389 == 0)
{
x_4 = x_3;
goto block_384;
}
else
{
lean_object* x_390; lean_object* x_391; 
x_390 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_2);
lean_inc(x_1);
x_391 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_390, x_2, x_3);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; 
x_392 = lean_ctor_get(x_391, 1);
lean_inc(x_392);
lean_dec(x_391);
x_4 = x_392;
goto block_384;
}
else
{
uint8_t x_393; 
lean_dec(x_2);
lean_dec(x_1);
x_393 = !lean_is_exclusive(x_391);
if (x_393 == 0)
{
return x_391;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_391, 0);
x_395 = lean_ctor_get(x_391, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_391);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
}
block_384:
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 9);
lean_dec(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_6, 3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_13, x_14);
lean_dec(x_13);
lean_ctor_set(x_6, 3, x_15);
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 5);
x_20 = lean_nat_add(x_19, x_14);
lean_ctor_set(x_17, 5, x_20);
lean_ctor_set(x_5, 9, x_19);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = l_Lean_nullKind;
x_23 = lean_name_eq(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_24, 0, x_1);
x_25 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__3;
lean_inc(x_1);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_1);
lean_closure_set(x_26, 2, x_24);
lean_inc(x_2);
x_27 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_26, x_2, x_4);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_PersistentEnvExtension_getState___rarg(x_30, x_33);
lean_dec(x_33);
lean_dec(x_30);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_1);
x_36 = l_Lean_Syntax_getKind(x_1);
x_37 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_35, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = l_Lean_Elab_Tactic_getEnv___rarg(x_28);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Elab_macroAttribute;
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
x_43 = l_Lean_PersistentEnvExtension_getState___rarg(x_42, x_39);
lean_dec(x_39);
lean_dec(x_42);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_44, x_36);
lean_dec(x_36);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_box(0);
x_47 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_46, x_2, x_40);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec(x_45);
x_49 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_48, x_2, x_40);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_36);
x_50 = lean_ctor_get(x_37, 0);
lean_inc(x_50);
lean_dec(x_37);
lean_inc(x_28);
x_51 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_28, x_1, x_50, x_2, x_28);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_27);
if (x_52 == 0)
{
return x_27;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_27, 0);
x_54 = lean_ctor_get(x_27, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_27);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_57 = lean_unsigned_to_nat(2u);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_box(0);
x_60 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_57, x_56, x_58, x_59, x_2, x_4);
lean_dec(x_56);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_62 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_61, x_2, x_4);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_17, 0);
x_64 = lean_ctor_get(x_17, 1);
x_65 = lean_ctor_get(x_17, 2);
x_66 = lean_ctor_get(x_17, 3);
x_67 = lean_ctor_get(x_17, 4);
x_68 = lean_ctor_get(x_17, 5);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_17);
x_69 = lean_nat_add(x_68, x_14);
x_70 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_64);
lean_ctor_set(x_70, 2, x_65);
lean_ctor_set(x_70, 3, x_66);
lean_ctor_set(x_70, 4, x_67);
lean_ctor_set(x_70, 5, x_69);
lean_ctor_set(x_4, 0, x_70);
lean_ctor_set(x_5, 9, x_68);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
x_72 = l_Lean_nullKind;
x_73 = lean_name_eq(x_71, x_72);
lean_dec(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_inc(x_1);
x_74 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_74, 0, x_1);
x_75 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__3;
lean_inc(x_1);
x_76 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_76, 0, x_75);
lean_closure_set(x_76, 1, x_1);
lean_closure_set(x_76, 2, x_74);
lean_inc(x_2);
x_77 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_76, x_2, x_4);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_Lean_PersistentEnvExtension_getState___rarg(x_80, x_83);
lean_dec(x_83);
lean_dec(x_80);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
lean_inc(x_1);
x_86 = l_Lean_Syntax_getKind(x_1);
x_87 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_85, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_88 = l_Lean_Elab_Tactic_getEnv___rarg(x_78);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Elab_macroAttribute;
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
x_93 = l_Lean_PersistentEnvExtension_getState___rarg(x_92, x_89);
lean_dec(x_89);
lean_dec(x_92);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_95 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_94, x_86);
lean_dec(x_86);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_box(0);
x_97 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_96, x_2, x_90);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
lean_dec(x_95);
x_99 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_98, x_2, x_90);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_86);
x_100 = lean_ctor_get(x_87, 0);
lean_inc(x_100);
lean_dec(x_87);
lean_inc(x_78);
x_101 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_78, x_1, x_100, x_2, x_78);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_2);
lean_dec(x_1);
x_102 = lean_ctor_get(x_77, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_77, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_104 = x_77;
} else {
 lean_dec_ref(x_77);
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
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_107 = lean_unsigned_to_nat(2u);
x_108 = lean_unsigned_to_nat(0u);
x_109 = lean_box(0);
x_110 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_107, x_106, x_108, x_109, x_2, x_4);
lean_dec(x_106);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_112 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_111, x_2, x_4);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_113 = lean_ctor_get(x_4, 0);
x_114 = lean_ctor_get(x_4, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_4);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_113, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_113, 3);
lean_inc(x_118);
x_119 = lean_ctor_get(x_113, 4);
lean_inc(x_119);
x_120 = lean_ctor_get(x_113, 5);
lean_inc(x_120);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 lean_ctor_release(x_113, 4);
 lean_ctor_release(x_113, 5);
 x_121 = x_113;
} else {
 lean_dec_ref(x_113);
 x_121 = lean_box(0);
}
x_122 = lean_nat_add(x_120, x_14);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 6, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_115);
lean_ctor_set(x_123, 1, x_116);
lean_ctor_set(x_123, 2, x_117);
lean_ctor_set(x_123, 3, x_118);
lean_ctor_set(x_123, 4, x_119);
lean_ctor_set(x_123, 5, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_114);
lean_ctor_set(x_5, 9, x_120);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = lean_ctor_get(x_1, 0);
lean_inc(x_125);
x_126 = l_Lean_nullKind;
x_127 = lean_name_eq(x_125, x_126);
lean_dec(x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_inc(x_1);
x_128 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_128, 0, x_1);
x_129 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__3;
lean_inc(x_1);
x_130 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_130, 0, x_129);
lean_closure_set(x_130, 1, x_1);
lean_closure_set(x_130, 2, x_128);
lean_inc(x_2);
x_131 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_130, x_2, x_124);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec(x_136);
x_138 = l_Lean_PersistentEnvExtension_getState___rarg(x_134, x_137);
lean_dec(x_137);
lean_dec(x_134);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
lean_inc(x_1);
x_140 = l_Lean_Syntax_getKind(x_1);
x_141 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_139, x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_142 = l_Lean_Elab_Tactic_getEnv___rarg(x_132);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = l_Lean_Elab_macroAttribute;
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
x_147 = l_Lean_PersistentEnvExtension_getState___rarg(x_146, x_143);
lean_dec(x_143);
lean_dec(x_146);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_149 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_148, x_140);
lean_dec(x_140);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_box(0);
x_151 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_150, x_2, x_144);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_149, 0);
lean_inc(x_152);
lean_dec(x_149);
x_153 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_152, x_2, x_144);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_140);
x_154 = lean_ctor_get(x_141, 0);
lean_inc(x_154);
lean_dec(x_141);
lean_inc(x_132);
x_155 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_132, x_1, x_154, x_2, x_132);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_2);
lean_dec(x_1);
x_156 = lean_ctor_get(x_131, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_131, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_158 = x_131;
} else {
 lean_dec_ref(x_131);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_161 = lean_unsigned_to_nat(2u);
x_162 = lean_unsigned_to_nat(0u);
x_163 = lean_box(0);
x_164 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_161, x_160, x_162, x_163, x_2, x_124);
lean_dec(x_160);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_166 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_165, x_2, x_124);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_167 = lean_ctor_get(x_6, 0);
x_168 = lean_ctor_get(x_6, 1);
x_169 = lean_ctor_get(x_6, 2);
x_170 = lean_ctor_get(x_6, 3);
x_171 = lean_ctor_get(x_6, 4);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_6);
x_172 = lean_unsigned_to_nat(1u);
x_173 = lean_nat_add(x_170, x_172);
lean_dec(x_170);
x_174 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_174, 0, x_167);
lean_ctor_set(x_174, 1, x_168);
lean_ctor_set(x_174, 2, x_169);
lean_ctor_set(x_174, 3, x_173);
lean_ctor_set(x_174, 4, x_171);
x_175 = lean_ctor_get(x_4, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_4, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_177 = x_4;
} else {
 lean_dec_ref(x_4);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_175, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_175, 2);
lean_inc(x_180);
x_181 = lean_ctor_get(x_175, 3);
lean_inc(x_181);
x_182 = lean_ctor_get(x_175, 4);
lean_inc(x_182);
x_183 = lean_ctor_get(x_175, 5);
lean_inc(x_183);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 lean_ctor_release(x_175, 2);
 lean_ctor_release(x_175, 3);
 lean_ctor_release(x_175, 4);
 lean_ctor_release(x_175, 5);
 x_184 = x_175;
} else {
 lean_dec_ref(x_175);
 x_184 = lean_box(0);
}
x_185 = lean_nat_add(x_183, x_172);
if (lean_is_scalar(x_184)) {
 x_186 = lean_alloc_ctor(0, 6, 0);
} else {
 x_186 = x_184;
}
lean_ctor_set(x_186, 0, x_178);
lean_ctor_set(x_186, 1, x_179);
lean_ctor_set(x_186, 2, x_180);
lean_ctor_set(x_186, 3, x_181);
lean_ctor_set(x_186, 4, x_182);
lean_ctor_set(x_186, 5, x_185);
if (lean_is_scalar(x_177)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_177;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_176);
lean_ctor_set(x_5, 9, x_183);
lean_ctor_set(x_5, 0, x_174);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_188 = lean_ctor_get(x_1, 0);
lean_inc(x_188);
x_189 = l_Lean_nullKind;
x_190 = lean_name_eq(x_188, x_189);
lean_dec(x_188);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_inc(x_1);
x_191 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_191, 0, x_1);
x_192 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__3;
lean_inc(x_1);
x_193 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_193, 0, x_192);
lean_closure_set(x_193, 1, x_1);
lean_closure_set(x_193, 2, x_191);
lean_inc(x_2);
x_194 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_193, x_2, x_187);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_196 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
x_198 = lean_ctor_get(x_195, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
lean_dec(x_198);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
lean_dec(x_199);
x_201 = l_Lean_PersistentEnvExtension_getState___rarg(x_197, x_200);
lean_dec(x_200);
lean_dec(x_197);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec(x_201);
lean_inc(x_1);
x_203 = l_Lean_Syntax_getKind(x_1);
x_204 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_202, x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_205 = l_Lean_Elab_Tactic_getEnv___rarg(x_195);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = l_Lean_Elab_macroAttribute;
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
x_210 = l_Lean_PersistentEnvExtension_getState___rarg(x_209, x_206);
lean_dec(x_206);
lean_dec(x_209);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_212 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_211, x_203);
lean_dec(x_203);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_box(0);
x_214 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_213, x_2, x_207);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_212, 0);
lean_inc(x_215);
lean_dec(x_212);
x_216 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_215, x_2, x_207);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_203);
x_217 = lean_ctor_get(x_204, 0);
lean_inc(x_217);
lean_dec(x_204);
lean_inc(x_195);
x_218 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_195, x_1, x_217, x_2, x_195);
return x_218;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_2);
lean_dec(x_1);
x_219 = lean_ctor_get(x_194, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_194, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_221 = x_194;
} else {
 lean_dec_ref(x_194);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_220);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_223 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_224 = lean_unsigned_to_nat(2u);
x_225 = lean_unsigned_to_nat(0u);
x_226 = lean_box(0);
x_227 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_224, x_223, x_225, x_226, x_2, x_187);
lean_dec(x_223);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; 
x_228 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_229 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_228, x_2, x_187);
return x_229;
}
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; uint8_t x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_230 = lean_ctor_get(x_5, 1);
x_231 = lean_ctor_get(x_5, 2);
x_232 = lean_ctor_get(x_5, 3);
x_233 = lean_ctor_get(x_5, 4);
x_234 = lean_ctor_get(x_5, 5);
x_235 = lean_ctor_get(x_5, 6);
x_236 = lean_ctor_get(x_5, 7);
x_237 = lean_ctor_get(x_5, 8);
x_238 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_239 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_5);
x_240 = lean_ctor_get(x_6, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_6, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_6, 2);
lean_inc(x_242);
x_243 = lean_ctor_get(x_6, 3);
lean_inc(x_243);
x_244 = lean_ctor_get(x_6, 4);
lean_inc(x_244);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_245 = x_6;
} else {
 lean_dec_ref(x_6);
 x_245 = lean_box(0);
}
x_246 = lean_unsigned_to_nat(1u);
x_247 = lean_nat_add(x_243, x_246);
lean_dec(x_243);
if (lean_is_scalar(x_245)) {
 x_248 = lean_alloc_ctor(0, 5, 0);
} else {
 x_248 = x_245;
}
lean_ctor_set(x_248, 0, x_240);
lean_ctor_set(x_248, 1, x_241);
lean_ctor_set(x_248, 2, x_242);
lean_ctor_set(x_248, 3, x_247);
lean_ctor_set(x_248, 4, x_244);
x_249 = lean_ctor_get(x_4, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_4, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_251 = x_4;
} else {
 lean_dec_ref(x_4);
 x_251 = lean_box(0);
}
x_252 = lean_ctor_get(x_249, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_249, 1);
lean_inc(x_253);
x_254 = lean_ctor_get(x_249, 2);
lean_inc(x_254);
x_255 = lean_ctor_get(x_249, 3);
lean_inc(x_255);
x_256 = lean_ctor_get(x_249, 4);
lean_inc(x_256);
x_257 = lean_ctor_get(x_249, 5);
lean_inc(x_257);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 lean_ctor_release(x_249, 2);
 lean_ctor_release(x_249, 3);
 lean_ctor_release(x_249, 4);
 lean_ctor_release(x_249, 5);
 x_258 = x_249;
} else {
 lean_dec_ref(x_249);
 x_258 = lean_box(0);
}
x_259 = lean_nat_add(x_257, x_246);
if (lean_is_scalar(x_258)) {
 x_260 = lean_alloc_ctor(0, 6, 0);
} else {
 x_260 = x_258;
}
lean_ctor_set(x_260, 0, x_252);
lean_ctor_set(x_260, 1, x_253);
lean_ctor_set(x_260, 2, x_254);
lean_ctor_set(x_260, 3, x_255);
lean_ctor_set(x_260, 4, x_256);
lean_ctor_set(x_260, 5, x_259);
if (lean_is_scalar(x_251)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_251;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_250);
x_262 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_262, 0, x_248);
lean_ctor_set(x_262, 1, x_230);
lean_ctor_set(x_262, 2, x_231);
lean_ctor_set(x_262, 3, x_232);
lean_ctor_set(x_262, 4, x_233);
lean_ctor_set(x_262, 5, x_234);
lean_ctor_set(x_262, 6, x_235);
lean_ctor_set(x_262, 7, x_236);
lean_ctor_set(x_262, 8, x_237);
lean_ctor_set(x_262, 9, x_257);
lean_ctor_set_uint8(x_262, sizeof(void*)*10, x_238);
lean_ctor_set_uint8(x_262, sizeof(void*)*10 + 1, x_239);
lean_ctor_set(x_2, 0, x_262);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_263 = lean_ctor_get(x_1, 0);
lean_inc(x_263);
x_264 = l_Lean_nullKind;
x_265 = lean_name_eq(x_263, x_264);
lean_dec(x_263);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_inc(x_1);
x_266 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_266, 0, x_1);
x_267 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__3;
lean_inc(x_1);
x_268 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_268, 0, x_267);
lean_closure_set(x_268, 1, x_1);
lean_closure_set(x_268, 2, x_266);
lean_inc(x_2);
x_269 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_268, x_2, x_261);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
x_271 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_270, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
lean_dec(x_273);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
lean_dec(x_274);
x_276 = l_Lean_PersistentEnvExtension_getState___rarg(x_272, x_275);
lean_dec(x_275);
lean_dec(x_272);
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
lean_dec(x_276);
lean_inc(x_1);
x_278 = l_Lean_Syntax_getKind(x_1);
x_279 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_277, x_278);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_280 = l_Lean_Elab_Tactic_getEnv___rarg(x_270);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_283 = l_Lean_Elab_macroAttribute;
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
x_285 = l_Lean_PersistentEnvExtension_getState___rarg(x_284, x_281);
lean_dec(x_281);
lean_dec(x_284);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
lean_dec(x_285);
x_287 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_286, x_278);
lean_dec(x_278);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_box(0);
x_289 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_288, x_2, x_282);
return x_289;
}
else
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_287, 0);
lean_inc(x_290);
lean_dec(x_287);
x_291 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_290, x_2, x_282);
return x_291;
}
}
else
{
lean_object* x_292; lean_object* x_293; 
lean_dec(x_278);
x_292 = lean_ctor_get(x_279, 0);
lean_inc(x_292);
lean_dec(x_279);
lean_inc(x_270);
x_293 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_270, x_1, x_292, x_2, x_270);
return x_293;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_2);
lean_dec(x_1);
x_294 = lean_ctor_get(x_269, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_269, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_296 = x_269;
} else {
 lean_dec_ref(x_269);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_295);
return x_297;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_298 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_299 = lean_unsigned_to_nat(2u);
x_300 = lean_unsigned_to_nat(0u);
x_301 = lean_box(0);
x_302 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_299, x_298, x_300, x_301, x_2, x_261);
lean_dec(x_298);
return x_302;
}
}
else
{
lean_object* x_303; lean_object* x_304; 
x_303 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_304 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_303, x_2, x_261);
return x_304;
}
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; uint8_t x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_305 = lean_ctor_get(x_2, 1);
x_306 = lean_ctor_get(x_2, 2);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_2);
x_307 = lean_ctor_get(x_5, 1);
lean_inc(x_307);
x_308 = lean_ctor_get(x_5, 2);
lean_inc(x_308);
x_309 = lean_ctor_get(x_5, 3);
lean_inc(x_309);
x_310 = lean_ctor_get(x_5, 4);
lean_inc(x_310);
x_311 = lean_ctor_get(x_5, 5);
lean_inc(x_311);
x_312 = lean_ctor_get(x_5, 6);
lean_inc(x_312);
x_313 = lean_ctor_get(x_5, 7);
lean_inc(x_313);
x_314 = lean_ctor_get(x_5, 8);
lean_inc(x_314);
x_315 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_316 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
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
 x_317 = x_5;
} else {
 lean_dec_ref(x_5);
 x_317 = lean_box(0);
}
x_318 = lean_ctor_get(x_6, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_6, 1);
lean_inc(x_319);
x_320 = lean_ctor_get(x_6, 2);
lean_inc(x_320);
x_321 = lean_ctor_get(x_6, 3);
lean_inc(x_321);
x_322 = lean_ctor_get(x_6, 4);
lean_inc(x_322);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_323 = x_6;
} else {
 lean_dec_ref(x_6);
 x_323 = lean_box(0);
}
x_324 = lean_unsigned_to_nat(1u);
x_325 = lean_nat_add(x_321, x_324);
lean_dec(x_321);
if (lean_is_scalar(x_323)) {
 x_326 = lean_alloc_ctor(0, 5, 0);
} else {
 x_326 = x_323;
}
lean_ctor_set(x_326, 0, x_318);
lean_ctor_set(x_326, 1, x_319);
lean_ctor_set(x_326, 2, x_320);
lean_ctor_set(x_326, 3, x_325);
lean_ctor_set(x_326, 4, x_322);
x_327 = lean_ctor_get(x_4, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_4, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_329 = x_4;
} else {
 lean_dec_ref(x_4);
 x_329 = lean_box(0);
}
x_330 = lean_ctor_get(x_327, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_327, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_327, 2);
lean_inc(x_332);
x_333 = lean_ctor_get(x_327, 3);
lean_inc(x_333);
x_334 = lean_ctor_get(x_327, 4);
lean_inc(x_334);
x_335 = lean_ctor_get(x_327, 5);
lean_inc(x_335);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 lean_ctor_release(x_327, 2);
 lean_ctor_release(x_327, 3);
 lean_ctor_release(x_327, 4);
 lean_ctor_release(x_327, 5);
 x_336 = x_327;
} else {
 lean_dec_ref(x_327);
 x_336 = lean_box(0);
}
x_337 = lean_nat_add(x_335, x_324);
if (lean_is_scalar(x_336)) {
 x_338 = lean_alloc_ctor(0, 6, 0);
} else {
 x_338 = x_336;
}
lean_ctor_set(x_338, 0, x_330);
lean_ctor_set(x_338, 1, x_331);
lean_ctor_set(x_338, 2, x_332);
lean_ctor_set(x_338, 3, x_333);
lean_ctor_set(x_338, 4, x_334);
lean_ctor_set(x_338, 5, x_337);
if (lean_is_scalar(x_329)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_329;
}
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_328);
if (lean_is_scalar(x_317)) {
 x_340 = lean_alloc_ctor(0, 10, 2);
} else {
 x_340 = x_317;
}
lean_ctor_set(x_340, 0, x_326);
lean_ctor_set(x_340, 1, x_307);
lean_ctor_set(x_340, 2, x_308);
lean_ctor_set(x_340, 3, x_309);
lean_ctor_set(x_340, 4, x_310);
lean_ctor_set(x_340, 5, x_311);
lean_ctor_set(x_340, 6, x_312);
lean_ctor_set(x_340, 7, x_313);
lean_ctor_set(x_340, 8, x_314);
lean_ctor_set(x_340, 9, x_335);
lean_ctor_set_uint8(x_340, sizeof(void*)*10, x_315);
lean_ctor_set_uint8(x_340, sizeof(void*)*10 + 1, x_316);
x_341 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_305);
lean_ctor_set(x_341, 2, x_306);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_342 = lean_ctor_get(x_1, 0);
lean_inc(x_342);
x_343 = l_Lean_nullKind;
x_344 = lean_name_eq(x_342, x_343);
lean_dec(x_342);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_inc(x_1);
x_345 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_345, 0, x_1);
x_346 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__3;
lean_inc(x_1);
x_347 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_347, 0, x_346);
lean_closure_set(x_347, 1, x_1);
lean_closure_set(x_347, 2, x_345);
lean_inc(x_341);
x_348 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_347, x_341, x_339);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_349 = lean_ctor_get(x_348, 1);
lean_inc(x_349);
lean_dec(x_348);
x_350 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_351 = lean_ctor_get(x_350, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_349, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
lean_dec(x_352);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
lean_dec(x_353);
x_355 = l_Lean_PersistentEnvExtension_getState___rarg(x_351, x_354);
lean_dec(x_354);
lean_dec(x_351);
x_356 = lean_ctor_get(x_355, 1);
lean_inc(x_356);
lean_dec(x_355);
lean_inc(x_1);
x_357 = l_Lean_Syntax_getKind(x_1);
x_358 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_356, x_357);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_359 = l_Lean_Elab_Tactic_getEnv___rarg(x_349);
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
x_362 = l_Lean_Elab_macroAttribute;
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
x_364 = l_Lean_PersistentEnvExtension_getState___rarg(x_363, x_360);
lean_dec(x_360);
lean_dec(x_363);
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
lean_dec(x_364);
x_366 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_365, x_357);
lean_dec(x_357);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; 
x_367 = lean_box(0);
x_368 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_367, x_341, x_361);
return x_368;
}
else
{
lean_object* x_369; lean_object* x_370; 
x_369 = lean_ctor_get(x_366, 0);
lean_inc(x_369);
lean_dec(x_366);
x_370 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_369, x_341, x_361);
return x_370;
}
}
else
{
lean_object* x_371; lean_object* x_372; 
lean_dec(x_357);
x_371 = lean_ctor_get(x_358, 0);
lean_inc(x_371);
lean_dec(x_358);
lean_inc(x_349);
x_372 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_349, x_1, x_371, x_341, x_349);
return x_372;
}
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_341);
lean_dec(x_1);
x_373 = lean_ctor_get(x_348, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_348, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_375 = x_348;
} else {
 lean_dec_ref(x_348);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(1, 2, 0);
} else {
 x_376 = x_375;
}
lean_ctor_set(x_376, 0, x_373);
lean_ctor_set(x_376, 1, x_374);
return x_376;
}
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_377 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_378 = lean_unsigned_to_nat(2u);
x_379 = lean_unsigned_to_nat(0u);
x_380 = lean_box(0);
x_381 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_378, x_377, x_379, x_380, x_341, x_339);
lean_dec(x_377);
return x_381;
}
}
else
{
lean_object* x_382; lean_object* x_383; 
x_382 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_383 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_382, x_341, x_339);
return x_383;
}
}
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5(x_1, x_2);
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
x_12 = lean_ctor_get(x_6, 8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_6, 8, x_14);
x_15 = l_Lean_Elab_Tactic_evalTactic___main(x_7, x_3, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 2);
x_19 = lean_ctor_get(x_6, 3);
x_20 = lean_ctor_get(x_6, 4);
x_21 = lean_ctor_get(x_6, 5);
x_22 = lean_ctor_get(x_6, 6);
x_23 = lean_ctor_get(x_6, 7);
x_24 = lean_ctor_get(x_6, 8);
x_25 = lean_ctor_get(x_6, 9);
x_26 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_27 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
lean_inc(x_25);
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
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_7);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
x_30 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_17);
lean_ctor_set(x_30, 2, x_18);
lean_ctor_set(x_30, 3, x_19);
lean_ctor_set(x_30, 4, x_20);
lean_ctor_set(x_30, 5, x_21);
lean_ctor_set(x_30, 6, x_22);
lean_ctor_set(x_30, 7, x_23);
lean_ctor_set(x_30, 8, x_29);
lean_ctor_set(x_30, 9, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*10, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*10 + 1, x_27);
lean_ctor_set(x_3, 0, x_30);
x_31 = l_Lean_Elab_Tactic_evalTactic___main(x_7, x_3, x_8);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_32 = lean_ctor_get(x_3, 1);
x_33 = lean_ctor_get(x_3, 2);
lean_inc(x_33);
lean_inc(x_32);
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
x_43 = lean_ctor_get(x_6, 9);
lean_inc(x_43);
x_44 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_45 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
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
 x_46 = x_6;
} else {
 lean_dec_ref(x_6);
 x_46 = lean_box(0);
}
lean_inc(x_7);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_7);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 10, 2);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_34);
lean_ctor_set(x_49, 1, x_35);
lean_ctor_set(x_49, 2, x_36);
lean_ctor_set(x_49, 3, x_37);
lean_ctor_set(x_49, 4, x_38);
lean_ctor_set(x_49, 5, x_39);
lean_ctor_set(x_49, 6, x_40);
lean_ctor_set(x_49, 7, x_41);
lean_ctor_set(x_49, 8, x_48);
lean_ctor_set(x_49, 9, x_43);
lean_ctor_set_uint8(x_49, sizeof(void*)*10, x_44);
lean_ctor_set_uint8(x_49, sizeof(void*)*10 + 1, x_45);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_32);
lean_ctor_set(x_50, 2, x_33);
x_51 = l_Lean_Elab_Tactic_evalTactic___main(x_7, x_50, x_8);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_5);
if (x_52 == 0)
{
return x_5;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_5, 0);
x_54 = lean_ctor_get(x_5, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_5);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 2);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 4);
x_25 = lean_ctor_get(x_6, 5);
x_26 = lean_ctor_get(x_6, 6);
x_27 = lean_ctor_get(x_6, 7);
x_28 = lean_ctor_get(x_6, 8);
x_29 = lean_ctor_get(x_6, 9);
x_30 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_31 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_32 = lean_ctor_get(x_7, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_7, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_7, 4);
lean_inc(x_34);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 x_35 = x_7;
} else {
 lean_dec_ref(x_7);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 5, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_1);
lean_ctor_set(x_36, 2, x_2);
lean_ctor_set(x_36, 3, x_33);
lean_ctor_set(x_36, 4, x_34);
x_37 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_21);
lean_ctor_set(x_37, 2, x_22);
lean_ctor_set(x_37, 3, x_23);
lean_ctor_set(x_37, 4, x_24);
lean_ctor_set(x_37, 5, x_25);
lean_ctor_set(x_37, 6, x_26);
lean_ctor_set(x_37, 7, x_27);
lean_ctor_set(x_37, 8, x_28);
lean_ctor_set(x_37, 9, x_29);
lean_ctor_set_uint8(x_37, sizeof(void*)*10, x_30);
lean_ctor_set_uint8(x_37, sizeof(void*)*10 + 1, x_31);
lean_ctor_set(x_4, 0, x_37);
x_38 = lean_apply_2(x_3, x_4, x_5);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_39 = lean_ctor_get(x_4, 1);
x_40 = lean_ctor_get(x_4, 2);
lean_inc(x_40);
lean_inc(x_39);
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
x_49 = lean_ctor_get(x_6, 9);
lean_inc(x_49);
x_50 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_51 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
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
 x_52 = x_6;
} else {
 lean_dec_ref(x_6);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_7, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_7, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_7, 4);
lean_inc(x_55);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 x_56 = x_7;
} else {
 lean_dec_ref(x_7);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 5, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_1);
lean_ctor_set(x_57, 2, x_2);
lean_ctor_set(x_57, 3, x_54);
lean_ctor_set(x_57, 4, x_55);
if (lean_is_scalar(x_52)) {
 x_58 = lean_alloc_ctor(0, 10, 2);
} else {
 x_58 = x_52;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_41);
lean_ctor_set(x_58, 2, x_42);
lean_ctor_set(x_58, 3, x_43);
lean_ctor_set(x_58, 4, x_44);
lean_ctor_set(x_58, 5, x_45);
lean_ctor_set(x_58, 6, x_46);
lean_ctor_set(x_58, 7, x_47);
lean_ctor_set(x_58, 8, x_48);
lean_ctor_set(x_58, 9, x_49);
lean_ctor_set_uint8(x_58, sizeof(void*)*10, x_50);
lean_ctor_set_uint8(x_58, sizeof(void*)*10 + 1, x_51);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_39);
lean_ctor_set(x_59, 2, x_40);
x_60 = lean_apply_2(x_3, x_59, x_5);
return x_60;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
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
x_8 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_2);
x_9 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Elab_Tactic_save(x_10);
lean_inc(x_10);
x_12 = lean_apply_2(x_1, x_2, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_12, 1);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_15, 2);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_16, 2);
lean_dec(x_26);
lean_ctor_set(x_16, 2, x_7);
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_7);
lean_ctor_set(x_15, 2, x_29);
return x_12;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
x_32 = lean_ctor_get(x_15, 3);
x_33 = lean_ctor_get(x_15, 4);
x_34 = lean_ctor_get(x_15, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_35 = lean_ctor_get(x_16, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 x_37 = x_16;
} else {
 lean_dec_ref(x_16);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 3, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_7);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_31);
lean_ctor_set(x_39, 2, x_38);
lean_ctor_set(x_39, 3, x_32);
lean_ctor_set(x_39, 4, x_33);
lean_ctor_set(x_39, 5, x_34);
lean_ctor_set(x_14, 0, x_39);
return x_12;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_40 = lean_ctor_get(x_14, 1);
x_41 = lean_ctor_get(x_14, 2);
x_42 = lean_ctor_get(x_14, 3);
x_43 = lean_ctor_get(x_14, 4);
x_44 = lean_ctor_get(x_14, 5);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_14);
x_45 = lean_ctor_get(x_15, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_15, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_15, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_15, 4);
lean_inc(x_48);
x_49 = lean_ctor_get(x_15, 5);
lean_inc(x_49);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 lean_ctor_release(x_15, 4);
 lean_ctor_release(x_15, 5);
 x_50 = x_15;
} else {
 lean_dec_ref(x_15);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_16, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_16, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 x_53 = x_16;
} else {
 lean_dec_ref(x_16);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 3, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set(x_54, 2, x_7);
if (lean_is_scalar(x_50)) {
 x_55 = lean_alloc_ctor(0, 6, 0);
} else {
 x_55 = x_50;
}
lean_ctor_set(x_55, 0, x_45);
lean_ctor_set(x_55, 1, x_46);
lean_ctor_set(x_55, 2, x_54);
lean_ctor_set(x_55, 3, x_47);
lean_ctor_set(x_55, 4, x_48);
lean_ctor_set(x_55, 5, x_49);
x_56 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_40);
lean_ctor_set(x_56, 2, x_41);
lean_ctor_set(x_56, 3, x_42);
lean_ctor_set(x_56, 4, x_43);
lean_ctor_set(x_56, 5, x_44);
lean_ctor_set(x_13, 0, x_56);
return x_12;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_57 = lean_ctor_get(x_13, 1);
lean_inc(x_57);
lean_dec(x_13);
x_58 = lean_ctor_get(x_14, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_14, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_14, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_14, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_14, 5);
lean_inc(x_62);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 lean_ctor_release(x_14, 5);
 x_63 = x_14;
} else {
 lean_dec_ref(x_14);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_15, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_15, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_15, 3);
lean_inc(x_66);
x_67 = lean_ctor_get(x_15, 4);
lean_inc(x_67);
x_68 = lean_ctor_get(x_15, 5);
lean_inc(x_68);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 lean_ctor_release(x_15, 4);
 lean_ctor_release(x_15, 5);
 x_69 = x_15;
} else {
 lean_dec_ref(x_15);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_16, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_16, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 x_72 = x_16;
} else {
 lean_dec_ref(x_16);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 3, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
lean_ctor_set(x_73, 2, x_7);
if (lean_is_scalar(x_69)) {
 x_74 = lean_alloc_ctor(0, 6, 0);
} else {
 x_74 = x_69;
}
lean_ctor_set(x_74, 0, x_64);
lean_ctor_set(x_74, 1, x_65);
lean_ctor_set(x_74, 2, x_73);
lean_ctor_set(x_74, 3, x_66);
lean_ctor_set(x_74, 4, x_67);
lean_ctor_set(x_74, 5, x_68);
if (lean_is_scalar(x_63)) {
 x_75 = lean_alloc_ctor(0, 6, 0);
} else {
 x_75 = x_63;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_58);
lean_ctor_set(x_75, 2, x_59);
lean_ctor_set(x_75, 3, x_60);
lean_ctor_set(x_75, 4, x_61);
lean_ctor_set(x_75, 5, x_62);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_57);
lean_ctor_set(x_12, 1, x_76);
return x_12;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_77 = lean_ctor_get(x_12, 0);
lean_inc(x_77);
lean_dec(x_12);
x_78 = lean_ctor_get(x_13, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_79 = x_13;
} else {
 lean_dec_ref(x_13);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_14, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_14, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_14, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_14, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_14, 5);
lean_inc(x_84);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 lean_ctor_release(x_14, 5);
 x_85 = x_14;
} else {
 lean_dec_ref(x_14);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_15, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_15, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_15, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_15, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_15, 5);
lean_inc(x_90);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 lean_ctor_release(x_15, 4);
 lean_ctor_release(x_15, 5);
 x_91 = x_15;
} else {
 lean_dec_ref(x_15);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_16, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_16, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 x_94 = x_16;
} else {
 lean_dec_ref(x_16);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 3, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_7);
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
if (lean_is_scalar(x_79)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_79;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_78);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_77);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_12);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_101 = lean_ctor_get(x_12, 1);
x_102 = l_Lean_Elab_Tactic_restore(x_101, x_11);
lean_dec(x_11);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_104, 2);
lean_inc(x_105);
x_106 = !lean_is_exclusive(x_103);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_103, 0);
lean_dec(x_107);
x_108 = !lean_is_exclusive(x_104);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_104, 2);
lean_dec(x_109);
x_110 = !lean_is_exclusive(x_105);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_105, 2);
lean_dec(x_111);
lean_ctor_set(x_105, 2, x_7);
x_112 = !lean_is_exclusive(x_10);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_10, 0);
lean_dec(x_113);
lean_ctor_set(x_10, 0, x_103);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_10, 1);
lean_inc(x_114);
lean_dec(x_10);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_103);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_12, 1, x_115);
return x_12;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_116 = lean_ctor_get(x_105, 0);
x_117 = lean_ctor_get(x_105, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_105);
x_118 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_118, 2, x_7);
lean_ctor_set(x_104, 2, x_118);
x_119 = lean_ctor_get(x_10, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_120 = x_10;
} else {
 lean_dec_ref(x_10);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_103);
lean_ctor_set(x_121, 1, x_119);
lean_ctor_set(x_12, 1, x_121);
return x_12;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_122 = lean_ctor_get(x_104, 0);
x_123 = lean_ctor_get(x_104, 1);
x_124 = lean_ctor_get(x_104, 3);
x_125 = lean_ctor_get(x_104, 4);
x_126 = lean_ctor_get(x_104, 5);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_104);
x_127 = lean_ctor_get(x_105, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_105, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 lean_ctor_release(x_105, 2);
 x_129 = x_105;
} else {
 lean_dec_ref(x_105);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(0, 3, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
lean_ctor_set(x_130, 2, x_7);
x_131 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_131, 0, x_122);
lean_ctor_set(x_131, 1, x_123);
lean_ctor_set(x_131, 2, x_130);
lean_ctor_set(x_131, 3, x_124);
lean_ctor_set(x_131, 4, x_125);
lean_ctor_set(x_131, 5, x_126);
lean_ctor_set(x_103, 0, x_131);
x_132 = lean_ctor_get(x_10, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_133 = x_10;
} else {
 lean_dec_ref(x_10);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_103);
lean_ctor_set(x_134, 1, x_132);
lean_ctor_set(x_12, 1, x_134);
return x_12;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_135 = lean_ctor_get(x_103, 1);
x_136 = lean_ctor_get(x_103, 2);
x_137 = lean_ctor_get(x_103, 3);
x_138 = lean_ctor_get(x_103, 4);
x_139 = lean_ctor_get(x_103, 5);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_103);
x_140 = lean_ctor_get(x_104, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_104, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_104, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_104, 4);
lean_inc(x_143);
x_144 = lean_ctor_get(x_104, 5);
lean_inc(x_144);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 lean_ctor_release(x_104, 2);
 lean_ctor_release(x_104, 3);
 lean_ctor_release(x_104, 4);
 lean_ctor_release(x_104, 5);
 x_145 = x_104;
} else {
 lean_dec_ref(x_104);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_105, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_105, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 lean_ctor_release(x_105, 2);
 x_148 = x_105;
} else {
 lean_dec_ref(x_105);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(0, 3, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
lean_ctor_set(x_149, 2, x_7);
if (lean_is_scalar(x_145)) {
 x_150 = lean_alloc_ctor(0, 6, 0);
} else {
 x_150 = x_145;
}
lean_ctor_set(x_150, 0, x_140);
lean_ctor_set(x_150, 1, x_141);
lean_ctor_set(x_150, 2, x_149);
lean_ctor_set(x_150, 3, x_142);
lean_ctor_set(x_150, 4, x_143);
lean_ctor_set(x_150, 5, x_144);
x_151 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_135);
lean_ctor_set(x_151, 2, x_136);
lean_ctor_set(x_151, 3, x_137);
lean_ctor_set(x_151, 4, x_138);
lean_ctor_set(x_151, 5, x_139);
x_152 = lean_ctor_get(x_10, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_153 = x_10;
} else {
 lean_dec_ref(x_10);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
lean_ctor_set(x_12, 1, x_154);
return x_12;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_155 = lean_ctor_get(x_12, 0);
x_156 = lean_ctor_get(x_12, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_12);
x_157 = l_Lean_Elab_Tactic_restore(x_156, x_11);
lean_dec(x_11);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec(x_157);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_159, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_158, 2);
lean_inc(x_162);
x_163 = lean_ctor_get(x_158, 3);
lean_inc(x_163);
x_164 = lean_ctor_get(x_158, 4);
lean_inc(x_164);
x_165 = lean_ctor_get(x_158, 5);
lean_inc(x_165);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 lean_ctor_release(x_158, 5);
 x_166 = x_158;
} else {
 lean_dec_ref(x_158);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_159, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_159, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_159, 3);
lean_inc(x_169);
x_170 = lean_ctor_get(x_159, 4);
lean_inc(x_170);
x_171 = lean_ctor_get(x_159, 5);
lean_inc(x_171);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 lean_ctor_release(x_159, 2);
 lean_ctor_release(x_159, 3);
 lean_ctor_release(x_159, 4);
 lean_ctor_release(x_159, 5);
 x_172 = x_159;
} else {
 lean_dec_ref(x_159);
 x_172 = lean_box(0);
}
x_173 = lean_ctor_get(x_160, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_160, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 x_175 = x_160;
} else {
 lean_dec_ref(x_160);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(0, 3, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
lean_ctor_set(x_176, 2, x_7);
if (lean_is_scalar(x_172)) {
 x_177 = lean_alloc_ctor(0, 6, 0);
} else {
 x_177 = x_172;
}
lean_ctor_set(x_177, 0, x_167);
lean_ctor_set(x_177, 1, x_168);
lean_ctor_set(x_177, 2, x_176);
lean_ctor_set(x_177, 3, x_169);
lean_ctor_set(x_177, 4, x_170);
lean_ctor_set(x_177, 5, x_171);
if (lean_is_scalar(x_166)) {
 x_178 = lean_alloc_ctor(0, 6, 0);
} else {
 x_178 = x_166;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_161);
lean_ctor_set(x_178, 2, x_162);
lean_ctor_set(x_178, 3, x_163);
lean_ctor_set(x_178, 4, x_164);
lean_ctor_set(x_178, 5, x_165);
x_179 = lean_ctor_get(x_10, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_180 = x_10;
} else {
 lean_dec_ref(x_10);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_155);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_183 = !lean_is_exclusive(x_9);
if (x_183 == 0)
{
return x_9;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_9, 0);
x_185 = lean_ctor_get(x_9, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_9);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
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
x_10 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_3);
x_11 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_10, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Elab_Tactic_save(x_12);
lean_inc(x_12);
x_14 = lean_apply_2(x_2, x_3, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_14, 1);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_15, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_17, 2);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_18, 2);
lean_dec(x_28);
lean_ctor_set(x_18, 2, x_9);
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_9);
lean_ctor_set(x_17, 2, x_31);
return x_14;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
x_34 = lean_ctor_get(x_17, 3);
x_35 = lean_ctor_get(x_17, 4);
x_36 = lean_ctor_get(x_17, 5);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
x_37 = lean_ctor_get(x_18, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_18, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_39 = x_18;
} else {
 lean_dec_ref(x_18);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 3, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_9);
x_41 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_33);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set(x_41, 3, x_34);
lean_ctor_set(x_41, 4, x_35);
lean_ctor_set(x_41, 5, x_36);
lean_ctor_set(x_16, 0, x_41);
return x_14;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_42 = lean_ctor_get(x_16, 1);
x_43 = lean_ctor_get(x_16, 2);
x_44 = lean_ctor_get(x_16, 3);
x_45 = lean_ctor_get(x_16, 4);
x_46 = lean_ctor_get(x_16, 5);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_16);
x_47 = lean_ctor_get(x_17, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_17, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_17, 3);
lean_inc(x_49);
x_50 = lean_ctor_get(x_17, 4);
lean_inc(x_50);
x_51 = lean_ctor_get(x_17, 5);
lean_inc(x_51);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 lean_ctor_release(x_17, 5);
 x_52 = x_17;
} else {
 lean_dec_ref(x_17);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_18, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_18, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_55 = x_18;
} else {
 lean_dec_ref(x_18);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 3, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_56, 2, x_9);
if (lean_is_scalar(x_52)) {
 x_57 = lean_alloc_ctor(0, 6, 0);
} else {
 x_57 = x_52;
}
lean_ctor_set(x_57, 0, x_47);
lean_ctor_set(x_57, 1, x_48);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_49);
lean_ctor_set(x_57, 4, x_50);
lean_ctor_set(x_57, 5, x_51);
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_42);
lean_ctor_set(x_58, 2, x_43);
lean_ctor_set(x_58, 3, x_44);
lean_ctor_set(x_58, 4, x_45);
lean_ctor_set(x_58, 5, x_46);
lean_ctor_set(x_15, 0, x_58);
return x_14;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_59 = lean_ctor_get(x_15, 1);
lean_inc(x_59);
lean_dec(x_15);
x_60 = lean_ctor_get(x_16, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_16, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_16, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_16, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_16, 5);
lean_inc(x_64);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 lean_ctor_release(x_16, 5);
 x_65 = x_16;
} else {
 lean_dec_ref(x_16);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_17, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_17, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_17, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_17, 4);
lean_inc(x_69);
x_70 = lean_ctor_get(x_17, 5);
lean_inc(x_70);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 lean_ctor_release(x_17, 5);
 x_71 = x_17;
} else {
 lean_dec_ref(x_17);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_18, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_18, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_74 = x_18;
} else {
 lean_dec_ref(x_18);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 3, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
lean_ctor_set(x_75, 2, x_9);
if (lean_is_scalar(x_71)) {
 x_76 = lean_alloc_ctor(0, 6, 0);
} else {
 x_76 = x_71;
}
lean_ctor_set(x_76, 0, x_66);
lean_ctor_set(x_76, 1, x_67);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set(x_76, 3, x_68);
lean_ctor_set(x_76, 4, x_69);
lean_ctor_set(x_76, 5, x_70);
if (lean_is_scalar(x_65)) {
 x_77 = lean_alloc_ctor(0, 6, 0);
} else {
 x_77 = x_65;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_60);
lean_ctor_set(x_77, 2, x_61);
lean_ctor_set(x_77, 3, x_62);
lean_ctor_set(x_77, 4, x_63);
lean_ctor_set(x_77, 5, x_64);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_59);
lean_ctor_set(x_14, 1, x_78);
return x_14;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_79 = lean_ctor_get(x_14, 0);
lean_inc(x_79);
lean_dec(x_14);
x_80 = lean_ctor_get(x_15, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_81 = x_15;
} else {
 lean_dec_ref(x_15);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_16, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_16, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_16, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_16, 4);
lean_inc(x_85);
x_86 = lean_ctor_get(x_16, 5);
lean_inc(x_86);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 lean_ctor_release(x_16, 5);
 x_87 = x_16;
} else {
 lean_dec_ref(x_16);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_17, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_17, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_17, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_17, 4);
lean_inc(x_91);
x_92 = lean_ctor_get(x_17, 5);
lean_inc(x_92);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 lean_ctor_release(x_17, 5);
 x_93 = x_17;
} else {
 lean_dec_ref(x_17);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_18, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_18, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_96 = x_18;
} else {
 lean_dec_ref(x_18);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 3, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
lean_ctor_set(x_97, 2, x_9);
if (lean_is_scalar(x_93)) {
 x_98 = lean_alloc_ctor(0, 6, 0);
} else {
 x_98 = x_93;
}
lean_ctor_set(x_98, 0, x_88);
lean_ctor_set(x_98, 1, x_89);
lean_ctor_set(x_98, 2, x_97);
lean_ctor_set(x_98, 3, x_90);
lean_ctor_set(x_98, 4, x_91);
lean_ctor_set(x_98, 5, x_92);
if (lean_is_scalar(x_87)) {
 x_99 = lean_alloc_ctor(0, 6, 0);
} else {
 x_99 = x_87;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_82);
lean_ctor_set(x_99, 2, x_83);
lean_ctor_set(x_99, 3, x_84);
lean_ctor_set(x_99, 4, x_85);
lean_ctor_set(x_99, 5, x_86);
if (lean_is_scalar(x_81)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_81;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_80);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_79);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_14);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_103 = lean_ctor_get(x_14, 1);
x_104 = l_Lean_Elab_Tactic_restore(x_103, x_13);
lean_dec(x_13);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_106, 2);
lean_inc(x_107);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_105, 0);
lean_dec(x_109);
x_110 = !lean_is_exclusive(x_106);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_106, 2);
lean_dec(x_111);
x_112 = !lean_is_exclusive(x_107);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_107, 2);
lean_dec(x_113);
lean_ctor_set(x_107, 2, x_9);
x_114 = !lean_is_exclusive(x_12);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_12, 0);
lean_dec(x_115);
lean_ctor_set(x_12, 0, x_105);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_12, 1);
lean_inc(x_116);
lean_dec(x_12);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_105);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_14, 1, x_117);
return x_14;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_ctor_get(x_107, 0);
x_119 = lean_ctor_get(x_107, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_107);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_120, 2, x_9);
lean_ctor_set(x_106, 2, x_120);
x_121 = lean_ctor_get(x_12, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_122 = x_12;
} else {
 lean_dec_ref(x_12);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_105);
lean_ctor_set(x_123, 1, x_121);
lean_ctor_set(x_14, 1, x_123);
return x_14;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_124 = lean_ctor_get(x_106, 0);
x_125 = lean_ctor_get(x_106, 1);
x_126 = lean_ctor_get(x_106, 3);
x_127 = lean_ctor_get(x_106, 4);
x_128 = lean_ctor_get(x_106, 5);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_106);
x_129 = lean_ctor_get(x_107, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_107, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 x_131 = x_107;
} else {
 lean_dec_ref(x_107);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 3, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
lean_ctor_set(x_132, 2, x_9);
x_133 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_133, 0, x_124);
lean_ctor_set(x_133, 1, x_125);
lean_ctor_set(x_133, 2, x_132);
lean_ctor_set(x_133, 3, x_126);
lean_ctor_set(x_133, 4, x_127);
lean_ctor_set(x_133, 5, x_128);
lean_ctor_set(x_105, 0, x_133);
x_134 = lean_ctor_get(x_12, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_135 = x_12;
} else {
 lean_dec_ref(x_12);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_105);
lean_ctor_set(x_136, 1, x_134);
lean_ctor_set(x_14, 1, x_136);
return x_14;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_137 = lean_ctor_get(x_105, 1);
x_138 = lean_ctor_get(x_105, 2);
x_139 = lean_ctor_get(x_105, 3);
x_140 = lean_ctor_get(x_105, 4);
x_141 = lean_ctor_get(x_105, 5);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_105);
x_142 = lean_ctor_get(x_106, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_106, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_106, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_106, 4);
lean_inc(x_145);
x_146 = lean_ctor_get(x_106, 5);
lean_inc(x_146);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 lean_ctor_release(x_106, 4);
 lean_ctor_release(x_106, 5);
 x_147 = x_106;
} else {
 lean_dec_ref(x_106);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_107, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_107, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 x_150 = x_107;
} else {
 lean_dec_ref(x_107);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 3, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
lean_ctor_set(x_151, 2, x_9);
if (lean_is_scalar(x_147)) {
 x_152 = lean_alloc_ctor(0, 6, 0);
} else {
 x_152 = x_147;
}
lean_ctor_set(x_152, 0, x_142);
lean_ctor_set(x_152, 1, x_143);
lean_ctor_set(x_152, 2, x_151);
lean_ctor_set(x_152, 3, x_144);
lean_ctor_set(x_152, 4, x_145);
lean_ctor_set(x_152, 5, x_146);
x_153 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_137);
lean_ctor_set(x_153, 2, x_138);
lean_ctor_set(x_153, 3, x_139);
lean_ctor_set(x_153, 4, x_140);
lean_ctor_set(x_153, 5, x_141);
x_154 = lean_ctor_get(x_12, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_155 = x_12;
} else {
 lean_dec_ref(x_12);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
lean_ctor_set(x_14, 1, x_156);
return x_14;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_157 = lean_ctor_get(x_14, 0);
x_158 = lean_ctor_get(x_14, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_14);
x_159 = l_Lean_Elab_Tactic_restore(x_158, x_13);
lean_dec(x_13);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec(x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_161, 2);
lean_inc(x_162);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 2);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 3);
lean_inc(x_165);
x_166 = lean_ctor_get(x_160, 4);
lean_inc(x_166);
x_167 = lean_ctor_get(x_160, 5);
lean_inc(x_167);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 lean_ctor_release(x_160, 5);
 x_168 = x_160;
} else {
 lean_dec_ref(x_160);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_161, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_161, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_161, 3);
lean_inc(x_171);
x_172 = lean_ctor_get(x_161, 4);
lean_inc(x_172);
x_173 = lean_ctor_get(x_161, 5);
lean_inc(x_173);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 lean_ctor_release(x_161, 2);
 lean_ctor_release(x_161, 3);
 lean_ctor_release(x_161, 4);
 lean_ctor_release(x_161, 5);
 x_174 = x_161;
} else {
 lean_dec_ref(x_161);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_162, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_162, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 lean_ctor_release(x_162, 2);
 x_177 = x_162;
} else {
 lean_dec_ref(x_162);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(0, 3, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
lean_ctor_set(x_178, 2, x_9);
if (lean_is_scalar(x_174)) {
 x_179 = lean_alloc_ctor(0, 6, 0);
} else {
 x_179 = x_174;
}
lean_ctor_set(x_179, 0, x_169);
lean_ctor_set(x_179, 1, x_170);
lean_ctor_set(x_179, 2, x_178);
lean_ctor_set(x_179, 3, x_171);
lean_ctor_set(x_179, 4, x_172);
lean_ctor_set(x_179, 5, x_173);
if (lean_is_scalar(x_168)) {
 x_180 = lean_alloc_ctor(0, 6, 0);
} else {
 x_180 = x_168;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_163);
lean_ctor_set(x_180, 2, x_164);
lean_ctor_set(x_180, 3, x_165);
lean_ctor_set(x_180, 4, x_166);
lean_ctor_set(x_180, 5, x_167);
x_181 = lean_ctor_get(x_12, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_182 = x_12;
} else {
 lean_dec_ref(x_12);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_157);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_11);
if (x_185 == 0)
{
return x_11;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_11, 0);
x_187 = lean_ctor_get(x_11, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_11);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
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
lean_dec(x_5);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
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
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set(x_22, 2, x_11);
if (x_21 == 0)
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_15);
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
x_26 = lean_apply_2(x_2, x_22, x_9);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_31 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_22);
x_32 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_31, x_22, x_9);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Elab_Tactic_save(x_33);
lean_inc(x_33);
x_35 = lean_apply_2(x_2, x_22, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_34);
lean_dec(x_33);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 2);
lean_inc(x_39);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_35, 1);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_36, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_37, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_38, 2);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_39, 2);
lean_dec(x_49);
lean_ctor_set(x_39, 2, x_30);
return x_35;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_39);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_30);
lean_ctor_set(x_38, 2, x_52);
return x_35;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_38, 0);
x_54 = lean_ctor_get(x_38, 1);
x_55 = lean_ctor_get(x_38, 3);
x_56 = lean_ctor_get(x_38, 4);
x_57 = lean_ctor_get(x_38, 5);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_38);
x_58 = lean_ctor_get(x_39, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_39, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_60 = x_39;
} else {
 lean_dec_ref(x_39);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 3, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_30);
x_62 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_62, 0, x_53);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_55);
lean_ctor_set(x_62, 4, x_56);
lean_ctor_set(x_62, 5, x_57);
lean_ctor_set(x_37, 0, x_62);
return x_35;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_63 = lean_ctor_get(x_37, 1);
x_64 = lean_ctor_get(x_37, 2);
x_65 = lean_ctor_get(x_37, 3);
x_66 = lean_ctor_get(x_37, 4);
x_67 = lean_ctor_get(x_37, 5);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_37);
x_68 = lean_ctor_get(x_38, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_38, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_38, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_38, 4);
lean_inc(x_71);
x_72 = lean_ctor_get(x_38, 5);
lean_inc(x_72);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 x_73 = x_38;
} else {
 lean_dec_ref(x_38);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_39, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_39, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_76 = x_39;
} else {
 lean_dec_ref(x_39);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 3, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set(x_77, 2, x_30);
if (lean_is_scalar(x_73)) {
 x_78 = lean_alloc_ctor(0, 6, 0);
} else {
 x_78 = x_73;
}
lean_ctor_set(x_78, 0, x_68);
lean_ctor_set(x_78, 1, x_69);
lean_ctor_set(x_78, 2, x_77);
lean_ctor_set(x_78, 3, x_70);
lean_ctor_set(x_78, 4, x_71);
lean_ctor_set(x_78, 5, x_72);
x_79 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_63);
lean_ctor_set(x_79, 2, x_64);
lean_ctor_set(x_79, 3, x_65);
lean_ctor_set(x_79, 4, x_66);
lean_ctor_set(x_79, 5, x_67);
lean_ctor_set(x_36, 0, x_79);
return x_35;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_80 = lean_ctor_get(x_36, 1);
lean_inc(x_80);
lean_dec(x_36);
x_81 = lean_ctor_get(x_37, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_37, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_37, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_37, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_37, 5);
lean_inc(x_85);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 x_86 = x_37;
} else {
 lean_dec_ref(x_37);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_38, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_38, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_38, 3);
lean_inc(x_89);
x_90 = lean_ctor_get(x_38, 4);
lean_inc(x_90);
x_91 = lean_ctor_get(x_38, 5);
lean_inc(x_91);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 x_92 = x_38;
} else {
 lean_dec_ref(x_38);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_39, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_39, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_95 = x_39;
} else {
 lean_dec_ref(x_39);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 3, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
lean_ctor_set(x_96, 2, x_30);
if (lean_is_scalar(x_92)) {
 x_97 = lean_alloc_ctor(0, 6, 0);
} else {
 x_97 = x_92;
}
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_88);
lean_ctor_set(x_97, 2, x_96);
lean_ctor_set(x_97, 3, x_89);
lean_ctor_set(x_97, 4, x_90);
lean_ctor_set(x_97, 5, x_91);
if (lean_is_scalar(x_86)) {
 x_98 = lean_alloc_ctor(0, 6, 0);
} else {
 x_98 = x_86;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_81);
lean_ctor_set(x_98, 2, x_82);
lean_ctor_set(x_98, 3, x_83);
lean_ctor_set(x_98, 4, x_84);
lean_ctor_set(x_98, 5, x_85);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_80);
lean_ctor_set(x_35, 1, x_99);
return x_35;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_100 = lean_ctor_get(x_35, 0);
lean_inc(x_100);
lean_dec(x_35);
x_101 = lean_ctor_get(x_36, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_102 = x_36;
} else {
 lean_dec_ref(x_36);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_37, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_37, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_37, 3);
lean_inc(x_105);
x_106 = lean_ctor_get(x_37, 4);
lean_inc(x_106);
x_107 = lean_ctor_get(x_37, 5);
lean_inc(x_107);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 x_108 = x_37;
} else {
 lean_dec_ref(x_37);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_38, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_38, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_38, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_38, 4);
lean_inc(x_112);
x_113 = lean_ctor_get(x_38, 5);
lean_inc(x_113);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 x_114 = x_38;
} else {
 lean_dec_ref(x_38);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_39, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_39, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_117 = x_39;
} else {
 lean_dec_ref(x_39);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 3, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
lean_ctor_set(x_118, 2, x_30);
if (lean_is_scalar(x_114)) {
 x_119 = lean_alloc_ctor(0, 6, 0);
} else {
 x_119 = x_114;
}
lean_ctor_set(x_119, 0, x_109);
lean_ctor_set(x_119, 1, x_110);
lean_ctor_set(x_119, 2, x_118);
lean_ctor_set(x_119, 3, x_111);
lean_ctor_set(x_119, 4, x_112);
lean_ctor_set(x_119, 5, x_113);
if (lean_is_scalar(x_108)) {
 x_120 = lean_alloc_ctor(0, 6, 0);
} else {
 x_120 = x_108;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_103);
lean_ctor_set(x_120, 2, x_104);
lean_ctor_set(x_120, 3, x_105);
lean_ctor_set(x_120, 4, x_106);
lean_ctor_set(x_120, 5, x_107);
if (lean_is_scalar(x_102)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_102;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_101);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_100);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
else
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_35);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_124 = lean_ctor_get(x_35, 1);
x_125 = l_Lean_Elab_Tactic_restore(x_124, x_34);
lean_dec(x_34);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 2);
lean_inc(x_128);
x_129 = !lean_is_exclusive(x_126);
if (x_129 == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_126, 0);
lean_dec(x_130);
x_131 = !lean_is_exclusive(x_127);
if (x_131 == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_127, 2);
lean_dec(x_132);
x_133 = !lean_is_exclusive(x_128);
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_128, 2);
lean_dec(x_134);
lean_ctor_set(x_128, 2, x_30);
x_135 = !lean_is_exclusive(x_33);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_33, 0);
lean_dec(x_136);
lean_ctor_set(x_33, 0, x_126);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_33, 1);
lean_inc(x_137);
lean_dec(x_33);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_126);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_35, 1, x_138);
return x_35;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_139 = lean_ctor_get(x_128, 0);
x_140 = lean_ctor_get(x_128, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_128);
x_141 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_141, 2, x_30);
lean_ctor_set(x_127, 2, x_141);
x_142 = lean_ctor_get(x_33, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_143 = x_33;
} else {
 lean_dec_ref(x_33);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_126);
lean_ctor_set(x_144, 1, x_142);
lean_ctor_set(x_35, 1, x_144);
return x_35;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_145 = lean_ctor_get(x_127, 0);
x_146 = lean_ctor_get(x_127, 1);
x_147 = lean_ctor_get(x_127, 3);
x_148 = lean_ctor_get(x_127, 4);
x_149 = lean_ctor_get(x_127, 5);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_127);
x_150 = lean_ctor_get(x_128, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_128, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 x_152 = x_128;
} else {
 lean_dec_ref(x_128);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(0, 3, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
lean_ctor_set(x_153, 2, x_30);
x_154 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_154, 0, x_145);
lean_ctor_set(x_154, 1, x_146);
lean_ctor_set(x_154, 2, x_153);
lean_ctor_set(x_154, 3, x_147);
lean_ctor_set(x_154, 4, x_148);
lean_ctor_set(x_154, 5, x_149);
lean_ctor_set(x_126, 0, x_154);
x_155 = lean_ctor_get(x_33, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_156 = x_33;
} else {
 lean_dec_ref(x_33);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_126);
lean_ctor_set(x_157, 1, x_155);
lean_ctor_set(x_35, 1, x_157);
return x_35;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_158 = lean_ctor_get(x_126, 1);
x_159 = lean_ctor_get(x_126, 2);
x_160 = lean_ctor_get(x_126, 3);
x_161 = lean_ctor_get(x_126, 4);
x_162 = lean_ctor_get(x_126, 5);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_126);
x_163 = lean_ctor_get(x_127, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_127, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_127, 3);
lean_inc(x_165);
x_166 = lean_ctor_get(x_127, 4);
lean_inc(x_166);
x_167 = lean_ctor_get(x_127, 5);
lean_inc(x_167);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 lean_ctor_release(x_127, 4);
 lean_ctor_release(x_127, 5);
 x_168 = x_127;
} else {
 lean_dec_ref(x_127);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_128, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_128, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 x_171 = x_128;
} else {
 lean_dec_ref(x_128);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(0, 3, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
lean_ctor_set(x_172, 2, x_30);
if (lean_is_scalar(x_168)) {
 x_173 = lean_alloc_ctor(0, 6, 0);
} else {
 x_173 = x_168;
}
lean_ctor_set(x_173, 0, x_163);
lean_ctor_set(x_173, 1, x_164);
lean_ctor_set(x_173, 2, x_172);
lean_ctor_set(x_173, 3, x_165);
lean_ctor_set(x_173, 4, x_166);
lean_ctor_set(x_173, 5, x_167);
x_174 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_158);
lean_ctor_set(x_174, 2, x_159);
lean_ctor_set(x_174, 3, x_160);
lean_ctor_set(x_174, 4, x_161);
lean_ctor_set(x_174, 5, x_162);
x_175 = lean_ctor_get(x_33, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_176 = x_33;
} else {
 lean_dec_ref(x_33);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
lean_ctor_set(x_35, 1, x_177);
return x_35;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_178 = lean_ctor_get(x_35, 0);
x_179 = lean_ctor_get(x_35, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_35);
x_180 = l_Lean_Elab_Tactic_restore(x_179, x_34);
lean_dec(x_34);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec(x_180);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_182, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_181, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_181, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_181, 3);
lean_inc(x_186);
x_187 = lean_ctor_get(x_181, 4);
lean_inc(x_187);
x_188 = lean_ctor_get(x_181, 5);
lean_inc(x_188);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 lean_ctor_release(x_181, 2);
 lean_ctor_release(x_181, 3);
 lean_ctor_release(x_181, 4);
 lean_ctor_release(x_181, 5);
 x_189 = x_181;
} else {
 lean_dec_ref(x_181);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get(x_182, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_182, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_182, 3);
lean_inc(x_192);
x_193 = lean_ctor_get(x_182, 4);
lean_inc(x_193);
x_194 = lean_ctor_get(x_182, 5);
lean_inc(x_194);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 lean_ctor_release(x_182, 2);
 lean_ctor_release(x_182, 3);
 lean_ctor_release(x_182, 4);
 lean_ctor_release(x_182, 5);
 x_195 = x_182;
} else {
 lean_dec_ref(x_182);
 x_195 = lean_box(0);
}
x_196 = lean_ctor_get(x_183, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_183, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 lean_ctor_release(x_183, 2);
 x_198 = x_183;
} else {
 lean_dec_ref(x_183);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(0, 3, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
lean_ctor_set(x_199, 2, x_30);
if (lean_is_scalar(x_195)) {
 x_200 = lean_alloc_ctor(0, 6, 0);
} else {
 x_200 = x_195;
}
lean_ctor_set(x_200, 0, x_190);
lean_ctor_set(x_200, 1, x_191);
lean_ctor_set(x_200, 2, x_199);
lean_ctor_set(x_200, 3, x_192);
lean_ctor_set(x_200, 4, x_193);
lean_ctor_set(x_200, 5, x_194);
if (lean_is_scalar(x_189)) {
 x_201 = lean_alloc_ctor(0, 6, 0);
} else {
 x_201 = x_189;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_184);
lean_ctor_set(x_201, 2, x_185);
lean_ctor_set(x_201, 3, x_186);
lean_ctor_set(x_201, 4, x_187);
lean_ctor_set(x_201, 5, x_188);
x_202 = lean_ctor_get(x_33, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_203 = x_33;
} else {
 lean_dec_ref(x_33);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_178);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
uint8_t x_206; 
lean_dec(x_30);
lean_dec(x_22);
lean_dec(x_2);
x_206 = !lean_is_exclusive(x_32);
if (x_206 == 0)
{
return x_32;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_32, 0);
x_208 = lean_ctor_get(x_32, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_32);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; 
x_210 = lean_ctor_get(x_7, 0);
x_211 = lean_ctor_get(x_7, 2);
x_212 = lean_ctor_get(x_7, 3);
x_213 = lean_ctor_get(x_7, 4);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_7);
x_214 = lean_ctor_get(x_8, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_8, 4);
lean_inc(x_215);
x_216 = lean_array_get_size(x_211);
x_217 = lean_array_get_size(x_215);
x_218 = lean_nat_dec_eq(x_216, x_217);
lean_dec(x_217);
lean_dec(x_216);
lean_inc(x_215);
x_219 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_219, 0, x_210);
lean_ctor_set(x_219, 1, x_214);
lean_ctor_set(x_219, 2, x_215);
lean_ctor_set(x_219, 3, x_212);
lean_ctor_set(x_219, 4, x_213);
lean_ctor_set(x_6, 0, x_219);
x_220 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_220, 0, x_6);
lean_ctor_set(x_220, 1, x_10);
lean_ctor_set(x_220, 2, x_11);
if (x_218 == 0)
{
lean_object* x_221; 
lean_dec(x_215);
lean_dec(x_211);
lean_dec(x_8);
lean_dec(x_3);
x_221 = lean_apply_2(x_2, x_220, x_9);
return x_221;
}
else
{
lean_object* x_222; uint8_t x_223; 
x_222 = lean_unsigned_to_nat(0u);
x_223 = l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1(x_3, x_8, lean_box(0), x_211, x_215, x_222);
lean_dec(x_215);
lean_dec(x_211);
lean_dec(x_8);
lean_dec(x_3);
if (x_223 == 0)
{
lean_object* x_224; 
x_224 = lean_apply_2(x_2, x_220, x_9);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_225 = lean_ctor_get(x_9, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_dec(x_225);
x_227 = lean_ctor_get(x_226, 2);
lean_inc(x_227);
lean_dec(x_226);
x_228 = lean_ctor_get(x_227, 2);
lean_inc(x_228);
lean_dec(x_227);
x_229 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_220);
x_230 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_229, x_220, x_9);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_232 = l_Lean_Elab_Tactic_save(x_231);
lean_inc(x_231);
x_233 = lean_apply_2(x_2, x_220, x_231);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_232);
lean_dec(x_231);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_236, 2);
lean_inc(x_237);
x_238 = lean_ctor_get(x_233, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_239 = x_233;
} else {
 lean_dec_ref(x_233);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_234, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_241 = x_234;
} else {
 lean_dec_ref(x_234);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_235, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_235, 2);
lean_inc(x_243);
x_244 = lean_ctor_get(x_235, 3);
lean_inc(x_244);
x_245 = lean_ctor_get(x_235, 4);
lean_inc(x_245);
x_246 = lean_ctor_get(x_235, 5);
lean_inc(x_246);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 lean_ctor_release(x_235, 4);
 lean_ctor_release(x_235, 5);
 x_247 = x_235;
} else {
 lean_dec_ref(x_235);
 x_247 = lean_box(0);
}
x_248 = lean_ctor_get(x_236, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_236, 1);
lean_inc(x_249);
x_250 = lean_ctor_get(x_236, 3);
lean_inc(x_250);
x_251 = lean_ctor_get(x_236, 4);
lean_inc(x_251);
x_252 = lean_ctor_get(x_236, 5);
lean_inc(x_252);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 lean_ctor_release(x_236, 2);
 lean_ctor_release(x_236, 3);
 lean_ctor_release(x_236, 4);
 lean_ctor_release(x_236, 5);
 x_253 = x_236;
} else {
 lean_dec_ref(x_236);
 x_253 = lean_box(0);
}
x_254 = lean_ctor_get(x_237, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_237, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 lean_ctor_release(x_237, 2);
 x_256 = x_237;
} else {
 lean_dec_ref(x_237);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(0, 3, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
lean_ctor_set(x_257, 2, x_228);
if (lean_is_scalar(x_253)) {
 x_258 = lean_alloc_ctor(0, 6, 0);
} else {
 x_258 = x_253;
}
lean_ctor_set(x_258, 0, x_248);
lean_ctor_set(x_258, 1, x_249);
lean_ctor_set(x_258, 2, x_257);
lean_ctor_set(x_258, 3, x_250);
lean_ctor_set(x_258, 4, x_251);
lean_ctor_set(x_258, 5, x_252);
if (lean_is_scalar(x_247)) {
 x_259 = lean_alloc_ctor(0, 6, 0);
} else {
 x_259 = x_247;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_242);
lean_ctor_set(x_259, 2, x_243);
lean_ctor_set(x_259, 3, x_244);
lean_ctor_set(x_259, 4, x_245);
lean_ctor_set(x_259, 5, x_246);
if (lean_is_scalar(x_241)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_241;
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_240);
if (lean_is_scalar(x_239)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_239;
}
lean_ctor_set(x_261, 0, x_238);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_262 = lean_ctor_get(x_233, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_233, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_264 = x_233;
} else {
 lean_dec_ref(x_233);
 x_264 = lean_box(0);
}
x_265 = l_Lean_Elab_Tactic_restore(x_263, x_232);
lean_dec(x_232);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
lean_dec(x_265);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_267, 2);
lean_inc(x_268);
x_269 = lean_ctor_get(x_266, 1);
lean_inc(x_269);
x_270 = lean_ctor_get(x_266, 2);
lean_inc(x_270);
x_271 = lean_ctor_get(x_266, 3);
lean_inc(x_271);
x_272 = lean_ctor_get(x_266, 4);
lean_inc(x_272);
x_273 = lean_ctor_get(x_266, 5);
lean_inc(x_273);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 lean_ctor_release(x_266, 2);
 lean_ctor_release(x_266, 3);
 lean_ctor_release(x_266, 4);
 lean_ctor_release(x_266, 5);
 x_274 = x_266;
} else {
 lean_dec_ref(x_266);
 x_274 = lean_box(0);
}
x_275 = lean_ctor_get(x_267, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_267, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_267, 3);
lean_inc(x_277);
x_278 = lean_ctor_get(x_267, 4);
lean_inc(x_278);
x_279 = lean_ctor_get(x_267, 5);
lean_inc(x_279);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 lean_ctor_release(x_267, 2);
 lean_ctor_release(x_267, 3);
 lean_ctor_release(x_267, 4);
 lean_ctor_release(x_267, 5);
 x_280 = x_267;
} else {
 lean_dec_ref(x_267);
 x_280 = lean_box(0);
}
x_281 = lean_ctor_get(x_268, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_268, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 lean_ctor_release(x_268, 2);
 x_283 = x_268;
} else {
 lean_dec_ref(x_268);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(0, 3, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
lean_ctor_set(x_284, 2, x_228);
if (lean_is_scalar(x_280)) {
 x_285 = lean_alloc_ctor(0, 6, 0);
} else {
 x_285 = x_280;
}
lean_ctor_set(x_285, 0, x_275);
lean_ctor_set(x_285, 1, x_276);
lean_ctor_set(x_285, 2, x_284);
lean_ctor_set(x_285, 3, x_277);
lean_ctor_set(x_285, 4, x_278);
lean_ctor_set(x_285, 5, x_279);
if (lean_is_scalar(x_274)) {
 x_286 = lean_alloc_ctor(0, 6, 0);
} else {
 x_286 = x_274;
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_269);
lean_ctor_set(x_286, 2, x_270);
lean_ctor_set(x_286, 3, x_271);
lean_ctor_set(x_286, 4, x_272);
lean_ctor_set(x_286, 5, x_273);
x_287 = lean_ctor_get(x_231, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_288 = x_231;
} else {
 lean_dec_ref(x_231);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
if (lean_is_scalar(x_264)) {
 x_290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_290 = x_264;
}
lean_ctor_set(x_290, 0, x_262);
lean_ctor_set(x_290, 1, x_289);
return x_290;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_228);
lean_dec(x_220);
lean_dec(x_2);
x_291 = lean_ctor_get(x_230, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_230, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_293 = x_230;
} else {
 lean_dec_ref(x_230);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
}
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_295 = lean_ctor_get(x_6, 1);
x_296 = lean_ctor_get(x_6, 2);
x_297 = lean_ctor_get(x_6, 3);
x_298 = lean_ctor_get(x_6, 4);
x_299 = lean_ctor_get(x_6, 5);
x_300 = lean_ctor_get(x_6, 6);
x_301 = lean_ctor_get(x_6, 7);
x_302 = lean_ctor_get(x_6, 8);
x_303 = lean_ctor_get(x_6, 9);
x_304 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_305 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
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
x_317 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_295);
lean_ctor_set(x_317, 2, x_296);
lean_ctor_set(x_317, 3, x_297);
lean_ctor_set(x_317, 4, x_298);
lean_ctor_set(x_317, 5, x_299);
lean_ctor_set(x_317, 6, x_300);
lean_ctor_set(x_317, 7, x_301);
lean_ctor_set(x_317, 8, x_302);
lean_ctor_set(x_317, 9, x_303);
lean_ctor_set_uint8(x_317, sizeof(void*)*10, x_304);
lean_ctor_set_uint8(x_317, sizeof(void*)*10 + 1, x_305);
x_318 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_10);
lean_ctor_set(x_318, 2, x_11);
if (x_315 == 0)
{
lean_object* x_319; 
lean_dec(x_312);
lean_dec(x_307);
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
x_322 = lean_apply_2(x_2, x_318, x_9);
return x_322;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
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
x_327 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_318);
x_328 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_327, x_318, x_9);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
lean_dec(x_328);
x_330 = l_Lean_Elab_Tactic_save(x_329);
lean_inc(x_329);
x_331 = lean_apply_2(x_2, x_318, x_329);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_330);
lean_dec(x_329);
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_334, 2);
lean_inc(x_335);
x_336 = lean_ctor_get(x_331, 0);
lean_inc(x_336);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_337 = x_331;
} else {
 lean_dec_ref(x_331);
 x_337 = lean_box(0);
}
x_338 = lean_ctor_get(x_332, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 lean_ctor_release(x_332, 1);
 x_339 = x_332;
} else {
 lean_dec_ref(x_332);
 x_339 = lean_box(0);
}
x_340 = lean_ctor_get(x_333, 1);
lean_inc(x_340);
x_341 = lean_ctor_get(x_333, 2);
lean_inc(x_341);
x_342 = lean_ctor_get(x_333, 3);
lean_inc(x_342);
x_343 = lean_ctor_get(x_333, 4);
lean_inc(x_343);
x_344 = lean_ctor_get(x_333, 5);
lean_inc(x_344);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 lean_ctor_release(x_333, 2);
 lean_ctor_release(x_333, 3);
 lean_ctor_release(x_333, 4);
 lean_ctor_release(x_333, 5);
 x_345 = x_333;
} else {
 lean_dec_ref(x_333);
 x_345 = lean_box(0);
}
x_346 = lean_ctor_get(x_334, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_334, 1);
lean_inc(x_347);
x_348 = lean_ctor_get(x_334, 3);
lean_inc(x_348);
x_349 = lean_ctor_get(x_334, 4);
lean_inc(x_349);
x_350 = lean_ctor_get(x_334, 5);
lean_inc(x_350);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 lean_ctor_release(x_334, 2);
 lean_ctor_release(x_334, 3);
 lean_ctor_release(x_334, 4);
 lean_ctor_release(x_334, 5);
 x_351 = x_334;
} else {
 lean_dec_ref(x_334);
 x_351 = lean_box(0);
}
x_352 = lean_ctor_get(x_335, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_335, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 lean_ctor_release(x_335, 2);
 x_354 = x_335;
} else {
 lean_dec_ref(x_335);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(0, 3, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_352);
lean_ctor_set(x_355, 1, x_353);
lean_ctor_set(x_355, 2, x_326);
if (lean_is_scalar(x_351)) {
 x_356 = lean_alloc_ctor(0, 6, 0);
} else {
 x_356 = x_351;
}
lean_ctor_set(x_356, 0, x_346);
lean_ctor_set(x_356, 1, x_347);
lean_ctor_set(x_356, 2, x_355);
lean_ctor_set(x_356, 3, x_348);
lean_ctor_set(x_356, 4, x_349);
lean_ctor_set(x_356, 5, x_350);
if (lean_is_scalar(x_345)) {
 x_357 = lean_alloc_ctor(0, 6, 0);
} else {
 x_357 = x_345;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_340);
lean_ctor_set(x_357, 2, x_341);
lean_ctor_set(x_357, 3, x_342);
lean_ctor_set(x_357, 4, x_343);
lean_ctor_set(x_357, 5, x_344);
if (lean_is_scalar(x_339)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_339;
}
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_338);
if (lean_is_scalar(x_337)) {
 x_359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_359 = x_337;
}
lean_ctor_set(x_359, 0, x_336);
lean_ctor_set(x_359, 1, x_358);
return x_359;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_360 = lean_ctor_get(x_331, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_331, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_362 = x_331;
} else {
 lean_dec_ref(x_331);
 x_362 = lean_box(0);
}
x_363 = l_Lean_Elab_Tactic_restore(x_361, x_330);
lean_dec(x_330);
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
lean_dec(x_363);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_365, 2);
lean_inc(x_366);
x_367 = lean_ctor_get(x_364, 1);
lean_inc(x_367);
x_368 = lean_ctor_get(x_364, 2);
lean_inc(x_368);
x_369 = lean_ctor_get(x_364, 3);
lean_inc(x_369);
x_370 = lean_ctor_get(x_364, 4);
lean_inc(x_370);
x_371 = lean_ctor_get(x_364, 5);
lean_inc(x_371);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 lean_ctor_release(x_364, 2);
 lean_ctor_release(x_364, 3);
 lean_ctor_release(x_364, 4);
 lean_ctor_release(x_364, 5);
 x_372 = x_364;
} else {
 lean_dec_ref(x_364);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_365, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_365, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_365, 3);
lean_inc(x_375);
x_376 = lean_ctor_get(x_365, 4);
lean_inc(x_376);
x_377 = lean_ctor_get(x_365, 5);
lean_inc(x_377);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 lean_ctor_release(x_365, 2);
 lean_ctor_release(x_365, 3);
 lean_ctor_release(x_365, 4);
 lean_ctor_release(x_365, 5);
 x_378 = x_365;
} else {
 lean_dec_ref(x_365);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_366, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_366, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 lean_ctor_release(x_366, 2);
 x_381 = x_366;
} else {
 lean_dec_ref(x_366);
 x_381 = lean_box(0);
}
if (lean_is_scalar(x_381)) {
 x_382 = lean_alloc_ctor(0, 3, 0);
} else {
 x_382 = x_381;
}
lean_ctor_set(x_382, 0, x_379);
lean_ctor_set(x_382, 1, x_380);
lean_ctor_set(x_382, 2, x_326);
if (lean_is_scalar(x_378)) {
 x_383 = lean_alloc_ctor(0, 6, 0);
} else {
 x_383 = x_378;
}
lean_ctor_set(x_383, 0, x_373);
lean_ctor_set(x_383, 1, x_374);
lean_ctor_set(x_383, 2, x_382);
lean_ctor_set(x_383, 3, x_375);
lean_ctor_set(x_383, 4, x_376);
lean_ctor_set(x_383, 5, x_377);
if (lean_is_scalar(x_372)) {
 x_384 = lean_alloc_ctor(0, 6, 0);
} else {
 x_384 = x_372;
}
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_367);
lean_ctor_set(x_384, 2, x_368);
lean_ctor_set(x_384, 3, x_369);
lean_ctor_set(x_384, 4, x_370);
lean_ctor_set(x_384, 5, x_371);
x_385 = lean_ctor_get(x_329, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_386 = x_329;
} else {
 lean_dec_ref(x_329);
 x_386 = lean_box(0);
}
if (lean_is_scalar(x_386)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_386;
}
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_385);
if (lean_is_scalar(x_362)) {
 x_388 = lean_alloc_ctor(1, 2, 0);
} else {
 x_388 = x_362;
}
lean_ctor_set(x_388, 0, x_360);
lean_ctor_set(x_388, 1, x_387);
return x_388;
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_326);
lean_dec(x_318);
lean_dec(x_2);
x_389 = lean_ctor_get(x_328, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_328, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_391 = x_328;
} else {
 lean_dec_ref(x_328);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(1, 2, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_390);
return x_392;
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
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_Tactic_getMainGoal___closed__3;
x_8 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_7, x_2, x_6);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
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
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Elab_Tactic_instantiateMVars(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_Expr_hasMVar(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_box(0);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_5);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_7);
x_12 = l_Lean_indentExpr(x_11);
x_13 = l_Lean_Elab_Tactic_ensureHasNoMVars___closed__3;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_14, x_3, x_8);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = l_Lean_Expr_hasMVar(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_22 = l_Lean_indentExpr(x_21);
x_23 = l_Lean_Elab_Tactic_ensureHasNoMVars___closed__3;
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_24, x_3, x_17);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
return x_5;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_5, 0);
x_28 = lean_ctor_get(x_5, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_5);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_List_append___rarg(x_2, x_1);
x_6 = l_Lean_Elab_Tactic_setGoals(x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
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
lean_inc(x_8);
x_10 = lean_apply_1(x_2, x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 4, 1);
lean_closure_set(x_12, 0, x_9);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_8, x_13, x_3, x_7);
lean_dec(x_8);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_liftMetaTactic___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_done(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_List_isEmpty___rarg(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_free_object(x_4);
x_9 = l_Lean_Elab_Tactic_reportUnsolvedGoals(x_1, x_6, x_2, x_7);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = l_List_isEmpty___rarg(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_reportUnsolvedGoals(x_1, x_11, x_2, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_focus___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
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
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Elab_Tactic_setGoals(x_11, x_3, x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_3);
x_14 = lean_apply_2(x_2, x_3, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_3);
x_17 = l_Lean_Elab_Tactic_done(x_1, x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Elab_Tactic_setGoals(x_9, x_3, x_18);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_15);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
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
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_5);
if (x_32 == 0)
{
return x_5;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_5, 0);
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_5);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_focus(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_focus___rarg), 4, 0);
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
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalSeq");
return x_1;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSeq___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Tactic_seq___elambda__1___closed__3;
x_3 = l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__2;
x_4 = l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__3;
x_5 = l_Lean_Elab_Tactic_addBuiltinTactic(x_2, x_3, x_4, x_1);
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
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalSkip");
return x_1;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSkip___boxed), 2, 0);
return x_1;
}
}
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Tactic_skip___elambda__1___closed__2;
x_3 = l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip___closed__2;
x_4 = l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip___closed__3;
x_5 = l_Lean_Elab_Tactic_addBuiltinTactic(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Tactic_evalTraceState___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_getPos(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Tactic_evalTraceState___spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 3);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lean_FileMap_toPosition(x_7, x_9);
lean_dec(x_9);
lean_dec(x_7);
x_11 = l_Lean_Elab_Tactic_addContext(x_1, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
x_15 = l_String_splitAux___main___closed__1;
x_16 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_16, 4, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_2);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_box(0);
x_20 = l_String_splitAux___main___closed__1;
x_21 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_10);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set(x_21, 3, x_20);
lean_ctor_set(x_21, 4, x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_8);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_4, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_3, 0);
x_31 = l_Lean_FileMap_toPosition(x_28, x_30);
lean_dec(x_28);
x_32 = l_Lean_Elab_Tactic_addContext(x_1, x_4, x_5);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_box(0);
x_36 = l_String_splitAux___main___closed__1;
x_37 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_31);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set(x_37, 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*5, x_2);
lean_ctor_set(x_32, 0, x_37);
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_box(0);
x_41 = l_String_splitAux___main___closed__1;
x_42 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_42, 0, x_29);
lean_ctor_set(x_42, 1, x_31);
lean_ctor_set(x_42, 2, x_40);
lean_ctor_set(x_42, 3, x_41);
lean_ctor_set(x_42, 4, x_38);
lean_ctor_set_uint8(x_42, sizeof(void*)*5, x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_31);
lean_dec(x_29);
x_44 = !lean_is_exclusive(x_32);
if (x_44 == 0)
{
return x_32;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_32, 0);
x_46 = lean_ctor_get(x_32, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_32);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalTraceState___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Tactic_evalTraceState___spec__4(x_3, x_2, x_6, x_4, x_5);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
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
x_14 = lean_ctor_get(x_8, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 2);
x_17 = l_PersistentArray_push___rarg(x_16, x_11);
lean_ctor_set(x_9, 2, x_17);
x_18 = lean_box(0);
lean_ctor_set(x_7, 0, x_18);
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
x_21 = lean_ctor_get(x_9, 2);
x_22 = lean_ctor_get(x_9, 3);
x_23 = lean_ctor_get(x_9, 4);
x_24 = lean_ctor_get(x_9, 5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_25 = l_PersistentArray_push___rarg(x_21, x_11);
x_26 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set(x_26, 4, x_23);
lean_ctor_set(x_26, 5, x_24);
lean_ctor_set(x_8, 0, x_26);
x_27 = lean_box(0);
lean_ctor_set(x_7, 0, x_27);
return x_7;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_dec(x_8);
x_29 = lean_ctor_get(x_9, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_9, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_9, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_9, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_9, 5);
lean_inc(x_34);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 lean_ctor_release(x_9, 4);
 lean_ctor_release(x_9, 5);
 x_35 = x_9;
} else {
 lean_dec_ref(x_9);
 x_35 = lean_box(0);
}
x_36 = l_PersistentArray_push___rarg(x_31, x_11);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 6, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_33);
lean_ctor_set(x_37, 5, x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_28);
x_39 = lean_box(0);
lean_ctor_set(x_7, 1, x_38);
lean_ctor_set(x_7, 0, x_39);
return x_7;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_40 = lean_ctor_get(x_7, 0);
lean_inc(x_40);
lean_dec(x_7);
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_42 = x_8;
} else {
 lean_dec_ref(x_8);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_9, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_9, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_9, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_9, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_9, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_9, 5);
lean_inc(x_48);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 lean_ctor_release(x_9, 4);
 lean_ctor_release(x_9, 5);
 x_49 = x_9;
} else {
 lean_dec_ref(x_9);
 x_49 = lean_box(0);
}
x_50 = l_PersistentArray_push___rarg(x_45, x_40);
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
if (lean_is_scalar(x_42)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_42;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_7);
if (x_55 == 0)
{
return x_7;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_7, 0);
x_57 = lean_ctor_get(x_7, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_7);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTraceState___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_getPos___at_Lean_Elab_Tactic_evalTraceState___spec__2(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalTraceState___spec__3(x_7, x_2, x_3, x_4, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_Tactic_evalTraceState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_goalsToMessageData(x_5);
x_8 = 0;
x_9 = l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTraceState___spec__1(x_1, x_8, x_7, x_2, x_6);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Tactic_evalTraceState___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getPos___at_Lean_Elab_Tactic_evalTraceState___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Tactic_evalTraceState___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Tactic_evalTraceState___spec__4(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_3);
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
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTraceState___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTraceState___spec__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Tactic_evalTraceState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalTraceState(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalTraceState");
return x_1;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTraceState___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Tactic_traceState___elambda__1___closed__2;
x_3 = l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__2;
x_4 = l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__3;
x_5 = l_Lean_Elab_Tactic_addBuiltinTactic(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalAssumption___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* _init_l_Lean_Elab_Tactic_evalAssumption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalAssumption___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_evalAssumption(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3);
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
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_assumption___boxed), 3, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = l_Lean_Elab_Tactic_evalAssumption___closed__1;
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 4, 1);
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
lean_object* l_Lean_Elab_Tactic_evalAssumption___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalAssumption___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalAssumption");
return x_1;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalAssumption), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Tactic_assumption___elambda__1___closed__2;
x_3 = l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__2;
x_4 = l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__3;
x_5 = l_Lean_Elab_Tactic_addBuiltinTactic(x_2, x_3, x_4, x_1);
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
lean_object* x_4; 
x_4 = l_Lean_Meta_intro1(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
else
{
uint8_t x_16; 
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
lean_object* l_Lean_Elab_Tactic_evalIntro(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_nullKind___closed__2;
lean_inc(x_13);
x_15 = l_Lean_Syntax_isOfKind(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_39; 
x_39 = lean_box(0);
x_16 = x_39;
goto block_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = l_Lean_Syntax_getArgs(x_13);
x_41 = lean_array_get_size(x_40);
lean_dec(x_40);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_eq(x_41, x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_box(0);
x_16 = x_44;
goto block_38;
}
else
{
lean_object* x_45; 
lean_dec(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_45 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
lean_inc(x_48);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntro___lambda__2___boxed), 3, 1);
lean_closure_set(x_50, 0, x_48);
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_51, 0, x_1);
lean_closure_set(x_51, 1, x_50);
x_52 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 4, 1);
lean_closure_set(x_52, 0, x_49);
x_53 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_53, 0, x_51);
lean_closure_set(x_53, 1, x_52);
x_54 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_48, x_53, x_2, x_47);
lean_dec(x_48);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_2);
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
block_38:
{
lean_dec(x_16);
if (x_15 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_1);
x_17 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Syntax_getArgs(x_13);
x_19 = lean_array_get_size(x_18);
lean_dec(x_18);
x_20 = lean_nat_dec_eq(x_19, x_12);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_1);
x_21 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_13, x_22);
lean_dec(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_24 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
lean_inc(x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntro___lambda__1___boxed), 4, 2);
lean_closure_set(x_29, 0, x_23);
lean_closure_set(x_29, 1, x_27);
x_30 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 4, 1);
lean_closure_set(x_31, 0, x_28);
x_32 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_32, 0, x_30);
lean_closure_set(x_32, 1, x_31);
x_33 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_27, x_32, x_2, x_26);
lean_dec(x_27);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_23);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_24);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
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
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalIntro");
return x_1;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntro), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
x_3 = l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__2;
x_4 = l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__3;
x_5 = l_Lean_Elab_Tactic_addBuiltinTactic(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_3__getIntrosSize___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l___private_Init_Lean_Elab_Tactic_Basic_3__getIntrosSize___main(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
return x_5;
}
case 8:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 3);
x_7 = l___private_Init_Lean_Elab_Tactic_Basic_3__getIntrosSize___main(x_6);
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
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_3__getIntrosSize___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Tactic_Basic_3__getIntrosSize___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_3__getIntrosSize(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Tactic_Basic_3__getIntrosSize___main(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_3__getIntrosSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Tactic_Basic_3__getIntrosSize(x_1);
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
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean_box(0);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
x_11 = l_Lean_Syntax_getId(x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
lean_dec(x_7);
x_15 = lean_array_fset(x_10, x_1, x_14);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalIntros___spec__1(x_6, x_1);
x_8 = l_Array_toList___rarg(x_7);
lean_dec(x_7);
x_9 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2, x_5, x_8, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
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
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
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
x_10 = l___private_Init_Lean_Elab_Tactic_Basic_3__getIntrosSize___main(x_8);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1, x_10, x_11, x_2, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_11);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
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
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_4);
if (x_26 == 0)
{
return x_4;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalIntros(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_31; uint8_t x_32; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_31 = l_Lean_nullKind___closed__2;
lean_inc(x_13);
x_32 = l_Lean_Syntax_isOfKind(x_13, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_box(0);
x_14 = x_33;
goto block_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = l_Lean_Syntax_getArgs(x_13);
x_35 = lean_array_get_size(x_34);
lean_dec(x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_eq(x_35, x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_box(0);
x_14 = x_38;
goto block_30;
}
else
{
lean_object* x_39; 
lean_dec(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_39 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
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
lean_inc(x_42);
x_44 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntros___lambda__2___boxed), 3, 1);
lean_closure_set(x_44, 0, x_42);
x_45 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_45, 0, x_1);
lean_closure_set(x_45, 1, x_44);
x_46 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 4, 1);
lean_closure_set(x_46, 0, x_43);
x_47 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_47, 0, x_45);
lean_closure_set(x_47, 1, x_46);
x_48 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_42, x_47, x_2, x_41);
lean_dec(x_42);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
return x_39;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_39);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
block_30:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_14);
x_15 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
lean_inc(x_2);
lean_inc(x_1);
x_16 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
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
lean_inc(x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntros___lambda__1___boxed), 4, 2);
lean_closure_set(x_21, 0, x_15);
lean_closure_set(x_21, 1, x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 4, 1);
lean_closure_set(x_23, 0, x_20);
x_24 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_19, x_24, x_2, x_18);
lean_dec(x_19);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
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
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalIntros");
return x_1;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntros), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
x_3 = l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__2;
x_4 = l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__3;
x_5 = l_Lean_Elab_Tactic_addBuiltinTactic(x_2, x_3, x_4, x_1);
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
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalParen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalParen");
return x_1;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalParen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l___regBuiltinTactic_Lean_Elab_Tactic_evalParen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalParen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalParen___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalParen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Tactic_paren___elambda__1___closed__1;
x_3 = l___regBuiltinTactic_Lean_Elab_Tactic_evalParen___closed__2;
x_4 = l___regBuiltinTactic_Lean_Elab_Tactic_evalParen___closed__3;
x_5 = l_Lean_Elab_Tactic_addBuiltinTactic(x_2, x_3, x_4, x_1);
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
x_7 = l_Lean_Elab_Tactic_focus___rarg(x_1, x_6, x_2, x_3);
return x_7;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalNestedTacticBlock");
return x_1;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalNestedTacticBlock), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Tactic_nestedTacticBlock___elambda__1___closed__2;
x_3 = l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock___closed__2;
x_4 = l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock___closed__3;
x_5 = l_Lean_Elab_Tactic_addBuiltinTactic(x_2, x_3, x_4, x_1);
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
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalNestedTacticBlockCurly");
return x_1;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalNestedTacticBlockCurly), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Tactic_nestedTacticBlockCurly___elambda__1___closed__2;
x_3 = l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__2;
x_4 = l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__3;
x_5 = l_Lean_Elab_Tactic_addBuiltinTactic(x_2, x_3, x_4, x_1);
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
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
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
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Syntax_getId(x_13);
lean_dec(x_13);
lean_inc(x_2);
x_17 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_List_findM_x3f___main___at_Lean_Elab_Tactic_evalCase___spec__1(x_16, x_18, x_2, x_19);
lean_dec(x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_15);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Tactic_evalCase___closed__3;
x_24 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_23, x_2, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__2(x_18, x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Elab_Tactic_setGoals(x_29, x_2, x_25);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_2);
x_32 = l_Lean_Elab_Tactic_evalTactic___main(x_15, x_2, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_2);
x_34 = l_Lean_Elab_Tactic_done(x_1, x_2, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Elab_Tactic_setGoals(x_27, x_2, x_35);
lean_dec(x_2);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_27);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
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
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
return x_32;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_32);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_17);
if (x_45 == 0)
{
return x_17;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_17, 0);
x_47 = lean_ctor_get(x_17, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_17);
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
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalCase___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalCase");
return x_1;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalCase___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l___regBuiltinTactic_Lean_Elab_Tactic_evalCase___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalCase___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCase), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalCase(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
x_3 = l___regBuiltinTactic_Lean_Elab_Tactic_evalCase___closed__2;
x_4 = l___regBuiltinTactic_Lean_Elab_Tactic_evalCase___closed__3;
x_5 = l_Lean_Elab_Tactic_addBuiltinTactic(x_2, x_3, x_4, x_1);
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
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalOrelse");
return x_1;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalOrelse), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Tactic_orelse___elambda__1___closed__1;
x_3 = l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse___closed__2;
x_4 = l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse___closed__3;
x_5 = l_Lean_Elab_Tactic_addBuiltinTactic(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Tactic_Basic_4__regTraceClasses___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__1;
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_4__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elab_Tactic_Basic_4__regTraceClasses___closed__1;
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
lean_object* initialize_Init_Lean_Util_CollectMVars(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Assumption(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Intro(lean_object*);
lean_object* initialize_Init_Lean_Elab_Util(lean_object*);
lean_object* initialize_Init_Lean_Elab_Term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Tactic_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Util_CollectMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Assumption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Intro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Term(lean_io_mk_world());
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
l_PersistentHashMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__3 = _init_l_PersistentHashMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__3();
lean_mark_persistent(l_PersistentHashMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__3);
l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__1 = _init_l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__1);
l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__2 = _init_l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__2();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__2);
l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1 = _init_l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1);
res = l_Lean_Elab_Tactic_mkBuiltinTacticTable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_builtinTacticTable = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_builtinTacticTable);
lean_dec_ref(res);
l_Lean_Elab_Tactic_addBuiltinTactic___closed__1 = _init_l_Lean_Elab_Tactic_addBuiltinTactic___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_addBuiltinTactic___closed__1);
l_Lean_Elab_Tactic_declareBuiltinTactic___closed__1 = _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_declareBuiltinTactic___closed__1);
l_Lean_Elab_Tactic_declareBuiltinTactic___closed__2 = _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_declareBuiltinTactic___closed__2);
l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3 = _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3);
l_Lean_Elab_Tactic_declareBuiltinTactic___closed__4 = _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_declareBuiltinTactic___closed__4);
l_Lean_Elab_Tactic_declareBuiltinTactic___closed__5 = _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_declareBuiltinTactic___closed__5);
l_Lean_Elab_Tactic_declareBuiltinTactic___closed__6 = _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_declareBuiltinTactic___closed__6);
l_Lean_Elab_Tactic_declareBuiltinTactic___closed__7 = _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_declareBuiltinTactic___closed__7);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__1);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__2);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__3);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__4);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__1 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__1);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__2 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__2);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__3 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__3);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__4 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__4);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__5 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__5);
res = l_Lean_Elab_Tactic_registerBuiltinTacticAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__1 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__1);
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
l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__1 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__1();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__2 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__2();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__2);
l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__3 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__3();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__3);
res = l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip___closed__1 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip___closed__1();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip___closed__2 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip___closed__2();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip___closed__2);
l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip___closed__3 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip___closed__3();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip___closed__3);
res = l___regBuiltinTactic_Lean_Elab_Tactic_evalSkip(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__1 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__1();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__2 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__2();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__2);
l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__3 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__3();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__3);
res = l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalAssumption___closed__1 = _init_l_Lean_Elab_Tactic_evalAssumption___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalAssumption___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__1 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__1();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__2 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__2();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__2);
l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__3 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__3();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__3);
res = l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__1 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__1();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__2 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__2();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__2);
l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__3 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__3();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__3);
res = l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__1 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__1();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__2 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__2();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__2);
l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__3 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__3();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__3);
res = l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTactic_Lean_Elab_Tactic_evalParen___closed__1 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalParen___closed__1();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalParen___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalParen___closed__2 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalParen___closed__2();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalParen___closed__2);
l___regBuiltinTactic_Lean_Elab_Tactic_evalParen___closed__3 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalParen___closed__3();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalParen___closed__3);
res = l___regBuiltinTactic_Lean_Elab_Tactic_evalParen(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock___closed__1 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock___closed__1();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock___closed__2 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock___closed__2();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock___closed__2);
l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock___closed__3 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock___closed__3();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock___closed__3);
res = l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlock(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__1 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__1();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__2 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__2();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__2);
l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__3 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__3();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly___closed__3);
res = l___regBuiltinTactic_Lean_Elab_Tactic_evalNestedTacticBlockCurly(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalCase___closed__1 = _init_l_Lean_Elab_Tactic_evalCase___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalCase___closed__1);
l_Lean_Elab_Tactic_evalCase___closed__2 = _init_l_Lean_Elab_Tactic_evalCase___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalCase___closed__2);
l_Lean_Elab_Tactic_evalCase___closed__3 = _init_l_Lean_Elab_Tactic_evalCase___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalCase___closed__3);
l___regBuiltinTactic_Lean_Elab_Tactic_evalCase___closed__1 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalCase___closed__1();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalCase___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalCase___closed__2 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalCase___closed__2();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalCase___closed__2);
l___regBuiltinTactic_Lean_Elab_Tactic_evalCase___closed__3 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalCase___closed__3();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalCase___closed__3);
res = l___regBuiltinTactic_Lean_Elab_Tactic_evalCase(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse___closed__1 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse___closed__1();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse___closed__2 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse___closed__2();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse___closed__2);
l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse___closed__3 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse___closed__3();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse___closed__3);
res = l___regBuiltinTactic_Lean_Elab_Tactic_evalOrelse(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Elab_Tactic_Basic_4__regTraceClasses___closed__1 = _init_l___private_Init_Lean_Elab_Tactic_Basic_4__regTraceClasses___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Tactic_Basic_4__regTraceClasses___closed__1);
res = l___private_Init_Lean_Elab_Tactic_Basic_4__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
