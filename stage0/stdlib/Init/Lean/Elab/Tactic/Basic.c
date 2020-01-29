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
extern lean_object* l_Lean_Meta_SynthInstance_inferTCGoalsLRAttr___closed__1;
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
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_coeDecidableEq(uint8_t);
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
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_save___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__5;
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__3;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalIntros___closed__3;
extern uint8_t l_String_posOfAux___main___closed__2;
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic___closed__6;
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_4__regTraceClasses(lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__4;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalTraceState___closed__2;
extern uint8_t l_String_posOfAux___main___closed__1;
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
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ensureHasType), 5, 3);
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
uint8_t x_6; 
x_6 = l_String_posOfAux___main___closed__2;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwError___rarg___boxed), 4, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_7, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwError___rarg___boxed), 4, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_10, x_3, x_4);
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_5);
x_12 = l_String_posOfAux___main___closed__1;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwError___rarg___boxed), 4, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
x_14 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_13, x_3, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwError___rarg___boxed), 4, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_2);
x_17 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_16, x_3, x_4);
return x_17;
}
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
lean_object* x_5; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; 
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
x_80 = l_coeDecidableEq(x_79);
if (x_80 == 0)
{
lean_dec(x_1);
x_5 = x_4;
goto block_74;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_3);
x_82 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_81, x_3, x_4);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_5 = x_83;
goto block_74;
}
else
{
uint8_t x_84; 
lean_dec(x_3);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_SMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__1(x_8, x_1);
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
x_27 = l_System_FilePath_dirName___closed__1;
x_28 = l_Lean_Name_toStringWithSep___main(x_27, x_1);
x_29 = l_Lean_Elab_Tactic_addBuiltinTactic___closed__1;
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
x_36 = l_Lean_SMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__1(x_34, x_1);
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
x_53 = l_System_FilePath_dirName___closed__1;
x_54 = l_Lean_Name_toStringWithSep___main(x_53, x_1);
x_55 = l_Lean_Elab_Tactic_addBuiltinTactic___closed__1;
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
uint8_t x_6; 
x_6 = l_coeDecidableEq(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__2;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Parser_Tactic_seq___elambda__1___closed__2;
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
x_45 = l_Lean_Parser_Tactic_seq___elambda__1___closed__1;
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
uint8_t x_48; 
x_48 = lean_string_dec_eq(x_35, x_45);
lean_dec(x_35);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_12);
lean_dec(x_1);
x_49 = lean_box(0);
x_15 = x_49;
goto block_24;
}
else
{
lean_object* x_50; 
lean_dec(x_14);
x_50 = l_Lean_Elab_Tactic_declareBuiltinTactic(x_1, x_12, x_2, x_13);
return x_50;
}
}
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_1);
x_51 = lean_box(0);
x_15 = x_51;
goto block_24;
}
}
else
{
lean_object* x_52; 
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
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_1);
x_56 = lean_box(0);
x_15 = x_56;
goto block_24;
}
}
block_24:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
x_16 = l_System_FilePath_dirName___closed__1;
x_17 = l_Lean_Name_toStringWithSep___main(x_16, x_2);
x_18 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__3;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__4;
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
uint8_t x_57; 
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_11);
if (x_57 == 0)
{
return x_11;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_11, 0);
x_59 = lean_ctor_get(x_11, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_11);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
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
x_24 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4(x_21, x_22, lean_box(0), x_23, x_3);
lean_dec(x_22);
lean_dec(x_21);
return x_24;
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
lean_object* x_4; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; uint8_t x_396; 
x_391 = lean_ctor_get(x_2, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
lean_dec(x_391);
x_393 = lean_ctor_get(x_392, 3);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 4);
lean_inc(x_394);
lean_dec(x_392);
x_395 = lean_nat_dec_eq(x_393, x_394);
lean_dec(x_394);
lean_dec(x_393);
x_396 = l_coeDecidableEq(x_395);
if (x_396 == 0)
{
x_4 = x_3;
goto block_390;
}
else
{
lean_object* x_397; lean_object* x_398; 
x_397 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_2);
lean_inc(x_1);
x_398 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_397, x_2, x_3);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; 
x_399 = lean_ctor_get(x_398, 1);
lean_inc(x_399);
lean_dec(x_398);
x_4 = x_399;
goto block_390;
}
else
{
uint8_t x_400; 
lean_dec(x_2);
lean_dec(x_1);
x_400 = !lean_is_exclusive(x_398);
if (x_400 == 0)
{
return x_398;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_398, 0);
x_402 = lean_ctor_get(x_398, 1);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_398);
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
return x_403;
}
}
}
block_390:
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
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = l_Lean_nullKind;
x_23 = lean_name_eq(x_21, x_22);
lean_dec(x_21);
x_24 = l_coeDecidableEq(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_inc(x_1);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_25, 0, x_1);
x_26 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__3;
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_1);
lean_closure_set(x_27, 2, x_25);
lean_inc(x_2);
x_28 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_27, x_2, x_4);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_PersistentEnvExtension_getState___rarg(x_31, x_34);
lean_dec(x_34);
lean_dec(x_31);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_1);
x_37 = l_Lean_Syntax_getKind(x_1);
x_38 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_36, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = l_Lean_Elab_Tactic_getEnv___rarg(x_29);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Elab_macroAttribute;
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
x_44 = l_Lean_PersistentEnvExtension_getState___rarg(x_43, x_40);
lean_dec(x_40);
lean_dec(x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_45, x_37);
lean_dec(x_37);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_box(0);
x_48 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_47, x_2, x_41);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
lean_dec(x_46);
x_50 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_49, x_2, x_41);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_37);
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
lean_dec(x_38);
lean_inc(x_29);
x_52 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_29, x_1, x_51, x_2, x_29);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_28);
if (x_53 == 0)
{
return x_28;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_28, 0);
x_55 = lean_ctor_get(x_28, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_28);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_58 = lean_unsigned_to_nat(2u);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_box(0);
x_61 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_58, x_57, x_59, x_60, x_2, x_4);
lean_dec(x_57);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_63 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_62, x_2, x_4);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_17, 0);
x_65 = lean_ctor_get(x_17, 1);
x_66 = lean_ctor_get(x_17, 2);
x_67 = lean_ctor_get(x_17, 3);
x_68 = lean_ctor_get(x_17, 4);
x_69 = lean_ctor_get(x_17, 5);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_17);
x_70 = lean_nat_add(x_69, x_14);
x_71 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_65);
lean_ctor_set(x_71, 2, x_66);
lean_ctor_set(x_71, 3, x_67);
lean_ctor_set(x_71, 4, x_68);
lean_ctor_set(x_71, 5, x_70);
lean_ctor_set(x_4, 0, x_71);
lean_ctor_set(x_5, 9, x_69);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_1, 0);
lean_inc(x_72);
x_73 = l_Lean_nullKind;
x_74 = lean_name_eq(x_72, x_73);
lean_dec(x_72);
x_75 = l_coeDecidableEq(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_inc(x_1);
x_76 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_76, 0, x_1);
x_77 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__3;
lean_inc(x_1);
x_78 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_78, 0, x_77);
lean_closure_set(x_78, 1, x_1);
lean_closure_set(x_78, 2, x_76);
lean_inc(x_2);
x_79 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_78, x_2, x_4);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l_Lean_PersistentEnvExtension_getState___rarg(x_82, x_85);
lean_dec(x_85);
lean_dec(x_82);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
lean_inc(x_1);
x_88 = l_Lean_Syntax_getKind(x_1);
x_89 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_87, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = l_Lean_Elab_Tactic_getEnv___rarg(x_80);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_Elab_macroAttribute;
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
x_95 = l_Lean_PersistentEnvExtension_getState___rarg(x_94, x_91);
lean_dec(x_91);
lean_dec(x_94);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_96, x_88);
lean_dec(x_88);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_box(0);
x_99 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_98, x_2, x_92);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_97, 0);
lean_inc(x_100);
lean_dec(x_97);
x_101 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_100, x_2, x_92);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_88);
x_102 = lean_ctor_get(x_89, 0);
lean_inc(x_102);
lean_dec(x_89);
lean_inc(x_80);
x_103 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_80, x_1, x_102, x_2, x_80);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_2);
lean_dec(x_1);
x_104 = lean_ctor_get(x_79, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_79, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_106 = x_79;
} else {
 lean_dec_ref(x_79);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_109 = lean_unsigned_to_nat(2u);
x_110 = lean_unsigned_to_nat(0u);
x_111 = lean_box(0);
x_112 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_109, x_108, x_110, x_111, x_2, x_4);
lean_dec(x_108);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_114 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_113, x_2, x_4);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_115 = lean_ctor_get(x_4, 0);
x_116 = lean_ctor_get(x_4, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_4);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_115, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_115, 4);
lean_inc(x_121);
x_122 = lean_ctor_get(x_115, 5);
lean_inc(x_122);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 lean_ctor_release(x_115, 2);
 lean_ctor_release(x_115, 3);
 lean_ctor_release(x_115, 4);
 lean_ctor_release(x_115, 5);
 x_123 = x_115;
} else {
 lean_dec_ref(x_115);
 x_123 = lean_box(0);
}
x_124 = lean_nat_add(x_122, x_14);
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
lean_ctor_set(x_125, 5, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_116);
lean_ctor_set(x_5, 9, x_122);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; uint8_t x_130; 
x_127 = lean_ctor_get(x_1, 0);
lean_inc(x_127);
x_128 = l_Lean_nullKind;
x_129 = lean_name_eq(x_127, x_128);
lean_dec(x_127);
x_130 = l_coeDecidableEq(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_inc(x_1);
x_131 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_131, 0, x_1);
x_132 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__3;
lean_inc(x_1);
x_133 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_133, 0, x_132);
lean_closure_set(x_133, 1, x_1);
lean_closure_set(x_133, 2, x_131);
lean_inc(x_2);
x_134 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_133, x_2, x_126);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec(x_139);
x_141 = l_Lean_PersistentEnvExtension_getState___rarg(x_137, x_140);
lean_dec(x_140);
lean_dec(x_137);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
lean_inc(x_1);
x_143 = l_Lean_Syntax_getKind(x_1);
x_144 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_142, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_145 = l_Lean_Elab_Tactic_getEnv___rarg(x_135);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = l_Lean_Elab_macroAttribute;
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
x_150 = l_Lean_PersistentEnvExtension_getState___rarg(x_149, x_146);
lean_dec(x_146);
lean_dec(x_149);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_152 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_151, x_143);
lean_dec(x_143);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_box(0);
x_154 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_153, x_2, x_147);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_155);
lean_dec(x_152);
x_156 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_155, x_2, x_147);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_143);
x_157 = lean_ctor_get(x_144, 0);
lean_inc(x_157);
lean_dec(x_144);
lean_inc(x_135);
x_158 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_135, x_1, x_157, x_2, x_135);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_2);
lean_dec(x_1);
x_159 = lean_ctor_get(x_134, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_134, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_161 = x_134;
} else {
 lean_dec_ref(x_134);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_163 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_164 = lean_unsigned_to_nat(2u);
x_165 = lean_unsigned_to_nat(0u);
x_166 = lean_box(0);
x_167 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_164, x_163, x_165, x_166, x_2, x_126);
lean_dec(x_163);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_169 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_168, x_2, x_126);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_170 = lean_ctor_get(x_6, 0);
x_171 = lean_ctor_get(x_6, 1);
x_172 = lean_ctor_get(x_6, 2);
x_173 = lean_ctor_get(x_6, 3);
x_174 = lean_ctor_get(x_6, 4);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_6);
x_175 = lean_unsigned_to_nat(1u);
x_176 = lean_nat_add(x_173, x_175);
lean_dec(x_173);
x_177 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_177, 0, x_170);
lean_ctor_set(x_177, 1, x_171);
lean_ctor_set(x_177, 2, x_172);
lean_ctor_set(x_177, 3, x_176);
lean_ctor_set(x_177, 4, x_174);
x_178 = lean_ctor_get(x_4, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_4, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_180 = x_4;
} else {
 lean_dec_ref(x_4);
 x_180 = lean_box(0);
}
x_181 = lean_ctor_get(x_178, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_178, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_178, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_178, 3);
lean_inc(x_184);
x_185 = lean_ctor_get(x_178, 4);
lean_inc(x_185);
x_186 = lean_ctor_get(x_178, 5);
lean_inc(x_186);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 lean_ctor_release(x_178, 2);
 lean_ctor_release(x_178, 3);
 lean_ctor_release(x_178, 4);
 lean_ctor_release(x_178, 5);
 x_187 = x_178;
} else {
 lean_dec_ref(x_178);
 x_187 = lean_box(0);
}
x_188 = lean_nat_add(x_186, x_175);
if (lean_is_scalar(x_187)) {
 x_189 = lean_alloc_ctor(0, 6, 0);
} else {
 x_189 = x_187;
}
lean_ctor_set(x_189, 0, x_181);
lean_ctor_set(x_189, 1, x_182);
lean_ctor_set(x_189, 2, x_183);
lean_ctor_set(x_189, 3, x_184);
lean_ctor_set(x_189, 4, x_185);
lean_ctor_set(x_189, 5, x_188);
if (lean_is_scalar(x_180)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_180;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_179);
lean_ctor_set(x_5, 9, x_186);
lean_ctor_set(x_5, 0, x_177);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_1, 0);
lean_inc(x_191);
x_192 = l_Lean_nullKind;
x_193 = lean_name_eq(x_191, x_192);
lean_dec(x_191);
x_194 = l_coeDecidableEq(x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_inc(x_1);
x_195 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_195, 0, x_1);
x_196 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__3;
lean_inc(x_1);
x_197 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_197, 0, x_196);
lean_closure_set(x_197, 1, x_1);
lean_closure_set(x_197, 2, x_195);
lean_inc(x_2);
x_198 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_197, x_2, x_190);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_200 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_199, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
lean_dec(x_202);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec(x_203);
x_205 = l_Lean_PersistentEnvExtension_getState___rarg(x_201, x_204);
lean_dec(x_204);
lean_dec(x_201);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec(x_205);
lean_inc(x_1);
x_207 = l_Lean_Syntax_getKind(x_1);
x_208 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_206, x_207);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_209 = l_Lean_Elab_Tactic_getEnv___rarg(x_199);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = l_Lean_Elab_macroAttribute;
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
x_214 = l_Lean_PersistentEnvExtension_getState___rarg(x_213, x_210);
lean_dec(x_210);
lean_dec(x_213);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
x_216 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_215, x_207);
lean_dec(x_207);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_box(0);
x_218 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_217, x_2, x_211);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_216, 0);
lean_inc(x_219);
lean_dec(x_216);
x_220 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_219, x_2, x_211);
return x_220;
}
}
else
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_207);
x_221 = lean_ctor_get(x_208, 0);
lean_inc(x_221);
lean_dec(x_208);
lean_inc(x_199);
x_222 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_199, x_1, x_221, x_2, x_199);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_2);
lean_dec(x_1);
x_223 = lean_ctor_get(x_198, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_198, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_225 = x_198;
} else {
 lean_dec_ref(x_198);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_227 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_228 = lean_unsigned_to_nat(2u);
x_229 = lean_unsigned_to_nat(0u);
x_230 = lean_box(0);
x_231 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_228, x_227, x_229, x_230, x_2, x_190);
lean_dec(x_227);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; 
x_232 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_233 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_232, x_2, x_190);
return x_233;
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_234 = lean_ctor_get(x_5, 1);
x_235 = lean_ctor_get(x_5, 2);
x_236 = lean_ctor_get(x_5, 3);
x_237 = lean_ctor_get(x_5, 4);
x_238 = lean_ctor_get(x_5, 5);
x_239 = lean_ctor_get(x_5, 6);
x_240 = lean_ctor_get(x_5, 7);
x_241 = lean_ctor_get(x_5, 8);
x_242 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_243 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_5);
x_244 = lean_ctor_get(x_6, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_6, 1);
lean_inc(x_245);
x_246 = lean_ctor_get(x_6, 2);
lean_inc(x_246);
x_247 = lean_ctor_get(x_6, 3);
lean_inc(x_247);
x_248 = lean_ctor_get(x_6, 4);
lean_inc(x_248);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_249 = x_6;
} else {
 lean_dec_ref(x_6);
 x_249 = lean_box(0);
}
x_250 = lean_unsigned_to_nat(1u);
x_251 = lean_nat_add(x_247, x_250);
lean_dec(x_247);
if (lean_is_scalar(x_249)) {
 x_252 = lean_alloc_ctor(0, 5, 0);
} else {
 x_252 = x_249;
}
lean_ctor_set(x_252, 0, x_244);
lean_ctor_set(x_252, 1, x_245);
lean_ctor_set(x_252, 2, x_246);
lean_ctor_set(x_252, 3, x_251);
lean_ctor_set(x_252, 4, x_248);
x_253 = lean_ctor_get(x_4, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_4, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_255 = x_4;
} else {
 lean_dec_ref(x_4);
 x_255 = lean_box(0);
}
x_256 = lean_ctor_get(x_253, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_253, 1);
lean_inc(x_257);
x_258 = lean_ctor_get(x_253, 2);
lean_inc(x_258);
x_259 = lean_ctor_get(x_253, 3);
lean_inc(x_259);
x_260 = lean_ctor_get(x_253, 4);
lean_inc(x_260);
x_261 = lean_ctor_get(x_253, 5);
lean_inc(x_261);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 lean_ctor_release(x_253, 2);
 lean_ctor_release(x_253, 3);
 lean_ctor_release(x_253, 4);
 lean_ctor_release(x_253, 5);
 x_262 = x_253;
} else {
 lean_dec_ref(x_253);
 x_262 = lean_box(0);
}
x_263 = lean_nat_add(x_261, x_250);
if (lean_is_scalar(x_262)) {
 x_264 = lean_alloc_ctor(0, 6, 0);
} else {
 x_264 = x_262;
}
lean_ctor_set(x_264, 0, x_256);
lean_ctor_set(x_264, 1, x_257);
lean_ctor_set(x_264, 2, x_258);
lean_ctor_set(x_264, 3, x_259);
lean_ctor_set(x_264, 4, x_260);
lean_ctor_set(x_264, 5, x_263);
if (lean_is_scalar(x_255)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_255;
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_254);
x_266 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_266, 0, x_252);
lean_ctor_set(x_266, 1, x_234);
lean_ctor_set(x_266, 2, x_235);
lean_ctor_set(x_266, 3, x_236);
lean_ctor_set(x_266, 4, x_237);
lean_ctor_set(x_266, 5, x_238);
lean_ctor_set(x_266, 6, x_239);
lean_ctor_set(x_266, 7, x_240);
lean_ctor_set(x_266, 8, x_241);
lean_ctor_set(x_266, 9, x_261);
lean_ctor_set_uint8(x_266, sizeof(void*)*10, x_242);
lean_ctor_set_uint8(x_266, sizeof(void*)*10 + 1, x_243);
lean_ctor_set(x_2, 0, x_266);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_267; lean_object* x_268; uint8_t x_269; uint8_t x_270; 
x_267 = lean_ctor_get(x_1, 0);
lean_inc(x_267);
x_268 = l_Lean_nullKind;
x_269 = lean_name_eq(x_267, x_268);
lean_dec(x_267);
x_270 = l_coeDecidableEq(x_269);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_inc(x_1);
x_271 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_271, 0, x_1);
x_272 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__3;
lean_inc(x_1);
x_273 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_273, 0, x_272);
lean_closure_set(x_273, 1, x_1);
lean_closure_set(x_273, 2, x_271);
lean_inc(x_2);
x_274 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_273, x_2, x_265);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
lean_dec(x_274);
x_276 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
x_278 = lean_ctor_get(x_275, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
lean_dec(x_278);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
lean_dec(x_279);
x_281 = l_Lean_PersistentEnvExtension_getState___rarg(x_277, x_280);
lean_dec(x_280);
lean_dec(x_277);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
lean_dec(x_281);
lean_inc(x_1);
x_283 = l_Lean_Syntax_getKind(x_1);
x_284 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_282, x_283);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_285 = l_Lean_Elab_Tactic_getEnv___rarg(x_275);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = l_Lean_Elab_macroAttribute;
x_289 = lean_ctor_get(x_288, 1);
lean_inc(x_289);
x_290 = l_Lean_PersistentEnvExtension_getState___rarg(x_289, x_286);
lean_dec(x_286);
lean_dec(x_289);
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
lean_dec(x_290);
x_292 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_291, x_283);
lean_dec(x_283);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_box(0);
x_294 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_293, x_2, x_287);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_292, 0);
lean_inc(x_295);
lean_dec(x_292);
x_296 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_295, x_2, x_287);
return x_296;
}
}
else
{
lean_object* x_297; lean_object* x_298; 
lean_dec(x_283);
x_297 = lean_ctor_get(x_284, 0);
lean_inc(x_297);
lean_dec(x_284);
lean_inc(x_275);
x_298 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_275, x_1, x_297, x_2, x_275);
return x_298;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_2);
lean_dec(x_1);
x_299 = lean_ctor_get(x_274, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_274, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_301 = x_274;
} else {
 lean_dec_ref(x_274);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_300);
return x_302;
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_303 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_304 = lean_unsigned_to_nat(2u);
x_305 = lean_unsigned_to_nat(0u);
x_306 = lean_box(0);
x_307 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_304, x_303, x_305, x_306, x_2, x_265);
lean_dec(x_303);
return x_307;
}
}
else
{
lean_object* x_308; lean_object* x_309; 
x_308 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_309 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_308, x_2, x_265);
return x_309;
}
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; uint8_t x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_310 = lean_ctor_get(x_2, 1);
x_311 = lean_ctor_get(x_2, 2);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_2);
x_312 = lean_ctor_get(x_5, 1);
lean_inc(x_312);
x_313 = lean_ctor_get(x_5, 2);
lean_inc(x_313);
x_314 = lean_ctor_get(x_5, 3);
lean_inc(x_314);
x_315 = lean_ctor_get(x_5, 4);
lean_inc(x_315);
x_316 = lean_ctor_get(x_5, 5);
lean_inc(x_316);
x_317 = lean_ctor_get(x_5, 6);
lean_inc(x_317);
x_318 = lean_ctor_get(x_5, 7);
lean_inc(x_318);
x_319 = lean_ctor_get(x_5, 8);
lean_inc(x_319);
x_320 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_321 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
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
 x_322 = x_5;
} else {
 lean_dec_ref(x_5);
 x_322 = lean_box(0);
}
x_323 = lean_ctor_get(x_6, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_6, 1);
lean_inc(x_324);
x_325 = lean_ctor_get(x_6, 2);
lean_inc(x_325);
x_326 = lean_ctor_get(x_6, 3);
lean_inc(x_326);
x_327 = lean_ctor_get(x_6, 4);
lean_inc(x_327);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_328 = x_6;
} else {
 lean_dec_ref(x_6);
 x_328 = lean_box(0);
}
x_329 = lean_unsigned_to_nat(1u);
x_330 = lean_nat_add(x_326, x_329);
lean_dec(x_326);
if (lean_is_scalar(x_328)) {
 x_331 = lean_alloc_ctor(0, 5, 0);
} else {
 x_331 = x_328;
}
lean_ctor_set(x_331, 0, x_323);
lean_ctor_set(x_331, 1, x_324);
lean_ctor_set(x_331, 2, x_325);
lean_ctor_set(x_331, 3, x_330);
lean_ctor_set(x_331, 4, x_327);
x_332 = lean_ctor_get(x_4, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_4, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_334 = x_4;
} else {
 lean_dec_ref(x_4);
 x_334 = lean_box(0);
}
x_335 = lean_ctor_get(x_332, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_332, 1);
lean_inc(x_336);
x_337 = lean_ctor_get(x_332, 2);
lean_inc(x_337);
x_338 = lean_ctor_get(x_332, 3);
lean_inc(x_338);
x_339 = lean_ctor_get(x_332, 4);
lean_inc(x_339);
x_340 = lean_ctor_get(x_332, 5);
lean_inc(x_340);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 lean_ctor_release(x_332, 1);
 lean_ctor_release(x_332, 2);
 lean_ctor_release(x_332, 3);
 lean_ctor_release(x_332, 4);
 lean_ctor_release(x_332, 5);
 x_341 = x_332;
} else {
 lean_dec_ref(x_332);
 x_341 = lean_box(0);
}
x_342 = lean_nat_add(x_340, x_329);
if (lean_is_scalar(x_341)) {
 x_343 = lean_alloc_ctor(0, 6, 0);
} else {
 x_343 = x_341;
}
lean_ctor_set(x_343, 0, x_335);
lean_ctor_set(x_343, 1, x_336);
lean_ctor_set(x_343, 2, x_337);
lean_ctor_set(x_343, 3, x_338);
lean_ctor_set(x_343, 4, x_339);
lean_ctor_set(x_343, 5, x_342);
if (lean_is_scalar(x_334)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_334;
}
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_333);
if (lean_is_scalar(x_322)) {
 x_345 = lean_alloc_ctor(0, 10, 2);
} else {
 x_345 = x_322;
}
lean_ctor_set(x_345, 0, x_331);
lean_ctor_set(x_345, 1, x_312);
lean_ctor_set(x_345, 2, x_313);
lean_ctor_set(x_345, 3, x_314);
lean_ctor_set(x_345, 4, x_315);
lean_ctor_set(x_345, 5, x_316);
lean_ctor_set(x_345, 6, x_317);
lean_ctor_set(x_345, 7, x_318);
lean_ctor_set(x_345, 8, x_319);
lean_ctor_set(x_345, 9, x_340);
lean_ctor_set_uint8(x_345, sizeof(void*)*10, x_320);
lean_ctor_set_uint8(x_345, sizeof(void*)*10 + 1, x_321);
x_346 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_310);
lean_ctor_set(x_346, 2, x_311);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_347; lean_object* x_348; uint8_t x_349; uint8_t x_350; 
x_347 = lean_ctor_get(x_1, 0);
lean_inc(x_347);
x_348 = l_Lean_nullKind;
x_349 = lean_name_eq(x_347, x_348);
lean_dec(x_347);
x_350 = l_coeDecidableEq(x_349);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_inc(x_1);
x_351 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_351, 0, x_1);
x_352 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__3;
lean_inc(x_1);
x_353 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_353, 0, x_352);
lean_closure_set(x_353, 1, x_1);
lean_closure_set(x_353, 2, x_351);
lean_inc(x_346);
x_354 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_353, x_346, x_344);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_355 = lean_ctor_get(x_354, 1);
lean_inc(x_355);
lean_dec(x_354);
x_356 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_357 = lean_ctor_get(x_356, 1);
lean_inc(x_357);
x_358 = lean_ctor_get(x_355, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
lean_dec(x_358);
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
lean_dec(x_359);
x_361 = l_Lean_PersistentEnvExtension_getState___rarg(x_357, x_360);
lean_dec(x_360);
lean_dec(x_357);
x_362 = lean_ctor_get(x_361, 1);
lean_inc(x_362);
lean_dec(x_361);
lean_inc(x_1);
x_363 = l_Lean_Syntax_getKind(x_1);
x_364 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_362, x_363);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_365 = l_Lean_Elab_Tactic_getEnv___rarg(x_355);
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_368 = l_Lean_Elab_macroAttribute;
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
x_370 = l_Lean_PersistentEnvExtension_getState___rarg(x_369, x_366);
lean_dec(x_366);
lean_dec(x_369);
x_371 = lean_ctor_get(x_370, 1);
lean_inc(x_371);
lean_dec(x_370);
x_372 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_371, x_363);
lean_dec(x_363);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; 
x_373 = lean_box(0);
x_374 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_373, x_346, x_367);
return x_374;
}
else
{
lean_object* x_375; lean_object* x_376; 
x_375 = lean_ctor_get(x_372, 0);
lean_inc(x_375);
lean_dec(x_372);
x_376 = l___private_Init_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_375, x_346, x_367);
return x_376;
}
}
else
{
lean_object* x_377; lean_object* x_378; 
lean_dec(x_363);
x_377 = lean_ctor_get(x_364, 0);
lean_inc(x_377);
lean_dec(x_364);
lean_inc(x_355);
x_378 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_355, x_1, x_377, x_346, x_355);
return x_378;
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_346);
lean_dec(x_1);
x_379 = lean_ctor_get(x_354, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_354, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_381 = x_354;
} else {
 lean_dec_ref(x_354);
 x_381 = lean_box(0);
}
if (lean_is_scalar(x_381)) {
 x_382 = lean_alloc_ctor(1, 2, 0);
} else {
 x_382 = x_381;
}
lean_ctor_set(x_382, 0, x_379);
lean_ctor_set(x_382, 1, x_380);
return x_382;
}
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_383 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_384 = lean_unsigned_to_nat(2u);
x_385 = lean_unsigned_to_nat(0u);
x_386 = lean_box(0);
x_387 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_384, x_383, x_385, x_386, x_346, x_344);
lean_dec(x_383);
return x_387;
}
}
else
{
lean_object* x_388; lean_object* x_389; 
x_388 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_389 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_388, x_346, x_344);
return x_389;
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
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_3);
x_12 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_11, x_3, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Elab_Tactic_save(x_13);
lean_inc(x_13);
x_15 = lean_apply_2(x_2, x_3, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_15, 1);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_16, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_18, 2);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_19, 2);
lean_dec(x_29);
lean_ctor_set(x_19, 2, x_10);
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_10);
lean_ctor_set(x_18, 2, x_32);
return x_15;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
x_35 = lean_ctor_get(x_18, 3);
x_36 = lean_ctor_get(x_18, 4);
x_37 = lean_ctor_get(x_18, 5);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_38 = lean_ctor_get(x_19, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_40 = x_19;
} else {
 lean_dec_ref(x_19);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 3, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_10);
x_42 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_34);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_35);
lean_ctor_set(x_42, 4, x_36);
lean_ctor_set(x_42, 5, x_37);
lean_ctor_set(x_17, 0, x_42);
return x_15;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_43 = lean_ctor_get(x_17, 1);
x_44 = lean_ctor_get(x_17, 2);
x_45 = lean_ctor_get(x_17, 3);
x_46 = lean_ctor_get(x_17, 4);
x_47 = lean_ctor_get(x_17, 5);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_17);
x_48 = lean_ctor_get(x_18, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_18, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_18, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_18, 4);
lean_inc(x_51);
x_52 = lean_ctor_get(x_18, 5);
lean_inc(x_52);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 x_53 = x_18;
} else {
 lean_dec_ref(x_18);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_19, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_19, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_56 = x_19;
} else {
 lean_dec_ref(x_19);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 3, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_10);
if (lean_is_scalar(x_53)) {
 x_58 = lean_alloc_ctor(0, 6, 0);
} else {
 x_58 = x_53;
}
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_49);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set(x_58, 3, x_50);
lean_ctor_set(x_58, 4, x_51);
lean_ctor_set(x_58, 5, x_52);
x_59 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_43);
lean_ctor_set(x_59, 2, x_44);
lean_ctor_set(x_59, 3, x_45);
lean_ctor_set(x_59, 4, x_46);
lean_ctor_set(x_59, 5, x_47);
lean_ctor_set(x_16, 0, x_59);
return x_15;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_60 = lean_ctor_get(x_16, 1);
lean_inc(x_60);
lean_dec(x_16);
x_61 = lean_ctor_get(x_17, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_17, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_17, 3);
lean_inc(x_63);
x_64 = lean_ctor_get(x_17, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_17, 5);
lean_inc(x_65);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 lean_ctor_release(x_17, 5);
 x_66 = x_17;
} else {
 lean_dec_ref(x_17);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_18, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_18, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_18, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_18, 4);
lean_inc(x_70);
x_71 = lean_ctor_get(x_18, 5);
lean_inc(x_71);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 x_72 = x_18;
} else {
 lean_dec_ref(x_18);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_19, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_19, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_75 = x_19;
} else {
 lean_dec_ref(x_19);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 3, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_10);
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
if (lean_is_scalar(x_66)) {
 x_78 = lean_alloc_ctor(0, 6, 0);
} else {
 x_78 = x_66;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_61);
lean_ctor_set(x_78, 2, x_62);
lean_ctor_set(x_78, 3, x_63);
lean_ctor_set(x_78, 4, x_64);
lean_ctor_set(x_78, 5, x_65);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_60);
lean_ctor_set(x_15, 1, x_79);
return x_15;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_80 = lean_ctor_get(x_15, 0);
lean_inc(x_80);
lean_dec(x_15);
x_81 = lean_ctor_get(x_16, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_82 = x_16;
} else {
 lean_dec_ref(x_16);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_17, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_17, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_17, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_17, 4);
lean_inc(x_86);
x_87 = lean_ctor_get(x_17, 5);
lean_inc(x_87);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 lean_ctor_release(x_17, 5);
 x_88 = x_17;
} else {
 lean_dec_ref(x_17);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_18, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_18, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_18, 3);
lean_inc(x_91);
x_92 = lean_ctor_get(x_18, 4);
lean_inc(x_92);
x_93 = lean_ctor_get(x_18, 5);
lean_inc(x_93);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 x_94 = x_18;
} else {
 lean_dec_ref(x_18);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_19, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_19, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_97 = x_19;
} else {
 lean_dec_ref(x_19);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(0, 3, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
lean_ctor_set(x_98, 2, x_10);
if (lean_is_scalar(x_94)) {
 x_99 = lean_alloc_ctor(0, 6, 0);
} else {
 x_99 = x_94;
}
lean_ctor_set(x_99, 0, x_89);
lean_ctor_set(x_99, 1, x_90);
lean_ctor_set(x_99, 2, x_98);
lean_ctor_set(x_99, 3, x_91);
lean_ctor_set(x_99, 4, x_92);
lean_ctor_set(x_99, 5, x_93);
if (lean_is_scalar(x_88)) {
 x_100 = lean_alloc_ctor(0, 6, 0);
} else {
 x_100 = x_88;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_83);
lean_ctor_set(x_100, 2, x_84);
lean_ctor_set(x_100, 3, x_85);
lean_ctor_set(x_100, 4, x_86);
lean_ctor_set(x_100, 5, x_87);
if (lean_is_scalar(x_82)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_82;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_81);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_80);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
else
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_15);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_104 = lean_ctor_get(x_15, 1);
x_105 = l_Lean_Elab_Tactic_restore(x_104, x_14);
lean_dec(x_14);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 2);
lean_inc(x_108);
x_109 = !lean_is_exclusive(x_106);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_106, 0);
lean_dec(x_110);
x_111 = !lean_is_exclusive(x_107);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_107, 2);
lean_dec(x_112);
x_113 = !lean_is_exclusive(x_108);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_108, 2);
lean_dec(x_114);
lean_ctor_set(x_108, 2, x_10);
x_115 = !lean_is_exclusive(x_13);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_13, 0);
lean_dec(x_116);
lean_ctor_set(x_13, 0, x_106);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_13, 1);
lean_inc(x_117);
lean_dec(x_13);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_106);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_15, 1, x_118);
return x_15;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_ctor_get(x_108, 0);
x_120 = lean_ctor_get(x_108, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_108);
x_121 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set(x_121, 2, x_10);
lean_ctor_set(x_107, 2, x_121);
x_122 = lean_ctor_get(x_13, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_123 = x_13;
} else {
 lean_dec_ref(x_13);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_106);
lean_ctor_set(x_124, 1, x_122);
lean_ctor_set(x_15, 1, x_124);
return x_15;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_125 = lean_ctor_get(x_107, 0);
x_126 = lean_ctor_get(x_107, 1);
x_127 = lean_ctor_get(x_107, 3);
x_128 = lean_ctor_get(x_107, 4);
x_129 = lean_ctor_get(x_107, 5);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_107);
x_130 = lean_ctor_get(x_108, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_108, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 lean_ctor_release(x_108, 2);
 x_132 = x_108;
} else {
 lean_dec_ref(x_108);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(0, 3, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
lean_ctor_set(x_133, 2, x_10);
x_134 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_126);
lean_ctor_set(x_134, 2, x_133);
lean_ctor_set(x_134, 3, x_127);
lean_ctor_set(x_134, 4, x_128);
lean_ctor_set(x_134, 5, x_129);
lean_ctor_set(x_106, 0, x_134);
x_135 = lean_ctor_get(x_13, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_136 = x_13;
} else {
 lean_dec_ref(x_13);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_106);
lean_ctor_set(x_137, 1, x_135);
lean_ctor_set(x_15, 1, x_137);
return x_15;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_138 = lean_ctor_get(x_106, 1);
x_139 = lean_ctor_get(x_106, 2);
x_140 = lean_ctor_get(x_106, 3);
x_141 = lean_ctor_get(x_106, 4);
x_142 = lean_ctor_get(x_106, 5);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_106);
x_143 = lean_ctor_get(x_107, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_107, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_107, 3);
lean_inc(x_145);
x_146 = lean_ctor_get(x_107, 4);
lean_inc(x_146);
x_147 = lean_ctor_get(x_107, 5);
lean_inc(x_147);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 lean_ctor_release(x_107, 3);
 lean_ctor_release(x_107, 4);
 lean_ctor_release(x_107, 5);
 x_148 = x_107;
} else {
 lean_dec_ref(x_107);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_108, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_108, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 lean_ctor_release(x_108, 2);
 x_151 = x_108;
} else {
 lean_dec_ref(x_108);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(0, 3, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
lean_ctor_set(x_152, 2, x_10);
if (lean_is_scalar(x_148)) {
 x_153 = lean_alloc_ctor(0, 6, 0);
} else {
 x_153 = x_148;
}
lean_ctor_set(x_153, 0, x_143);
lean_ctor_set(x_153, 1, x_144);
lean_ctor_set(x_153, 2, x_152);
lean_ctor_set(x_153, 3, x_145);
lean_ctor_set(x_153, 4, x_146);
lean_ctor_set(x_153, 5, x_147);
x_154 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_138);
lean_ctor_set(x_154, 2, x_139);
lean_ctor_set(x_154, 3, x_140);
lean_ctor_set(x_154, 4, x_141);
lean_ctor_set(x_154, 5, x_142);
x_155 = lean_ctor_get(x_13, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_156 = x_13;
} else {
 lean_dec_ref(x_13);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
lean_ctor_set(x_15, 1, x_157);
return x_15;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_158 = lean_ctor_get(x_15, 0);
x_159 = lean_ctor_get(x_15, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_15);
x_160 = l_Lean_Elab_Tactic_restore(x_159, x_14);
lean_dec(x_14);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
lean_dec(x_160);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_162, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_161, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_161, 3);
lean_inc(x_166);
x_167 = lean_ctor_get(x_161, 4);
lean_inc(x_167);
x_168 = lean_ctor_get(x_161, 5);
lean_inc(x_168);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 lean_ctor_release(x_161, 2);
 lean_ctor_release(x_161, 3);
 lean_ctor_release(x_161, 4);
 lean_ctor_release(x_161, 5);
 x_169 = x_161;
} else {
 lean_dec_ref(x_161);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_162, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_162, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_162, 3);
lean_inc(x_172);
x_173 = lean_ctor_get(x_162, 4);
lean_inc(x_173);
x_174 = lean_ctor_get(x_162, 5);
lean_inc(x_174);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 lean_ctor_release(x_162, 2);
 lean_ctor_release(x_162, 3);
 lean_ctor_release(x_162, 4);
 lean_ctor_release(x_162, 5);
 x_175 = x_162;
} else {
 lean_dec_ref(x_162);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_163, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_163, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 lean_ctor_release(x_163, 2);
 x_178 = x_163;
} else {
 lean_dec_ref(x_163);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(0, 3, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
lean_ctor_set(x_179, 2, x_10);
if (lean_is_scalar(x_175)) {
 x_180 = lean_alloc_ctor(0, 6, 0);
} else {
 x_180 = x_175;
}
lean_ctor_set(x_180, 0, x_170);
lean_ctor_set(x_180, 1, x_171);
lean_ctor_set(x_180, 2, x_179);
lean_ctor_set(x_180, 3, x_172);
lean_ctor_set(x_180, 4, x_173);
lean_ctor_set(x_180, 5, x_174);
if (lean_is_scalar(x_169)) {
 x_181 = lean_alloc_ctor(0, 6, 0);
} else {
 x_181 = x_169;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_164);
lean_ctor_set(x_181, 2, x_165);
lean_ctor_set(x_181, 3, x_166);
lean_ctor_set(x_181, 4, x_167);
lean_ctor_set(x_181, 5, x_168);
x_182 = lean_ctor_get(x_13, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_183 = x_13;
} else {
 lean_dec_ref(x_13);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_158);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_186 = !lean_is_exclusive(x_12);
if (x_186 == 0)
{
return x_12;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_12, 0);
x_188 = lean_ctor_get(x_12, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_12);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; 
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
uint8_t x_210; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_3);
x_210 = 0;
x_23 = x_210;
goto block_209;
}
else
{
lean_object* x_211; uint8_t x_212; 
x_211 = lean_unsigned_to_nat(0u);
x_212 = l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1(x_3, x_8, lean_box(0), x_15, x_18, x_211);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_3);
x_23 = x_212;
goto block_209;
}
block_209:
{
uint8_t x_24; 
x_24 = l_coeDecidableEq(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_apply_2(x_2, x_22, x_9);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_9, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 2);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 2);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_22);
x_31 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_30, x_22, x_9);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Elab_Tactic_save(x_32);
lean_inc(x_32);
x_34 = lean_apply_2(x_2, x_22, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_33);
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 2);
lean_inc(x_38);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_34, 1);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_35, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_36, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_37, 2);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_38);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_38, 2);
lean_dec(x_48);
lean_ctor_set(x_38, 2, x_29);
return x_34;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_29);
lean_ctor_set(x_37, 2, x_51);
return x_34;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_37, 0);
x_53 = lean_ctor_get(x_37, 1);
x_54 = lean_ctor_get(x_37, 3);
x_55 = lean_ctor_get(x_37, 4);
x_56 = lean_ctor_get(x_37, 5);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_37);
x_57 = lean_ctor_get(x_38, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_38, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_59 = x_38;
} else {
 lean_dec_ref(x_38);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 3, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_29);
x_61 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_53);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_54);
lean_ctor_set(x_61, 4, x_55);
lean_ctor_set(x_61, 5, x_56);
lean_ctor_set(x_36, 0, x_61);
return x_34;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_62 = lean_ctor_get(x_36, 1);
x_63 = lean_ctor_get(x_36, 2);
x_64 = lean_ctor_get(x_36, 3);
x_65 = lean_ctor_get(x_36, 4);
x_66 = lean_ctor_get(x_36, 5);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_36);
x_67 = lean_ctor_get(x_37, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_37, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_37, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_37, 4);
lean_inc(x_70);
x_71 = lean_ctor_get(x_37, 5);
lean_inc(x_71);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 x_72 = x_37;
} else {
 lean_dec_ref(x_37);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_38, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_38, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_75 = x_38;
} else {
 lean_dec_ref(x_38);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 3, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_29);
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
lean_ctor_set(x_35, 0, x_78);
return x_34;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_79 = lean_ctor_get(x_35, 1);
lean_inc(x_79);
lean_dec(x_35);
x_80 = lean_ctor_get(x_36, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_36, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_36, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_36, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_36, 5);
lean_inc(x_84);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 lean_ctor_release(x_36, 4);
 lean_ctor_release(x_36, 5);
 x_85 = x_36;
} else {
 lean_dec_ref(x_36);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_37, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_37, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_37, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_37, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_37, 5);
lean_inc(x_90);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 x_91 = x_37;
} else {
 lean_dec_ref(x_37);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_38, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_38, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_94 = x_38;
} else {
 lean_dec_ref(x_38);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 3, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_29);
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
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_79);
lean_ctor_set(x_34, 1, x_98);
return x_34;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_99 = lean_ctor_get(x_34, 0);
lean_inc(x_99);
lean_dec(x_34);
x_100 = lean_ctor_get(x_35, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_101 = x_35;
} else {
 lean_dec_ref(x_35);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_36, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_36, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_36, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_36, 4);
lean_inc(x_105);
x_106 = lean_ctor_get(x_36, 5);
lean_inc(x_106);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 lean_ctor_release(x_36, 4);
 lean_ctor_release(x_36, 5);
 x_107 = x_36;
} else {
 lean_dec_ref(x_36);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_37, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_37, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_37, 3);
lean_inc(x_110);
x_111 = lean_ctor_get(x_37, 4);
lean_inc(x_111);
x_112 = lean_ctor_get(x_37, 5);
lean_inc(x_112);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 x_113 = x_37;
} else {
 lean_dec_ref(x_37);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_38, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_38, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_116 = x_38;
} else {
 lean_dec_ref(x_38);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 3, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
lean_ctor_set(x_117, 2, x_29);
if (lean_is_scalar(x_113)) {
 x_118 = lean_alloc_ctor(0, 6, 0);
} else {
 x_118 = x_113;
}
lean_ctor_set(x_118, 0, x_108);
lean_ctor_set(x_118, 1, x_109);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_118, 3, x_110);
lean_ctor_set(x_118, 4, x_111);
lean_ctor_set(x_118, 5, x_112);
if (lean_is_scalar(x_107)) {
 x_119 = lean_alloc_ctor(0, 6, 0);
} else {
 x_119 = x_107;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_102);
lean_ctor_set(x_119, 2, x_103);
lean_ctor_set(x_119, 3, x_104);
lean_ctor_set(x_119, 4, x_105);
lean_ctor_set(x_119, 5, x_106);
if (lean_is_scalar(x_101)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_101;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_100);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_99);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
else
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_34);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_123 = lean_ctor_get(x_34, 1);
x_124 = l_Lean_Elab_Tactic_restore(x_123, x_33);
lean_dec(x_33);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_126, 2);
lean_inc(x_127);
x_128 = !lean_is_exclusive(x_125);
if (x_128 == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_125, 0);
lean_dec(x_129);
x_130 = !lean_is_exclusive(x_126);
if (x_130 == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_126, 2);
lean_dec(x_131);
x_132 = !lean_is_exclusive(x_127);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_127, 2);
lean_dec(x_133);
lean_ctor_set(x_127, 2, x_29);
x_134 = !lean_is_exclusive(x_32);
if (x_134 == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_32, 0);
lean_dec(x_135);
lean_ctor_set(x_32, 0, x_125);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_32, 1);
lean_inc(x_136);
lean_dec(x_32);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_125);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set(x_34, 1, x_137);
return x_34;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_138 = lean_ctor_get(x_127, 0);
x_139 = lean_ctor_get(x_127, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_127);
x_140 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_140, 2, x_29);
lean_ctor_set(x_126, 2, x_140);
x_141 = lean_ctor_get(x_32, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_142 = x_32;
} else {
 lean_dec_ref(x_32);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_125);
lean_ctor_set(x_143, 1, x_141);
lean_ctor_set(x_34, 1, x_143);
return x_34;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_144 = lean_ctor_get(x_126, 0);
x_145 = lean_ctor_get(x_126, 1);
x_146 = lean_ctor_get(x_126, 3);
x_147 = lean_ctor_get(x_126, 4);
x_148 = lean_ctor_get(x_126, 5);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_126);
x_149 = lean_ctor_get(x_127, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_127, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 x_151 = x_127;
} else {
 lean_dec_ref(x_127);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(0, 3, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
lean_ctor_set(x_152, 2, x_29);
x_153 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_153, 0, x_144);
lean_ctor_set(x_153, 1, x_145);
lean_ctor_set(x_153, 2, x_152);
lean_ctor_set(x_153, 3, x_146);
lean_ctor_set(x_153, 4, x_147);
lean_ctor_set(x_153, 5, x_148);
lean_ctor_set(x_125, 0, x_153);
x_154 = lean_ctor_get(x_32, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_155 = x_32;
} else {
 lean_dec_ref(x_32);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_125);
lean_ctor_set(x_156, 1, x_154);
lean_ctor_set(x_34, 1, x_156);
return x_34;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_157 = lean_ctor_get(x_125, 1);
x_158 = lean_ctor_get(x_125, 2);
x_159 = lean_ctor_get(x_125, 3);
x_160 = lean_ctor_get(x_125, 4);
x_161 = lean_ctor_get(x_125, 5);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_125);
x_162 = lean_ctor_get(x_126, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_126, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_126, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_126, 4);
lean_inc(x_165);
x_166 = lean_ctor_get(x_126, 5);
lean_inc(x_166);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 lean_ctor_release(x_126, 2);
 lean_ctor_release(x_126, 3);
 lean_ctor_release(x_126, 4);
 lean_ctor_release(x_126, 5);
 x_167 = x_126;
} else {
 lean_dec_ref(x_126);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_127, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_127, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 x_170 = x_127;
} else {
 lean_dec_ref(x_127);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(0, 3, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
lean_ctor_set(x_171, 2, x_29);
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
x_173 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_157);
lean_ctor_set(x_173, 2, x_158);
lean_ctor_set(x_173, 3, x_159);
lean_ctor_set(x_173, 4, x_160);
lean_ctor_set(x_173, 5, x_161);
x_174 = lean_ctor_get(x_32, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_175 = x_32;
} else {
 lean_dec_ref(x_32);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
lean_ctor_set(x_34, 1, x_176);
return x_34;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_177 = lean_ctor_get(x_34, 0);
x_178 = lean_ctor_get(x_34, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_34);
x_179 = l_Lean_Elab_Tactic_restore(x_178, x_33);
lean_dec(x_33);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec(x_179);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_181, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_180, 2);
lean_inc(x_184);
x_185 = lean_ctor_get(x_180, 3);
lean_inc(x_185);
x_186 = lean_ctor_get(x_180, 4);
lean_inc(x_186);
x_187 = lean_ctor_get(x_180, 5);
lean_inc(x_187);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 lean_ctor_release(x_180, 2);
 lean_ctor_release(x_180, 3);
 lean_ctor_release(x_180, 4);
 lean_ctor_release(x_180, 5);
 x_188 = x_180;
} else {
 lean_dec_ref(x_180);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_181, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_181, 1);
lean_inc(x_190);
x_191 = lean_ctor_get(x_181, 3);
lean_inc(x_191);
x_192 = lean_ctor_get(x_181, 4);
lean_inc(x_192);
x_193 = lean_ctor_get(x_181, 5);
lean_inc(x_193);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 lean_ctor_release(x_181, 2);
 lean_ctor_release(x_181, 3);
 lean_ctor_release(x_181, 4);
 lean_ctor_release(x_181, 5);
 x_194 = x_181;
} else {
 lean_dec_ref(x_181);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_182, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_182, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 lean_ctor_release(x_182, 2);
 x_197 = x_182;
} else {
 lean_dec_ref(x_182);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(0, 3, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
lean_ctor_set(x_198, 2, x_29);
if (lean_is_scalar(x_194)) {
 x_199 = lean_alloc_ctor(0, 6, 0);
} else {
 x_199 = x_194;
}
lean_ctor_set(x_199, 0, x_189);
lean_ctor_set(x_199, 1, x_190);
lean_ctor_set(x_199, 2, x_198);
lean_ctor_set(x_199, 3, x_191);
lean_ctor_set(x_199, 4, x_192);
lean_ctor_set(x_199, 5, x_193);
if (lean_is_scalar(x_188)) {
 x_200 = lean_alloc_ctor(0, 6, 0);
} else {
 x_200 = x_188;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_183);
lean_ctor_set(x_200, 2, x_184);
lean_ctor_set(x_200, 3, x_185);
lean_ctor_set(x_200, 4, x_186);
lean_ctor_set(x_200, 5, x_187);
x_201 = lean_ctor_get(x_32, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_202 = x_32;
} else {
 lean_dec_ref(x_32);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_177);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_2);
x_205 = !lean_is_exclusive(x_31);
if (x_205 == 0)
{
return x_31;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_31, 0);
x_207 = lean_ctor_get(x_31, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_31);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_213 = lean_ctor_get(x_7, 0);
x_214 = lean_ctor_get(x_7, 2);
x_215 = lean_ctor_get(x_7, 3);
x_216 = lean_ctor_get(x_7, 4);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_7);
x_217 = lean_ctor_get(x_8, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_8, 4);
lean_inc(x_218);
x_219 = lean_array_get_size(x_214);
x_220 = lean_array_get_size(x_218);
x_221 = lean_nat_dec_eq(x_219, x_220);
lean_dec(x_220);
lean_dec(x_219);
lean_inc(x_218);
x_222 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_222, 0, x_213);
lean_ctor_set(x_222, 1, x_217);
lean_ctor_set(x_222, 2, x_218);
lean_ctor_set(x_222, 3, x_215);
lean_ctor_set(x_222, 4, x_216);
lean_ctor_set(x_6, 0, x_222);
x_223 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_223, 0, x_6);
lean_ctor_set(x_223, 1, x_10);
lean_ctor_set(x_223, 2, x_11);
if (x_221 == 0)
{
uint8_t x_298; 
lean_dec(x_218);
lean_dec(x_214);
lean_dec(x_8);
lean_dec(x_3);
x_298 = 0;
x_224 = x_298;
goto block_297;
}
else
{
lean_object* x_299; uint8_t x_300; 
x_299 = lean_unsigned_to_nat(0u);
x_300 = l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1(x_3, x_8, lean_box(0), x_214, x_218, x_299);
lean_dec(x_218);
lean_dec(x_214);
lean_dec(x_8);
lean_dec(x_3);
x_224 = x_300;
goto block_297;
}
block_297:
{
uint8_t x_225; 
x_225 = l_coeDecidableEq(x_224);
if (x_225 == 0)
{
lean_object* x_226; 
x_226 = lean_apply_2(x_2, x_223, x_9);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_227 = lean_ctor_get(x_9, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
lean_dec(x_227);
x_229 = lean_ctor_get(x_228, 2);
lean_inc(x_229);
lean_dec(x_228);
x_230 = lean_ctor_get(x_229, 2);
lean_inc(x_230);
lean_dec(x_229);
x_231 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_223);
x_232 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_231, x_223, x_9);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
lean_dec(x_232);
x_234 = l_Lean_Elab_Tactic_save(x_233);
lean_inc(x_233);
x_235 = lean_apply_2(x_2, x_223, x_233);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_234);
lean_dec(x_233);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_238, 2);
lean_inc(x_239);
x_240 = lean_ctor_get(x_235, 0);
lean_inc(x_240);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_241 = x_235;
} else {
 lean_dec_ref(x_235);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_236, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_243 = x_236;
} else {
 lean_dec_ref(x_236);
 x_243 = lean_box(0);
}
x_244 = lean_ctor_get(x_237, 1);
lean_inc(x_244);
x_245 = lean_ctor_get(x_237, 2);
lean_inc(x_245);
x_246 = lean_ctor_get(x_237, 3);
lean_inc(x_246);
x_247 = lean_ctor_get(x_237, 4);
lean_inc(x_247);
x_248 = lean_ctor_get(x_237, 5);
lean_inc(x_248);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 lean_ctor_release(x_237, 2);
 lean_ctor_release(x_237, 3);
 lean_ctor_release(x_237, 4);
 lean_ctor_release(x_237, 5);
 x_249 = x_237;
} else {
 lean_dec_ref(x_237);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_238, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_238, 1);
lean_inc(x_251);
x_252 = lean_ctor_get(x_238, 3);
lean_inc(x_252);
x_253 = lean_ctor_get(x_238, 4);
lean_inc(x_253);
x_254 = lean_ctor_get(x_238, 5);
lean_inc(x_254);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 lean_ctor_release(x_238, 2);
 lean_ctor_release(x_238, 3);
 lean_ctor_release(x_238, 4);
 lean_ctor_release(x_238, 5);
 x_255 = x_238;
} else {
 lean_dec_ref(x_238);
 x_255 = lean_box(0);
}
x_256 = lean_ctor_get(x_239, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_239, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 lean_ctor_release(x_239, 2);
 x_258 = x_239;
} else {
 lean_dec_ref(x_239);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(0, 3, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
lean_ctor_set(x_259, 2, x_230);
if (lean_is_scalar(x_255)) {
 x_260 = lean_alloc_ctor(0, 6, 0);
} else {
 x_260 = x_255;
}
lean_ctor_set(x_260, 0, x_250);
lean_ctor_set(x_260, 1, x_251);
lean_ctor_set(x_260, 2, x_259);
lean_ctor_set(x_260, 3, x_252);
lean_ctor_set(x_260, 4, x_253);
lean_ctor_set(x_260, 5, x_254);
if (lean_is_scalar(x_249)) {
 x_261 = lean_alloc_ctor(0, 6, 0);
} else {
 x_261 = x_249;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_244);
lean_ctor_set(x_261, 2, x_245);
lean_ctor_set(x_261, 3, x_246);
lean_ctor_set(x_261, 4, x_247);
lean_ctor_set(x_261, 5, x_248);
if (lean_is_scalar(x_243)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_243;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_242);
if (lean_is_scalar(x_241)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_241;
}
lean_ctor_set(x_263, 0, x_240);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_264 = lean_ctor_get(x_235, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_235, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_266 = x_235;
} else {
 lean_dec_ref(x_235);
 x_266 = lean_box(0);
}
x_267 = l_Lean_Elab_Tactic_restore(x_265, x_234);
lean_dec(x_234);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
lean_dec(x_267);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_269, 2);
lean_inc(x_270);
x_271 = lean_ctor_get(x_268, 1);
lean_inc(x_271);
x_272 = lean_ctor_get(x_268, 2);
lean_inc(x_272);
x_273 = lean_ctor_get(x_268, 3);
lean_inc(x_273);
x_274 = lean_ctor_get(x_268, 4);
lean_inc(x_274);
x_275 = lean_ctor_get(x_268, 5);
lean_inc(x_275);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 lean_ctor_release(x_268, 2);
 lean_ctor_release(x_268, 3);
 lean_ctor_release(x_268, 4);
 lean_ctor_release(x_268, 5);
 x_276 = x_268;
} else {
 lean_dec_ref(x_268);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_269, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_269, 1);
lean_inc(x_278);
x_279 = lean_ctor_get(x_269, 3);
lean_inc(x_279);
x_280 = lean_ctor_get(x_269, 4);
lean_inc(x_280);
x_281 = lean_ctor_get(x_269, 5);
lean_inc(x_281);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 lean_ctor_release(x_269, 2);
 lean_ctor_release(x_269, 3);
 lean_ctor_release(x_269, 4);
 lean_ctor_release(x_269, 5);
 x_282 = x_269;
} else {
 lean_dec_ref(x_269);
 x_282 = lean_box(0);
}
x_283 = lean_ctor_get(x_270, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_270, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 lean_ctor_release(x_270, 2);
 x_285 = x_270;
} else {
 lean_dec_ref(x_270);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(0, 3, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_284);
lean_ctor_set(x_286, 2, x_230);
if (lean_is_scalar(x_282)) {
 x_287 = lean_alloc_ctor(0, 6, 0);
} else {
 x_287 = x_282;
}
lean_ctor_set(x_287, 0, x_277);
lean_ctor_set(x_287, 1, x_278);
lean_ctor_set(x_287, 2, x_286);
lean_ctor_set(x_287, 3, x_279);
lean_ctor_set(x_287, 4, x_280);
lean_ctor_set(x_287, 5, x_281);
if (lean_is_scalar(x_276)) {
 x_288 = lean_alloc_ctor(0, 6, 0);
} else {
 x_288 = x_276;
}
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_271);
lean_ctor_set(x_288, 2, x_272);
lean_ctor_set(x_288, 3, x_273);
lean_ctor_set(x_288, 4, x_274);
lean_ctor_set(x_288, 5, x_275);
x_289 = lean_ctor_get(x_233, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_290 = x_233;
} else {
 lean_dec_ref(x_233);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_289);
if (lean_is_scalar(x_266)) {
 x_292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_292 = x_266;
}
lean_ctor_set(x_292, 0, x_264);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_230);
lean_dec(x_223);
lean_dec(x_2);
x_293 = lean_ctor_get(x_232, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_232, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_295 = x_232;
} else {
 lean_dec_ref(x_232);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_293);
lean_ctor_set(x_296, 1, x_294);
return x_296;
}
}
}
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; 
x_301 = lean_ctor_get(x_6, 1);
x_302 = lean_ctor_get(x_6, 2);
x_303 = lean_ctor_get(x_6, 3);
x_304 = lean_ctor_get(x_6, 4);
x_305 = lean_ctor_get(x_6, 5);
x_306 = lean_ctor_get(x_6, 6);
x_307 = lean_ctor_get(x_6, 7);
x_308 = lean_ctor_get(x_6, 8);
x_309 = lean_ctor_get(x_6, 9);
x_310 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_311 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
lean_inc(x_309);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_306);
lean_inc(x_305);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_6);
x_312 = lean_ctor_get(x_7, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_7, 2);
lean_inc(x_313);
x_314 = lean_ctor_get(x_7, 3);
lean_inc(x_314);
x_315 = lean_ctor_get(x_7, 4);
lean_inc(x_315);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 x_316 = x_7;
} else {
 lean_dec_ref(x_7);
 x_316 = lean_box(0);
}
x_317 = lean_ctor_get(x_8, 1);
lean_inc(x_317);
x_318 = lean_ctor_get(x_8, 4);
lean_inc(x_318);
x_319 = lean_array_get_size(x_313);
x_320 = lean_array_get_size(x_318);
x_321 = lean_nat_dec_eq(x_319, x_320);
lean_dec(x_320);
lean_dec(x_319);
lean_inc(x_318);
if (lean_is_scalar(x_316)) {
 x_322 = lean_alloc_ctor(0, 5, 0);
} else {
 x_322 = x_316;
}
lean_ctor_set(x_322, 0, x_312);
lean_ctor_set(x_322, 1, x_317);
lean_ctor_set(x_322, 2, x_318);
lean_ctor_set(x_322, 3, x_314);
lean_ctor_set(x_322, 4, x_315);
x_323 = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_301);
lean_ctor_set(x_323, 2, x_302);
lean_ctor_set(x_323, 3, x_303);
lean_ctor_set(x_323, 4, x_304);
lean_ctor_set(x_323, 5, x_305);
lean_ctor_set(x_323, 6, x_306);
lean_ctor_set(x_323, 7, x_307);
lean_ctor_set(x_323, 8, x_308);
lean_ctor_set(x_323, 9, x_309);
lean_ctor_set_uint8(x_323, sizeof(void*)*10, x_310);
lean_ctor_set_uint8(x_323, sizeof(void*)*10 + 1, x_311);
x_324 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_10);
lean_ctor_set(x_324, 2, x_11);
if (x_321 == 0)
{
uint8_t x_399; 
lean_dec(x_318);
lean_dec(x_313);
lean_dec(x_8);
lean_dec(x_3);
x_399 = 0;
x_325 = x_399;
goto block_398;
}
else
{
lean_object* x_400; uint8_t x_401; 
x_400 = lean_unsigned_to_nat(0u);
x_401 = l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1(x_3, x_8, lean_box(0), x_313, x_318, x_400);
lean_dec(x_318);
lean_dec(x_313);
lean_dec(x_8);
lean_dec(x_3);
x_325 = x_401;
goto block_398;
}
block_398:
{
uint8_t x_326; 
x_326 = l_coeDecidableEq(x_325);
if (x_326 == 0)
{
lean_object* x_327; 
x_327 = lean_apply_2(x_2, x_324, x_9);
return x_327;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_328 = lean_ctor_get(x_9, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
lean_dec(x_328);
x_330 = lean_ctor_get(x_329, 2);
lean_inc(x_330);
lean_dec(x_329);
x_331 = lean_ctor_get(x_330, 2);
lean_inc(x_331);
lean_dec(x_330);
x_332 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_324);
x_333 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_332, x_324, x_9);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
lean_dec(x_333);
x_335 = l_Lean_Elab_Tactic_save(x_334);
lean_inc(x_334);
x_336 = lean_apply_2(x_2, x_324, x_334);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_335);
lean_dec(x_334);
x_337 = lean_ctor_get(x_336, 1);
lean_inc(x_337);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_339, 2);
lean_inc(x_340);
x_341 = lean_ctor_get(x_336, 0);
lean_inc(x_341);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_342 = x_336;
} else {
 lean_dec_ref(x_336);
 x_342 = lean_box(0);
}
x_343 = lean_ctor_get(x_337, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_344 = x_337;
} else {
 lean_dec_ref(x_337);
 x_344 = lean_box(0);
}
x_345 = lean_ctor_get(x_338, 1);
lean_inc(x_345);
x_346 = lean_ctor_get(x_338, 2);
lean_inc(x_346);
x_347 = lean_ctor_get(x_338, 3);
lean_inc(x_347);
x_348 = lean_ctor_get(x_338, 4);
lean_inc(x_348);
x_349 = lean_ctor_get(x_338, 5);
lean_inc(x_349);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 lean_ctor_release(x_338, 4);
 lean_ctor_release(x_338, 5);
 x_350 = x_338;
} else {
 lean_dec_ref(x_338);
 x_350 = lean_box(0);
}
x_351 = lean_ctor_get(x_339, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_339, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_339, 3);
lean_inc(x_353);
x_354 = lean_ctor_get(x_339, 4);
lean_inc(x_354);
x_355 = lean_ctor_get(x_339, 5);
lean_inc(x_355);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 lean_ctor_release(x_339, 2);
 lean_ctor_release(x_339, 3);
 lean_ctor_release(x_339, 4);
 lean_ctor_release(x_339, 5);
 x_356 = x_339;
} else {
 lean_dec_ref(x_339);
 x_356 = lean_box(0);
}
x_357 = lean_ctor_get(x_340, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_340, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 x_359 = x_340;
} else {
 lean_dec_ref(x_340);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(0, 3, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_358);
lean_ctor_set(x_360, 2, x_331);
if (lean_is_scalar(x_356)) {
 x_361 = lean_alloc_ctor(0, 6, 0);
} else {
 x_361 = x_356;
}
lean_ctor_set(x_361, 0, x_351);
lean_ctor_set(x_361, 1, x_352);
lean_ctor_set(x_361, 2, x_360);
lean_ctor_set(x_361, 3, x_353);
lean_ctor_set(x_361, 4, x_354);
lean_ctor_set(x_361, 5, x_355);
if (lean_is_scalar(x_350)) {
 x_362 = lean_alloc_ctor(0, 6, 0);
} else {
 x_362 = x_350;
}
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_345);
lean_ctor_set(x_362, 2, x_346);
lean_ctor_set(x_362, 3, x_347);
lean_ctor_set(x_362, 4, x_348);
lean_ctor_set(x_362, 5, x_349);
if (lean_is_scalar(x_344)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_344;
}
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_343);
if (lean_is_scalar(x_342)) {
 x_364 = lean_alloc_ctor(0, 2, 0);
} else {
 x_364 = x_342;
}
lean_ctor_set(x_364, 0, x_341);
lean_ctor_set(x_364, 1, x_363);
return x_364;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_365 = lean_ctor_get(x_336, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_336, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_367 = x_336;
} else {
 lean_dec_ref(x_336);
 x_367 = lean_box(0);
}
x_368 = l_Lean_Elab_Tactic_restore(x_366, x_335);
lean_dec(x_335);
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
lean_dec(x_368);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_370, 2);
lean_inc(x_371);
x_372 = lean_ctor_get(x_369, 1);
lean_inc(x_372);
x_373 = lean_ctor_get(x_369, 2);
lean_inc(x_373);
x_374 = lean_ctor_get(x_369, 3);
lean_inc(x_374);
x_375 = lean_ctor_get(x_369, 4);
lean_inc(x_375);
x_376 = lean_ctor_get(x_369, 5);
lean_inc(x_376);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 lean_ctor_release(x_369, 2);
 lean_ctor_release(x_369, 3);
 lean_ctor_release(x_369, 4);
 lean_ctor_release(x_369, 5);
 x_377 = x_369;
} else {
 lean_dec_ref(x_369);
 x_377 = lean_box(0);
}
x_378 = lean_ctor_get(x_370, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_370, 1);
lean_inc(x_379);
x_380 = lean_ctor_get(x_370, 3);
lean_inc(x_380);
x_381 = lean_ctor_get(x_370, 4);
lean_inc(x_381);
x_382 = lean_ctor_get(x_370, 5);
lean_inc(x_382);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 lean_ctor_release(x_370, 2);
 lean_ctor_release(x_370, 3);
 lean_ctor_release(x_370, 4);
 lean_ctor_release(x_370, 5);
 x_383 = x_370;
} else {
 lean_dec_ref(x_370);
 x_383 = lean_box(0);
}
x_384 = lean_ctor_get(x_371, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_371, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 x_386 = x_371;
} else {
 lean_dec_ref(x_371);
 x_386 = lean_box(0);
}
if (lean_is_scalar(x_386)) {
 x_387 = lean_alloc_ctor(0, 3, 0);
} else {
 x_387 = x_386;
}
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_385);
lean_ctor_set(x_387, 2, x_331);
if (lean_is_scalar(x_383)) {
 x_388 = lean_alloc_ctor(0, 6, 0);
} else {
 x_388 = x_383;
}
lean_ctor_set(x_388, 0, x_378);
lean_ctor_set(x_388, 1, x_379);
lean_ctor_set(x_388, 2, x_387);
lean_ctor_set(x_388, 3, x_380);
lean_ctor_set(x_388, 4, x_381);
lean_ctor_set(x_388, 5, x_382);
if (lean_is_scalar(x_377)) {
 x_389 = lean_alloc_ctor(0, 6, 0);
} else {
 x_389 = x_377;
}
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_372);
lean_ctor_set(x_389, 2, x_373);
lean_ctor_set(x_389, 3, x_374);
lean_ctor_set(x_389, 4, x_375);
lean_ctor_set(x_389, 5, x_376);
x_390 = lean_ctor_get(x_334, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_391 = x_334;
} else {
 lean_dec_ref(x_334);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_390);
if (lean_is_scalar(x_367)) {
 x_393 = lean_alloc_ctor(1, 2, 0);
} else {
 x_393 = x_367;
}
lean_ctor_set(x_393, 0, x_365);
lean_ctor_set(x_393, 1, x_392);
return x_393;
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_331);
lean_dec(x_324);
lean_dec(x_2);
x_394 = lean_ctor_get(x_333, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_333, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_396 = x_333;
} else {
 lean_dec_ref(x_333);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 2, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_394);
lean_ctor_set(x_397, 1, x_395);
return x_397;
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_Expr_hasMVar(x_7);
x_10 = l_coeDecidableEq(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_box(0);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_5);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_7);
x_13 = l_Lean_indentExpr(x_12);
x_14 = l_Lean_Elab_Tactic_ensureHasNoMVars___closed__3;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_15, x_3, x_8);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = l_Lean_Expr_hasMVar(x_17);
x_20 = l_coeDecidableEq(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_17);
x_24 = l_Lean_indentExpr(x_23);
x_25 = l_Lean_Elab_Tactic_ensureHasNoMVars___closed__3;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_26, x_3, x_18);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
return x_5;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_List_isEmpty___rarg(x_6);
x_9 = l_coeDecidableEq(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_free_object(x_4);
x_10 = l_Lean_Elab_Tactic_reportUnsolvedGoals(x_1, x_6, x_2, x_7);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = l_List_isEmpty___rarg(x_12);
x_15 = l_coeDecidableEq(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Tactic_reportUnsolvedGoals(x_1, x_12, x_2, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
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
x_10 = l_coeDecidableEq(x_9);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_4 = x_6;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_3, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_3, 0);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_2);
x_15 = l_Lean_Name_appendIndexAfter(x_2, x_8);
x_16 = l_Lean_Name_append___main(x_1, x_15);
x_17 = l_Lean_MetavarContext_renameMVar(x_7, x_5, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_8, x_18);
lean_dec(x_8);
lean_ctor_set(x_3, 1, x_19);
lean_ctor_set(x_3, 0, x_17);
x_4 = x_6;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
lean_inc(x_8);
lean_inc(x_2);
x_21 = l_Lean_Name_appendIndexAfter(x_2, x_8);
x_22 = l_Lean_Name_append___main(x_1, x_21);
x_23 = l_Lean_MetavarContext_renameMVar(x_7, x_5, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_8, x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_3 = x_26;
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
lean_object* x_91; uint8_t x_92; uint8_t x_93; 
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_inc(x_91);
x_92 = l_Lean_MetavarContext_isAnonymousMVar(x_91, x_85);
x_93 = l_coeDecidableEq(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_85);
lean_dec(x_1);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_7);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = l_Lean_MetavarContext_renameMVar(x_91, x_85, x_1);
lean_ctor_set(x_84, 1, x_96);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_7);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; 
x_99 = lean_ctor_get(x_84, 0);
x_100 = lean_ctor_get(x_84, 1);
x_101 = lean_ctor_get(x_84, 2);
x_102 = lean_ctor_get(x_84, 3);
x_103 = lean_ctor_get(x_84, 4);
x_104 = lean_ctor_get(x_84, 5);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_84);
lean_inc(x_85);
lean_inc(x_100);
x_105 = l_Lean_MetavarContext_isAnonymousMVar(x_100, x_85);
x_106 = l_coeDecidableEq(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_85);
lean_dec(x_1);
x_107 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_107, 0, x_99);
lean_ctor_set(x_107, 1, x_100);
lean_ctor_set(x_107, 2, x_101);
lean_ctor_set(x_107, 3, x_102);
lean_ctor_set(x_107, 4, x_103);
lean_ctor_set(x_107, 5, x_104);
lean_ctor_set(x_83, 0, x_107);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_7);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = l_Lean_MetavarContext_renameMVar(x_100, x_85, x_1);
x_111 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_111, 0, x_99);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_111, 2, x_101);
lean_ctor_set(x_111, 3, x_102);
lean_ctor_set(x_111, 4, x_103);
lean_ctor_set(x_111, 5, x_104);
lean_ctor_set(x_83, 0, x_111);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_7);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_127; 
x_114 = lean_ctor_get(x_83, 1);
x_115 = lean_ctor_get(x_83, 2);
x_116 = lean_ctor_get(x_83, 3);
x_117 = lean_ctor_get(x_83, 4);
x_118 = lean_ctor_get(x_83, 5);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_83);
x_119 = lean_ctor_get(x_84, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_84, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_84, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_84, 3);
lean_inc(x_122);
x_123 = lean_ctor_get(x_84, 4);
lean_inc(x_123);
x_124 = lean_ctor_get(x_84, 5);
lean_inc(x_124);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 lean_ctor_release(x_84, 2);
 lean_ctor_release(x_84, 3);
 lean_ctor_release(x_84, 4);
 lean_ctor_release(x_84, 5);
 x_125 = x_84;
} else {
 lean_dec_ref(x_84);
 x_125 = lean_box(0);
}
lean_inc(x_85);
lean_inc(x_120);
x_126 = l_Lean_MetavarContext_isAnonymousMVar(x_120, x_85);
x_127 = l_coeDecidableEq(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_85);
lean_dec(x_1);
if (lean_is_scalar(x_125)) {
 x_128 = lean_alloc_ctor(0, 6, 0);
} else {
 x_128 = x_125;
}
lean_ctor_set(x_128, 0, x_119);
lean_ctor_set(x_128, 1, x_120);
lean_ctor_set(x_128, 2, x_121);
lean_ctor_set(x_128, 3, x_122);
lean_ctor_set(x_128, 4, x_123);
lean_ctor_set(x_128, 5, x_124);
x_129 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_114);
lean_ctor_set(x_129, 2, x_115);
lean_ctor_set(x_129, 3, x_116);
lean_ctor_set(x_129, 4, x_117);
lean_ctor_set(x_129, 5, x_118);
lean_ctor_set(x_7, 0, x_129);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_7);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = l_Lean_MetavarContext_renameMVar(x_120, x_85, x_1);
if (lean_is_scalar(x_125)) {
 x_133 = lean_alloc_ctor(0, 6, 0);
} else {
 x_133 = x_125;
}
lean_ctor_set(x_133, 0, x_119);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set(x_133, 2, x_121);
lean_ctor_set(x_133, 3, x_122);
lean_ctor_set(x_133, 4, x_123);
lean_ctor_set(x_133, 5, x_124);
x_134 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_114);
lean_ctor_set(x_134, 2, x_115);
lean_ctor_set(x_134, 3, x_116);
lean_ctor_set(x_134, 4, x_117);
lean_ctor_set(x_134, 5, x_118);
lean_ctor_set(x_7, 0, x_134);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_7);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_152; 
x_137 = lean_ctor_get(x_7, 1);
lean_inc(x_137);
lean_dec(x_7);
x_138 = lean_ctor_get(x_83, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_83, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_83, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_83, 4);
lean_inc(x_141);
x_142 = lean_ctor_get(x_83, 5);
lean_inc(x_142);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 lean_ctor_release(x_83, 2);
 lean_ctor_release(x_83, 3);
 lean_ctor_release(x_83, 4);
 lean_ctor_release(x_83, 5);
 x_143 = x_83;
} else {
 lean_dec_ref(x_83);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_84, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_84, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_84, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_84, 3);
lean_inc(x_147);
x_148 = lean_ctor_get(x_84, 4);
lean_inc(x_148);
x_149 = lean_ctor_get(x_84, 5);
lean_inc(x_149);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 lean_ctor_release(x_84, 2);
 lean_ctor_release(x_84, 3);
 lean_ctor_release(x_84, 4);
 lean_ctor_release(x_84, 5);
 x_150 = x_84;
} else {
 lean_dec_ref(x_84);
 x_150 = lean_box(0);
}
lean_inc(x_85);
lean_inc(x_145);
x_151 = l_Lean_MetavarContext_isAnonymousMVar(x_145, x_85);
x_152 = l_coeDecidableEq(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_85);
lean_dec(x_1);
if (lean_is_scalar(x_150)) {
 x_153 = lean_alloc_ctor(0, 6, 0);
} else {
 x_153 = x_150;
}
lean_ctor_set(x_153, 0, x_144);
lean_ctor_set(x_153, 1, x_145);
lean_ctor_set(x_153, 2, x_146);
lean_ctor_set(x_153, 3, x_147);
lean_ctor_set(x_153, 4, x_148);
lean_ctor_set(x_153, 5, x_149);
if (lean_is_scalar(x_143)) {
 x_154 = lean_alloc_ctor(0, 6, 0);
} else {
 x_154 = x_143;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_138);
lean_ctor_set(x_154, 2, x_139);
lean_ctor_set(x_154, 3, x_140);
lean_ctor_set(x_154, 4, x_141);
lean_ctor_set(x_154, 5, x_142);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_137);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_158 = l_Lean_MetavarContext_renameMVar(x_145, x_85, x_1);
if (lean_is_scalar(x_150)) {
 x_159 = lean_alloc_ctor(0, 6, 0);
} else {
 x_159 = x_150;
}
lean_ctor_set(x_159, 0, x_144);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set(x_159, 2, x_146);
lean_ctor_set(x_159, 3, x_147);
lean_ctor_set(x_159, 4, x_148);
lean_ctor_set(x_159, 5, x_149);
if (lean_is_scalar(x_143)) {
 x_160 = lean_alloc_ctor(0, 6, 0);
} else {
 x_160 = x_143;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_138);
lean_ctor_set(x_160, 2, x_139);
lean_ctor_set(x_160, 3, x_140);
lean_ctor_set(x_160, 4, x_141);
lean_ctor_set(x_160, 5, x_142);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_137);
x_162 = lean_box(0);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
}
else
{
lean_object* x_164; 
lean_dec(x_82);
x_164 = lean_box(0);
x_9 = x_164;
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
uint8_t x_4; lean_object* x_73; uint8_t x_74; 
x_73 = l_Lean_Parser_Tactic_intro___elambda__1___closed__2;
lean_inc(x_1);
x_74 = l_Lean_Syntax_isOfKind(x_1, x_73);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = 0;
x_4 = x_75;
goto block_72;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = l_Lean_Syntax_getArgs(x_1);
x_77 = lean_array_get_size(x_76);
lean_dec(x_76);
x_78 = lean_unsigned_to_nat(2u);
x_79 = lean_nat_dec_eq(x_77, x_78);
lean_dec(x_77);
x_4 = x_79;
goto block_72;
}
block_72:
{
uint8_t x_5; 
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = l_Lean_nullKind___closed__2;
lean_inc(x_8);
x_10 = l_Lean_Syntax_isOfKind(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_67; 
x_67 = 0;
x_11 = x_67;
goto block_66;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = l_Lean_Syntax_getArgs(x_8);
x_69 = lean_array_get_size(x_68);
lean_dec(x_68);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_nat_dec_eq(x_69, x_70);
lean_dec(x_69);
x_11 = x_71;
goto block_66;
}
block_66:
{
uint8_t x_12; 
x_12 = l_coeDecidableEq(x_11);
if (x_12 == 0)
{
if (x_10 == 0)
{
uint8_t x_13; 
x_13 = l_String_posOfAux___main___closed__1;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_1);
x_14 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getArg(x_8, x_15);
lean_dec(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntro___lambda__1___boxed), 4, 2);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 4, 1);
lean_closure_set(x_24, 0, x_21);
x_25 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_24);
x_26 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_20, x_25, x_2, x_19);
lean_dec(x_20);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
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
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; 
x_31 = l_Lean_Syntax_getArgs(x_8);
x_32 = lean_array_get_size(x_31);
lean_dec(x_31);
x_33 = lean_nat_dec_eq(x_32, x_7);
lean_dec(x_32);
x_34 = l_coeDecidableEq(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_8);
lean_dec(x_1);
x_35 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_Syntax_getArg(x_8, x_36);
lean_dec(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_38 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
lean_inc(x_41);
x_43 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntro___lambda__1___boxed), 4, 2);
lean_closure_set(x_43, 0, x_37);
lean_closure_set(x_43, 1, x_41);
x_44 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_44, 0, x_1);
lean_closure_set(x_44, 1, x_43);
x_45 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 4, 1);
lean_closure_set(x_45, 0, x_42);
x_46 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_46, 0, x_44);
lean_closure_set(x_46, 1, x_45);
x_47 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_41, x_46, x_2, x_40);
lean_dec(x_41);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_37);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
else
{
lean_object* x_52; 
lean_dec(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_52 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
lean_inc(x_55);
x_57 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntro___lambda__2___boxed), 3, 1);
lean_closure_set(x_57, 0, x_55);
x_58 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_58, 0, x_1);
lean_closure_set(x_58, 1, x_57);
x_59 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 4, 1);
lean_closure_set(x_59, 0, x_56);
x_60 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_60, 0, x_58);
lean_closure_set(x_60, 1, x_59);
x_61 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_55, x_60, x_2, x_54);
lean_dec(x_55);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec(x_2);
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
uint8_t x_4; lean_object* x_49; uint8_t x_50; 
x_49 = l_Lean_Parser_Tactic_intros___elambda__1___closed__2;
lean_inc(x_1);
x_50 = l_Lean_Syntax_isOfKind(x_1, x_49);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = 0;
x_4 = x_51;
goto block_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = l_Lean_Syntax_getArgs(x_1);
x_53 = lean_array_get_size(x_52);
lean_dec(x_52);
x_54 = lean_unsigned_to_nat(2u);
x_55 = lean_nat_dec_eq(x_53, x_54);
lean_dec(x_53);
x_4 = x_55;
goto block_48;
}
block_48:
{
uint8_t x_5; 
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_41; uint8_t x_42; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_41 = l_Lean_nullKind___closed__2;
lean_inc(x_8);
x_42 = l_Lean_Syntax_isOfKind(x_8, x_41);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = 0;
x_9 = x_43;
goto block_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = l_Lean_Syntax_getArgs(x_8);
x_45 = lean_array_get_size(x_44);
lean_dec(x_44);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_eq(x_45, x_46);
lean_dec(x_45);
x_9 = x_47;
goto block_40;
}
block_40:
{
uint8_t x_10; 
x_10 = l_coeDecidableEq(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntros___lambda__1___boxed), 4, 2);
lean_closure_set(x_17, 0, x_11);
lean_closure_set(x_17, 1, x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 4, 1);
lean_closure_set(x_19, 0, x_16);
x_20 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_15, x_20, x_2, x_14);
lean_dec(x_15);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_26; 
lean_dec(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_26 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_32, 0, x_1);
lean_closure_set(x_32, 1, x_31);
x_33 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 4, 1);
lean_closure_set(x_33, 0, x_30);
x_34 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_34, 0, x_32);
lean_closure_set(x_34, 1, x_33);
x_35 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_29, x_34, x_2, x_28);
lean_dec(x_29);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
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
uint8_t x_4; lean_object* x_45; uint8_t x_46; 
x_45 = l_Lean_Parser_Tactic_case___elambda__1___closed__2;
lean_inc(x_1);
x_46 = l_Lean_Syntax_isOfKind(x_1, x_45);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = 0;
x_4 = x_47;
goto block_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = l_Lean_Syntax_getArgs(x_1);
x_49 = lean_array_get_size(x_48);
lean_dec(x_48);
x_50 = lean_unsigned_to_nat(3u);
x_51 = lean_nat_dec_eq(x_49, x_50);
lean_dec(x_49);
x_4 = x_51;
goto block_44;
}
block_44:
{
uint8_t x_5; 
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_getId(x_8);
lean_dec(x_8);
lean_inc(x_2);
x_12 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_findM_x3f___main___at_Lean_Elab_Tactic_evalCase___spec__1(x_11, x_13, x_2, x_14);
lean_dec(x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_10);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Tactic_evalCase___closed__3;
x_19 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_18, x_2, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__2(x_13, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_Tactic_setGoals(x_24, x_2, x_20);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_2);
x_27 = l_Lean_Elab_Tactic_evalTactic___main(x_10, x_2, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_2);
x_29 = l_Lean_Elab_Tactic_done(x_1, x_2, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Elab_Tactic_setGoals(x_22, x_2, x_30);
lean_dec(x_2);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_22);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
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
lean_dec(x_22);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
return x_27;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_27);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_12);
if (x_40 == 0)
{
return x_12;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
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
uint8_t x_6; 
x_6 = l_String_posOfAux___main___closed__1;
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_save(x_3);
lean_inc(x_2);
x_13 = l_Lean_Elab_Tactic_evalTactic___main(x_9, x_2, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Elab_Tactic_restore(x_14, x_12);
lean_dec(x_12);
x_16 = l_Lean_Elab_Tactic_evalTactic___main(x_11, x_2, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_17 = l_Lean_Syntax_getArgs(x_1);
x_18 = lean_array_get_size(x_17);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(3u);
x_20 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_18);
x_21 = l_coeDecidableEq(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
x_25 = lean_unsigned_to_nat(2u);
x_26 = l_Lean_Syntax_getArg(x_1, x_25);
lean_dec(x_1);
x_27 = l_Lean_Elab_Tactic_save(x_3);
lean_inc(x_2);
x_28 = l_Lean_Elab_Tactic_evalTactic___main(x_24, x_2, x_3);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_2);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Elab_Tactic_restore(x_29, x_27);
lean_dec(x_27);
x_31 = l_Lean_Elab_Tactic_evalTactic___main(x_26, x_2, x_30);
return x_31;
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
