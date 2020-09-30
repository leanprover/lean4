// Lean compiler output
// Module: Lean.Elab.Tactic.Basic
// Imports: Init Lean.Util.CollectMVars Lean.Meta.Tactic.Assumption Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Clear Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Subst Lean.Elab.Util Lean.Elab.Term Lean.Elab.Binders
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
extern lean_object* l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__4;
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__9;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalTactic___main___spec__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_evalClear___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntroMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__1;
lean_object* l_Lean_Elab_Tactic_getMainTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__8;
lean_object* l___private_Lean_Elab_Tactic_Basic_3__introStep___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__3;
lean_object* lean_nat_div(lean_object*, lean_object*);
extern lean_object* l_Lean_KeyedDeclsAttribute_KeyedDeclsAttribute_inhabited___closed__1;
lean_object* l_Lean_Elab_Tactic_evalTacticSeq1Indented(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l_Lean_Elab_Tactic_evalIntros___closed__1;
lean_object* l_Lean_Elab_Tactic_withMainMVarContext(lean_object*);
extern lean_object* l_Lean_nullKind;
extern lean_object* l_Lean_mkThunk___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Basic_4__getIntrosSize___main(lean_object*);
lean_object* l_Lean_Elab_Tactic_monadExcept___closed__2;
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_goalsToMessageData___spec__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSkip___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_catch(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1___rarg(lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l___private_Lean_Elab_Util_6__regTraceClasses___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_evalClear___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadExcept___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Tactic_evalTactic___main___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalChoiceAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_4__getIntrosSize___boxed(lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSkip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focus___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadExcept___closed__1;
lean_object* l_Lean_Elab_Tactic_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_appendGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__2;
lean_object* l_Lean_Elab_Tactic_focus(lean_object*);
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_3__introStep___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__6;
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__4;
lean_object* l_Lean_Elab_Tactic_liftMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCase___closed__1;
lean_object* l_Lean_Elab_Tactic_done(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticSeq1Indented___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_forEachVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BacktrackableState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___closed__2;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_clear___lambda__1___closed__6;
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_findM_x3f___main___at___private_Lean_Elab_Tactic_Basic_6__findTag_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_goalsToMessageData___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg(lean_object*);
lean_object* l_List_findM_x3f___main___at___private_Lean_Elab_Tactic_Basic_6__findTag_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveAllState(lean_object*);
lean_object* l_ReaderT_Monad___rarg(lean_object*);
lean_object* l_Lean_Meta_subst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_32__withMVarContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_ensureHasType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCase___closed__5;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__3;
lean_object* l_Lean_Elab_Tactic_evalCase___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___closed__1;
lean_object* l_Lean_Meta_getMVars___at_Lean_Elab_Tactic_ensureHasNoMVars___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_CheckAssignment_checkFVar___closed__12;
extern lean_object* l_Lean_Meta_throwTacticEx___rarg___closed__3;
lean_object* l_Lean_Elab_Tactic_getGoals___boxed(lean_object*);
extern lean_object* l_Lean_Name_inhabited;
lean_object* l___private_Lean_Elab_Tactic_Basic_7__regTraceClasses___closed__1;
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__9;
lean_object* l_Lean_Elab_Tactic_evalDone___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented(lean_object*);
lean_object* l_Lean_MetavarContext_renameMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__3;
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__4;
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_evalClear___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro___closed__7;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Elab_Tactic_hasOrElse(lean_object*);
lean_object* l_Lean_Elab_Tactic_orelse(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTraceState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_done___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadExcept;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__1;
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__1;
extern lean_object* l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__17;
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_State_inhabited___closed__7;
lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__12;
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_substCore___lambda__5___closed__1;
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Elab_Tactic_getMainTag___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___closed__2;
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTactic___main___spec__10(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_8__letBindRhss___main___closed__13;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalClear(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__1;
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__2;
lean_object* l_Lean_Meta_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAssumption(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
lean_object* l_Lean_Elab_Tactic_try_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticSeqBracketed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_TacticM_run_x27(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__1;
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCase___closed__4;
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__1;
extern lean_object* l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__14;
lean_object* l_Lean_Elab_Tactic_evalCase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__1;
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadExcept___closed__3;
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__19;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_7__regTraceClasses(lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprMVarAssigned___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg___closed__1;
lean_object* l_Lean_Meta_setMCtx___at_Lean_Elab_Tactic_BacktrackableState_restore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTraceState(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__3;
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__2;
lean_object* l_Lean_Elab_Tactic_evalIntro___closed__3;
extern lean_object* l_Lean_Meta_clear___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__11;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalChoice(lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focus___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind___closed__2;
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__7;
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveBacktrackableState___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_11__elabUsingElabFns___closed__6;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq(lean_object*);
lean_object* l_Lean_Elab_Tactic_TacticM_run(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__1;
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_inhabited;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic___main___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__3;
lean_object* l_Lean_Elab_Tactic_evalSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSkip(lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalDone___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MonadCacheT_MonadLift___closed__1;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalDone___boxed(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftTermElabM(lean_object*);
lean_object* l_Lean_Elab_Tactic_getGoals___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveAllState___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDone(lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__2;
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__7;
uint8_t l_Lean_Name_isPrefixOf___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getGoals___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__1;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___closed__1;
lean_object* l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__1;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__2;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalChoice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__6;
lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalParen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSeq1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainModule___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_3__introStep___closed__1;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_SavedState_inhabited___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSubst(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__1(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_evalClear___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalChoice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntros(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTraceState(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__1;
lean_object* l_Lean_Elab_Tactic_evalIntro___closed__2;
lean_object* l_Lean_Elab_Tactic_saveBacktrackableState___boxed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Meta_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_Lean_Ref;
lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess___closed__2;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic___main___spec__8___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
lean_object* l_List_findM_x3f___main___at___private_Lean_Elab_Tactic_Basic_6__findTag_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalOrelse___closed__1;
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__4;
lean_object* l___private_Lean_Elab_Tactic_Basic_6__findTag_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaM(lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Elab_Tactic_SavedState_inhabited___closed__1;
lean_object* l_Lean_Elab_Tactic_reportUnsolvedGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveAllState___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_State_inhabited;
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_try___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTactic___main___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprMVarAssigned___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_evalOrelse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalAssumption___boxed(lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__12;
lean_object* l_Lean_Elab_Tactic_forEachVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Tactic_evalRevert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFocus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Tactic_ensureHasNoMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_revert___lambda__1___closed__1;
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__10;
extern lean_object* l_Lean_Meta_CheckAssignment_checkFVar___closed__14;
lean_object* l_Lean_Elab_Tactic_evalIntros___closed__2;
lean_object* l_Lean_Elab_Tactic_appendGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveBacktrackableState(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__1;
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__5;
extern lean_object* l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__16;
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__16;
lean_object* l_Lean_Elab_goalsToMessageData(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_isAnonymousMVar(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSeq1(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Basic_4__getIntrosSize___main___boxed(lean_object*);
extern lean_object* l_ReaderT_MonadLift___closed__1;
lean_object* l_Lean_Elab_Tactic_evalParen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_assumptionAux___closed__1;
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Elab_Tactic_liftMetaTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___closed__1;
extern lean_object* l_Lean_Core_State_inhabited___closed__2;
lean_object* l_Lean_Elab_Tactic_liftTermElabM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFocus(lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__1;
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSubst___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__3;
lean_object* l___private_Lean_Elab_Util_5__expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalRevert___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2(lean_object*);
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__2;
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focusAux(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro___closed__4;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Tactic_evalTactic___main___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro___closed__1;
lean_object* l_Lean_Elab_Tactic_evalAssumption(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro___closed__8;
lean_object* l_Lean_Elab_Tactic_saveBacktrackableState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCase___closed__2;
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__2;
lean_object* l_Lean_Elab_Tactic_evalChoiceAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalOrelse___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__7;
lean_object* l_Lean_Elab_Tactic_setGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarsImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveAllState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__2;
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focus___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro___closed__9;
uint8_t l_Lean_Name_isSuffixOf___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalOrelse___closed__1;
lean_object* l_Lean_Elab_Tactic_catch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_TacticM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalChoiceAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFocus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* lean_metavar_ctx_find_decl(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro___closed__5;
lean_object* l_Lean_refTrans___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRevert(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_6__findTag_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_10__elabUsingElabFnsAux___main___closed__3;
lean_object* l_Array_qsortAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Check_6__checkApp___closed__5;
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_hasOrElse___closed__1;
lean_object* l_Lean_Elab_Tactic_monadExcept___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalIntros___spec__1(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__1;
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux(lean_object*);
lean_object* l_Lean_Elab_Tactic_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTraceState___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focusAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__11;
lean_object* l_Lean_addErrorMessageContextDefault___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars___at_Lean_Elab_Tactic_ensureHasNoMVars___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadExcept___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_MonadExceptOf___rarg(lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_4__getIntrosSize(lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTraceState___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalDone(lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Elab_Tactic_BacktrackableState_restore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_3__introStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntro(lean_object*);
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l_Lean_Elab_Tactic_liftMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_try_x3f(lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_getFVarIds___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Elab_Tactic_getMainTag___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BacktrackableState_restore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSubst___closed__1;
lean_object* l_Lean_Elab_Tactic_evalIntros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__14;
lean_object* l_ReaderT_MonadExceptOf___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_List_findM_x3f___main___at___private_Lean_Elab_Tactic_Basic_6__findTag_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticSeqBracketed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Tactic_ensureHasNoMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__3;
lean_object* l_Lean_Elab_Tactic_try(lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalTactic___main___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalChoiceAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMacroExpansion(lean_object*);
extern lean_object* l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
lean_object* l_ReaderT_MonadFunctor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_registerHygienicIntro___closed__2;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalOrelse(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__3;
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__3;
lean_object* l_Lean_Elab_Tactic_focus___rarg___closed__1;
lean_object* l_Lean_Meta_setMCtx___at_Lean_Elab_Tactic_BacktrackableState_restore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_Lean_Elab_mkMacroAttribute___closed__2;
lean_object* l_Lean_Elab_Tactic_orelse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_getFVarIds___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
extern lean_object* l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__1;
lean_object* l_Lean_Elab_Tactic_getMainModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCase(lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalSeq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__9;
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__2;
lean_object* l_Lean_Elab_Tactic_getGoals(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__1;
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__3;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
lean_object* l_Lean_Elab_Tactic_TacticM_run_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__6;
lean_object* l_Lean_Elab_Tactic_expandTacticMacro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalParen(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro___closed__6;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalSeq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Util_6__regTraceClasses___closed__1;
lean_object* l_Lean_setEnv___at_Lean_Elab_Tactic_BacktrackableState_restore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSeq1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_filterAuxM___main___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSkip___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__13;
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
x_2 = lean_alloc_ctor(10, 2, 0);
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
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Elab_goalsToMessageData(x_1);
x_10 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__4;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_reportUnsolvedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* _init_l_Lean_Elab_Tactic_State_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_saveBacktrackableState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_5, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_1, x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_16);
lean_ctor_set(x_23, 2, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
lean_object* l_Lean_Elab_Tactic_saveBacktrackableState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_saveBacktrackableState___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_saveBacktrackableState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_saveBacktrackableState___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Tactic_saveBacktrackableState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_saveBacktrackableState(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_setEnv___at_Lean_Elab_Tactic_BacktrackableState_restore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_take(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_1);
x_16 = lean_st_ref_set(x_9, x_12, x_13);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_12, 1);
x_24 = lean_ctor_get(x_12, 2);
x_25 = lean_ctor_get(x_12, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_st_ref_set(x_9, x_26, x_13);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_box(0);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
lean_object* l_Lean_Meta_setMCtx___at_Lean_Elab_Tactic_BacktrackableState_restore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_take(x_7, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_1);
x_16 = lean_st_ref_set(x_7, x_12, x_13);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_12, 1);
x_24 = lean_ctor_get(x_12, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_st_ref_set(x_7, x_25, x_13);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
lean_object* l_Lean_Elab_Tactic_BacktrackableState_restore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = l_Lean_setEnv___at_Lean_Elab_Tactic_BacktrackableState_restore___spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = l_Lean_Meta_setMCtx___at_Lean_Elab_Tactic_BacktrackableState_restore___spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_3, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_st_ref_set(x_3, x_19, x_18);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
lean_object* l_Lean_setEnv___at_Lean_Elab_Tactic_BacktrackableState_restore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_setEnv___at_Lean_Elab_Tactic_BacktrackableState_restore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Meta_setMCtx___at_Lean_Elab_Tactic_BacktrackableState_restore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_setMCtx___at_Lean_Elab_Tactic_BacktrackableState_restore___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_BacktrackableState_restore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_catch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Elab_Tactic_saveBacktrackableState___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_apply_10(x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
return x_20;
}
}
}
lean_object* l_Lean_Elab_Tactic_catch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_catch___rarg), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_orelse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
return x_14;
}
}
}
lean_object* l_Lean_Elab_Tactic_orelse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_orelse___rarg), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_monadExcept___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_monadExcept___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_Elab_Tactic_saveBacktrackableState___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = lean_apply_9(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_apply_10(x_3, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
return x_21;
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadExcept___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_monadExcept___lambda__1___boxed), 11, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadExcept___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_monadExcept___lambda__2), 12, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadExcept___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_monadExcept___closed__1;
x_2 = l_Lean_Elab_Tactic_monadExcept___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadExcept() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_monadExcept___closed__3;
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_monadExcept___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_monadExcept___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* _init_l_Lean_Elab_Tactic_hasOrElse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_orelse___rarg), 11, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_hasOrElse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_hasOrElse___closed__1;
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_SavedState_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_State_inhabited___closed__2;
x_3 = l_Lean_Meta_State_inhabited___closed__7;
x_4 = l_Lean_Elab_Term_SavedState_inhabited___closed__1;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Tactic_SavedState_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_SavedState_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_saveAllState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_5, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_3, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_1, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_20);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_16);
lean_ctor_set(x_24, 3, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
lean_object* l_Lean_Elab_Tactic_saveAllState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_saveAllState___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_saveAllState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_saveAllState___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Tactic_saveAllState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_saveAllState(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_st_ref_set(x_9, x_11, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_st_ref_set(x_7, x_14, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_st_ref_set(x_5, x_17, x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_st_ref_set(x_3, x_20, x_19);
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
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
lean_object* l_Lean_Elab_Tactic_SavedState_restore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_liftTermElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_7(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_liftTermElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftTermElabM___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_liftTermElabM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_5(x_1, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaM___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_ensureHasType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_ensureHasType(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_ensureHasType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_ensureHasType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_reportUnsolvedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_reportUnsolvedGoals(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_reportUnsolvedGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_reportUnsolvedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 7);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getCurrMacroScope___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_getCurrMacroScope___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_getCurrMacroScope(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_getMainModule___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_environment_main_module(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_environment_main_module(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
lean_object* l_Lean_Elab_Tactic_getMainModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getMainModule___rarg___boxed), 2, 0);
return x_8;
}
}
lean_object* l_Lean_Elab_Tactic_getMainModule___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_getMainModule___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_getMainModule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_getMainModule(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_mkMacroAttribute___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__1;
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
x_1 = lean_box(0);
x_2 = l_Lean_Meta_registerHygienicIntro___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__1;
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
x_4 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__6;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_6 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__7;
x_7 = l_Lean_Meta_registerHygienicIntro___closed__2;
x_8 = l_Lean_Elab_mkElabAttribute___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_1);
return x_8;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_9, 3);
x_14 = l_Lean_replaceRef(x_1, x_13);
x_15 = l_Lean_replaceRef(x_14, x_13);
lean_dec(x_14);
x_16 = l_Lean_replaceRef(x_15, x_13);
lean_dec(x_13);
lean_dec(x_15);
lean_ctor_set(x_9, 3, x_16);
x_17 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
x_20 = lean_ctor_get(x_9, 2);
x_21 = lean_ctor_get(x_9, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_22 = l_Lean_replaceRef(x_1, x_21);
x_23 = l_Lean_replaceRef(x_22, x_21);
lean_dec(x_22);
x_24 = l_Lean_replaceRef(x_23, x_21);
lean_dec(x_21);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_24);
x_26 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25, x_10, x_11);
lean_dec(x_25);
return x_26;
}
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
lean_inc(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = l_Lean_MessageData_ofList___closed__3;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l___private_Lean_Elab_Term_10__elabUsingElabFnsAux___main___closed__3;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(x_2, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
x_23 = l_Lean_Elab_Tactic_saveBacktrackableState___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_26 = lean_apply_10(x_21, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_27) == 0)
{
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
lean_inc(x_1);
x_35 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_3 = x_22;
x_12 = x_36;
goto _start;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_ctor_get(x_29, 1);
x_40 = lean_ctor_get(x_29, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_27, 0);
lean_inc(x_41);
x_42 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_43 = lean_nat_dec_eq(x_41, x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_free_object(x_29);
lean_dec(x_27);
lean_inc(x_1);
x_44 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_39);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_3 = x_22;
x_12 = x_45;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_29, 1);
lean_inc(x_47);
lean_dec(x_29);
x_48 = lean_ctor_get(x_27, 0);
lean_inc(x_48);
x_49 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_50 = lean_nat_dec_eq(x_48, x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_27);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_27);
lean_inc(x_1);
x_52 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_47);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_3 = x_22;
x_12 = x_53;
goto _start;
}
}
}
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_withMacroExpansion___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_6, 6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_6, 6, x_16);
x_17 = lean_apply_9(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
x_25 = lean_ctor_get(x_6, 7);
x_26 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
x_27 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 1);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
x_30 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_19);
lean_ctor_set(x_30, 2, x_20);
lean_ctor_set(x_30, 3, x_21);
lean_ctor_set(x_30, 4, x_22);
lean_ctor_set(x_30, 5, x_23);
lean_ctor_set(x_30, 6, x_29);
lean_ctor_set(x_30, 7, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*8, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*8 + 1, x_27);
x_31 = lean_apply_9(x_3, x_4, x_5, x_30, x_7, x_8, x_9, x_10, x_11, x_12);
return x_31;
}
}
}
lean_object* l_Lean_Elab_Tactic_withMacroExpansion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMacroExpansion___rarg), 12, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Check_6__checkApp___closed__5;
x_2 = l_StateRefT_x27_MonadExceptOf___rarg(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__2;
x_2 = l_ReaderT_MonadExceptOf___rarg(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__3;
x_2 = l_StateRefT_x27_MonadExceptOf___rarg(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__4;
x_2 = l_ReaderT_MonadExceptOf___rarg(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_Lean_Ref;
x_2 = l_Lean_Meta_CheckAssignment_checkFVar___closed__12;
x_3 = l_Lean_MonadCacheT_MonadLift___closed__1;
x_4 = l_Lean_refTrans___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
x_2 = lean_alloc_closure((void*)(l_ReaderT_MonadFunctor___boxed), 6, 5);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, lean_box(0));
lean_closure_set(x_2, 3, x_1);
lean_closure_set(x_2, 4, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__6;
x_2 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__7;
x_3 = l_ReaderT_MonadLift___closed__1;
x_4 = l_Lean_refTrans___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_CheckAssignment_checkFVar___closed__14;
x_2 = l_ReaderT_MonadLift___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_addMessageContextTrans___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__9;
x_2 = l_Lean_MonadCacheT_MonadLift___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_addMessageContextTrans___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__10;
x_2 = l_ReaderT_MonadLift___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_addMessageContextTrans___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__11;
x_2 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_addErrorMessageContextDefault___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_Lean_Ref;
x_2 = l_Lean_Meta_CheckAssignment_checkFVar___closed__12;
x_3 = l_Lean_MonadCacheT_MonadLift___closed__1;
x_4 = l_Lean_refTrans___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__13;
x_2 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__7;
x_3 = l_ReaderT_MonadLift___closed__1;
x_4 = l_Lean_refTrans___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
lean_inc(x_2);
x_13 = l_Lean_Syntax_getKind(x_2);
x_14 = l_System_FilePath_dirName___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_13);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Meta_throwTacticEx___rarg___closed__3;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Elab_Term_11__elabUsingElabFns___closed__6;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__1;
x_23 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__5;
x_24 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__8;
x_25 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__12;
x_26 = l_Lean_throwErrorAt___rarg(x_22, x_23, x_24, x_25, lean_box(0), x_2, x_21);
x_27 = lean_apply_9(x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
lean_dec(x_3);
x_30 = l_Lean_Elab_Term_getCurrMacroScope(x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Elab_Tactic_saveBacktrackableState___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Elab_Term_getCurrMacroScope(x_6, x_7, x_8, x_9, x_10, x_11, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_st_ref_get(x_11, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_st_ref_get(x_11, x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_10, 2);
lean_inc(x_47);
lean_inc(x_41);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_5__expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_48, 0, x_41);
x_49 = x_48;
x_50 = lean_environment_main_module(x_41);
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_36);
lean_ctor_set(x_51, 3, x_46);
lean_ctor_set(x_51, 4, x_47);
lean_inc(x_2);
x_52 = lean_apply_3(x_28, x_2, x_51, x_45);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_st_ref_take(x_11, x_44);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_56, 1);
lean_dec(x_59);
lean_ctor_set(x_56, 1, x_54);
x_60 = lean_st_ref_set(x_11, x_56, x_57);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_62 = lean_apply_10(x_1, x_53, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_64);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_66; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 0, x_63);
return x_65;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
lean_object* x_70; 
lean_dec(x_63);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_dec(x_65);
x_3 = x_29;
x_12 = x_70;
goto _start;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_56, 0);
x_73 = lean_ctor_get(x_56, 2);
x_74 = lean_ctor_get(x_56, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_56);
x_75 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_54);
lean_ctor_set(x_75, 2, x_73);
lean_ctor_set(x_75, 3, x_74);
x_76 = lean_st_ref_set(x_11, x_75, x_57);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_78 = lean_apply_10(x_1, x_53, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_80);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
 lean_ctor_set_tag(x_84, 1);
}
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
else
{
lean_object* x_85; 
lean_dec(x_79);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_3 = x_29;
x_12 = x_85;
goto _start;
}
}
}
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_52, 0);
lean_inc(x_87);
lean_dec(x_52);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__1;
x_93 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__5;
x_94 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__14;
x_95 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__12;
x_96 = l_Lean_throwErrorAt___rarg(x_92, x_93, x_94, x_95, lean_box(0), x_88, x_91);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_97 = lean_apply_9(x_96, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_100 = lean_apply_10(x_1, x_98, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_102);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_104; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_103, 0);
lean_dec(x_105);
lean_ctor_set_tag(x_103, 1);
lean_ctor_set(x_103, 0, x_101);
return x_103;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_101);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
else
{
lean_object* x_108; 
lean_dec(x_101);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
lean_dec(x_103);
x_3 = x_29;
x_12 = x_108;
goto _start;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_97, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_97, 1);
lean_inc(x_111);
lean_dec(x_97);
x_112 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_111);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_113; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_112, 0);
lean_dec(x_114);
lean_ctor_set_tag(x_112, 1);
lean_ctor_set(x_112, 0, x_110);
return x_112;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_dec(x_112);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_110);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
lean_object* x_117; 
lean_dec(x_110);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
lean_dec(x_112);
x_3 = x_29;
x_12 = x_117;
goto _start;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__5;
x_120 = l_Lean_Elab_throwUnsupportedSyntax___rarg(x_119);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_121 = lean_apply_9(x_120, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_124 = lean_apply_10(x_1, x_122, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_126);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_128; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_127, 0);
lean_dec(x_129);
lean_ctor_set_tag(x_127, 1);
lean_ctor_set(x_127, 0, x_125);
return x_127;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_125);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
else
{
lean_object* x_132; 
lean_dec(x_125);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_dec(x_127);
x_3 = x_29;
x_12 = x_132;
goto _start;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_121, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_121, 1);
lean_inc(x_135);
lean_dec(x_121);
x_136 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_135);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_137; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_136, 0);
lean_dec(x_138);
lean_ctor_set_tag(x_136, 1);
lean_ctor_set(x_136, 0, x_134);
return x_136;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_134);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
else
{
lean_object* x_141; 
lean_dec(x_134);
x_141 = lean_ctor_get(x_136, 1);
lean_inc(x_141);
lean_dec(x_136);
x_3 = x_29;
x_12 = x_141;
goto _start;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_expandTacticMacro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_2);
x_16 = l_Lean_Syntax_getKind(x_2);
x_17 = l_Lean_Elab_macroAttribute;
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
x_19 = l_Lean_PersistentEnvExtension_getState___rarg(x_18, x_15);
lean_dec(x_15);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_20, x_16);
lean_dec(x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main(x_1, x_2, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main(x_1, x_2, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_25;
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic___main___spec__8___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic___main___spec__8___rarg), 1, 0);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_1);
x_12 = l_Lean_Syntax_getKind(x_1);
x_13 = l_System_FilePath_dirName___closed__1;
x_14 = l_Lean_Name_toStringWithSep___main(x_13, x_12);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Meta_throwTacticEx___rarg___closed__3;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l___private_Lean_Elab_Term_11__elabUsingElabFns___closed__6;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Elab_Tactic_saveBacktrackableState___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_st_ref_get(x_10, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_get(x_10, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_9, 2);
lean_inc(x_41);
lean_inc(x_35);
x_42 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_5__expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_42, 0, x_35);
x_43 = x_42;
x_44 = lean_environment_main_module(x_35);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_30);
lean_ctor_set(x_45, 3, x_40);
lean_ctor_set(x_45, 4, x_41);
lean_inc(x_1);
x_46 = lean_apply_3(x_22, x_1, x_45, x_39);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_st_ref_take(x_10, x_38);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_50, 1);
lean_dec(x_53);
lean_ctor_set(x_50, 1, x_48);
x_54 = lean_st_ref_set(x_10, x_50, x_51);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_56 = l_Lean_Elab_Tactic_evalTactic___main(x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_60; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* x_64; 
lean_dec(x_57);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_dec(x_59);
x_2 = x_23;
x_11 = x_64;
goto _start;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_50, 0);
x_67 = lean_ctor_get(x_50, 2);
x_68 = lean_ctor_get(x_50, 3);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_50);
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_48);
lean_ctor_set(x_69, 2, x_67);
lean_ctor_set(x_69, 3, x_68);
x_70 = lean_st_ref_set(x_10, x_69, x_51);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_72 = l_Lean_Elab_Tactic_evalTactic___main(x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_74);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
 lean_ctor_set_tag(x_78, 1);
}
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
else
{
lean_object* x_79; 
lean_dec(x_73);
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_2 = x_23;
x_11 = x_79;
goto _start;
}
}
}
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_46, 0);
lean_inc(x_81);
lean_dec(x_46);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
lean_inc(x_9);
x_86 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__1___rarg(x_82, x_85, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
lean_dec(x_82);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_88);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_90; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_89, 0);
lean_dec(x_91);
lean_ctor_set_tag(x_89, 1);
lean_ctor_set(x_89, 0, x_87);
return x_89;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
else
{
lean_object* x_94; 
lean_dec(x_87);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_dec(x_89);
x_2 = x_23;
x_11 = x_94;
goto _start;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic___main___spec__8___rarg(x_38);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_98);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_100; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_99, 0);
lean_dec(x_101);
lean_ctor_set_tag(x_99, 1);
lean_ctor_set(x_99, 0, x_97);
return x_99;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
else
{
lean_object* x_104; 
lean_dec(x_97);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_dec(x_99);
x_2 = x_23;
x_11 = x_104;
goto _start;
}
}
}
}
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalTactic___main___spec__11(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 3);
x_14 = l_Lean_replaceRef(x_1, x_13);
x_15 = l_Lean_Syntax_getPos(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 2);
x_19 = lean_ctor_get(x_6, 5);
x_20 = l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_FileMap_toPosition(x_17, x_23);
x_25 = lean_box(0);
lean_inc(x_19);
lean_inc(x_18);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_19);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
x_28 = l_String_splitAux___main___closed__1;
lean_inc(x_16);
x_29 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set(x_29, 4, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*5, x_3);
x_30 = lean_st_ref_take(x_7, x_22);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_31, 2);
x_35 = l_Std_PersistentArray_push___rarg(x_34, x_29);
lean_ctor_set(x_31, 2, x_35);
x_36 = lean_st_ref_set(x_7, x_31, x_32);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_43 = lean_ctor_get(x_31, 0);
x_44 = lean_ctor_get(x_31, 1);
x_45 = lean_ctor_get(x_31, 2);
x_46 = lean_ctor_get(x_31, 3);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_31);
x_47 = l_Std_PersistentArray_push___rarg(x_45, x_29);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_46);
x_49 = lean_st_ref_set(x_7, x_48, x_32);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_box(0);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_54 = lean_ctor_get(x_15, 0);
lean_inc(x_54);
lean_dec(x_15);
x_55 = lean_ctor_get(x_6, 0);
x_56 = lean_ctor_get(x_6, 1);
x_57 = lean_ctor_get(x_6, 2);
x_58 = lean_ctor_get(x_6, 5);
x_59 = l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_FileMap_toPosition(x_56, x_54);
x_63 = lean_box(0);
lean_inc(x_58);
lean_inc(x_57);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_58);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
x_66 = l_String_splitAux___main___closed__1;
lean_inc(x_55);
x_67 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_67, 0, x_55);
lean_ctor_set(x_67, 1, x_62);
lean_ctor_set(x_67, 2, x_63);
lean_ctor_set(x_67, 3, x_66);
lean_ctor_set(x_67, 4, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*5, x_3);
x_68 = lean_st_ref_take(x_7, x_61);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_69, 2);
x_73 = l_Std_PersistentArray_push___rarg(x_72, x_67);
lean_ctor_set(x_69, 2, x_73);
x_74 = lean_st_ref_set(x_7, x_69, x_70);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_74, 0, x_77);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_81 = lean_ctor_get(x_69, 0);
x_82 = lean_ctor_get(x_69, 1);
x_83 = lean_ctor_get(x_69, 2);
x_84 = lean_ctor_get(x_69, 3);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_69);
x_85 = l_Std_PersistentArray_push___rarg(x_83, x_67);
x_86 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_82);
lean_ctor_set(x_86, 2, x_85);
lean_ctor_set(x_86, 3, x_84);
x_87 = lean_st_ref_set(x_7, x_86, x_70);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = lean_box(0);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
}
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTactic___main___spec__10(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 3);
x_13 = l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalTactic___main___spec__11(x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Tactic_evalTactic___main___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
x_13 = 0;
x_14 = l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTactic___main___spec__10(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_2, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_fget(x_1, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Elab_Tactic_evalTactic___main(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
x_11 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l_Lean_Elab_Tactic_evalTactic___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 2);
x_15 = lean_ctor_get(x_8, 3);
x_16 = l_Lean_replaceRef(x_1, x_15);
x_17 = l_Lean_replaceRef(x_16, x_15);
lean_dec(x_16);
x_18 = l_Lean_replaceRef(x_17, x_15);
lean_dec(x_15);
lean_dec(x_17);
lean_inc(x_18);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_ctor_set(x_8, 3, x_18);
x_19 = lean_nat_dec_eq(x_13, x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_8);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_13, x_20);
lean_dec(x_13);
lean_inc(x_12);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_14);
lean_ctor_set(x_22, 3, x_18);
x_23 = lean_st_ref_take(x_9, x_10);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_nat_add(x_27, x_20);
lean_ctor_set(x_24, 1, x_28);
x_29 = lean_st_ref_set(x_9, x_24, x_25);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_4, 7);
lean_dec(x_32);
lean_ctor_set(x_4, 7, x_27);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
x_64 = l_Lean_nullKind;
x_65 = lean_name_eq(x_63, x_64);
lean_dec(x_63);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = l___private_Lean_Elab_Util_6__regTraceClasses___closed__3;
x_67 = l_Lean_checkTraceOption(x_12, x_66);
lean_dec(x_12);
if (x_67 == 0)
{
x_33 = x_30;
goto block_62;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_inc(x_1);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_1);
x_69 = l_Lean_Elab_logTrace___at_Lean_Elab_Tactic_evalTactic___main___spec__9(x_66, x_68, x_2, x_3, x_4, x_5, x_6, x_7, x_22, x_9, x_30);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_33 = x_70;
goto block_62;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_12);
x_71 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_72 = lean_unsigned_to_nat(0u);
x_73 = l_Array_forMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__12(x_71, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_22, x_9, x_30);
lean_dec(x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_12);
lean_dec(x_1);
x_74 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_75 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg(x_74, x_2, x_3, x_4, x_5, x_6, x_7, x_22, x_9, x_30);
lean_dec(x_9);
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_75;
}
block_62:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = lean_st_ref_get(x_9, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Tactic_saveAllState___rarg(x_3, x_4, x_5, x_6, x_7, x_22, x_9, x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_42 = lean_ctor_get(x_41, 2);
lean_inc(x_42);
x_43 = l_Lean_PersistentEnvExtension_getState___rarg(x_42, x_37);
lean_dec(x_37);
lean_dec(x_42);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
lean_inc(x_1);
x_45 = l_Lean_Syntax_getKind(x_1);
x_46 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_44, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_39);
x_47 = lean_st_ref_get(x_9, x_40);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Elab_macroAttribute;
x_52 = lean_ctor_get(x_51, 2);
lean_inc(x_52);
x_53 = l_Lean_PersistentEnvExtension_getState___rarg(x_52, x_50);
lean_dec(x_50);
lean_dec(x_52);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_54, x_45);
lean_dec(x_45);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_box(0);
x_57 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_22, x_9, x_49);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec(x_55);
x_59 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_22, x_9, x_49);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_45);
x_60 = lean_ctor_get(x_46, 0);
lean_inc(x_60);
lean_dec(x_46);
x_61 = l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_39, x_1, x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_22, x_9, x_40);
return x_61;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_76 = lean_ctor_get(x_4, 0);
x_77 = lean_ctor_get(x_4, 1);
x_78 = lean_ctor_get(x_4, 2);
x_79 = lean_ctor_get(x_4, 3);
x_80 = lean_ctor_get(x_4, 4);
x_81 = lean_ctor_get(x_4, 5);
x_82 = lean_ctor_get(x_4, 6);
x_83 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
x_84 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_4);
x_85 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_85, 0, x_76);
lean_ctor_set(x_85, 1, x_77);
lean_ctor_set(x_85, 2, x_78);
lean_ctor_set(x_85, 3, x_79);
lean_ctor_set(x_85, 4, x_80);
lean_ctor_set(x_85, 5, x_81);
lean_ctor_set(x_85, 6, x_82);
lean_ctor_set(x_85, 7, x_27);
lean_ctor_set_uint8(x_85, sizeof(void*)*8, x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*8 + 1, x_84);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_1, 0);
lean_inc(x_116);
x_117 = l_Lean_nullKind;
x_118 = lean_name_eq(x_116, x_117);
lean_dec(x_116);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = l___private_Lean_Elab_Util_6__regTraceClasses___closed__3;
x_120 = l_Lean_checkTraceOption(x_12, x_119);
lean_dec(x_12);
if (x_120 == 0)
{
x_86 = x_30;
goto block_115;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_inc(x_1);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_1);
x_122 = l_Lean_Elab_logTrace___at_Lean_Elab_Tactic_evalTactic___main___spec__9(x_119, x_121, x_2, x_3, x_85, x_5, x_6, x_7, x_22, x_9, x_30);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_86 = x_123;
goto block_115;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_12);
x_124 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_125 = lean_unsigned_to_nat(0u);
x_126 = l_Array_forMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__12(x_124, x_125, x_2, x_3, x_85, x_5, x_6, x_7, x_22, x_9, x_30);
lean_dec(x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_12);
lean_dec(x_1);
x_127 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_128 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg(x_127, x_2, x_3, x_85, x_5, x_6, x_7, x_22, x_9, x_30);
lean_dec(x_9);
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_85);
lean_dec(x_3);
lean_dec(x_2);
return x_128;
}
block_115:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_87 = lean_st_ref_get(x_9, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Elab_Tactic_saveAllState___rarg(x_3, x_85, x_5, x_6, x_7, x_22, x_9, x_89);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_95 = lean_ctor_get(x_94, 2);
lean_inc(x_95);
x_96 = l_Lean_PersistentEnvExtension_getState___rarg(x_95, x_90);
lean_dec(x_90);
lean_dec(x_95);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
lean_inc(x_1);
x_98 = l_Lean_Syntax_getKind(x_1);
x_99 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_97, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_92);
x_100 = lean_st_ref_get(x_9, x_93);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lean_Elab_macroAttribute;
x_105 = lean_ctor_get(x_104, 2);
lean_inc(x_105);
x_106 = l_Lean_PersistentEnvExtension_getState___rarg(x_105, x_103);
lean_dec(x_103);
lean_dec(x_105);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_107, x_98);
lean_dec(x_98);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_box(0);
x_110 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_109, x_2, x_3, x_85, x_5, x_6, x_7, x_22, x_9, x_102);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_108, 0);
lean_inc(x_111);
lean_dec(x_108);
x_112 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_111, x_2, x_3, x_85, x_5, x_6, x_7, x_22, x_9, x_102);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_98);
x_113 = lean_ctor_get(x_99, 0);
lean_inc(x_113);
lean_dec(x_99);
x_114 = l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_92, x_1, x_113, x_2, x_3, x_85, x_5, x_6, x_7, x_22, x_9, x_93);
return x_114;
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_129 = lean_ctor_get(x_24, 0);
x_130 = lean_ctor_get(x_24, 1);
x_131 = lean_ctor_get(x_24, 2);
x_132 = lean_ctor_get(x_24, 3);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_24);
x_133 = lean_nat_add(x_130, x_20);
x_134 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_134, 2, x_131);
lean_ctor_set(x_134, 3, x_132);
x_135 = lean_st_ref_set(x_9, x_134, x_25);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_ctor_get(x_4, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_4, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_4, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_4, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_4, 4);
lean_inc(x_141);
x_142 = lean_ctor_get(x_4, 5);
lean_inc(x_142);
x_143 = lean_ctor_get(x_4, 6);
lean_inc(x_143);
x_144 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
x_145 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 x_146 = x_4;
} else {
 lean_dec_ref(x_4);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 8, 2);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_137);
lean_ctor_set(x_147, 1, x_138);
lean_ctor_set(x_147, 2, x_139);
lean_ctor_set(x_147, 3, x_140);
lean_ctor_set(x_147, 4, x_141);
lean_ctor_set(x_147, 5, x_142);
lean_ctor_set(x_147, 6, x_143);
lean_ctor_set(x_147, 7, x_130);
lean_ctor_set_uint8(x_147, sizeof(void*)*8, x_144);
lean_ctor_set_uint8(x_147, sizeof(void*)*8 + 1, x_145);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_178 = lean_ctor_get(x_1, 0);
lean_inc(x_178);
x_179 = l_Lean_nullKind;
x_180 = lean_name_eq(x_178, x_179);
lean_dec(x_178);
if (x_180 == 0)
{
lean_object* x_181; uint8_t x_182; 
x_181 = l___private_Lean_Elab_Util_6__regTraceClasses___closed__3;
x_182 = l_Lean_checkTraceOption(x_12, x_181);
lean_dec(x_12);
if (x_182 == 0)
{
x_148 = x_136;
goto block_177;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_inc(x_1);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_1);
x_184 = l_Lean_Elab_logTrace___at_Lean_Elab_Tactic_evalTactic___main___spec__9(x_181, x_183, x_2, x_3, x_147, x_5, x_6, x_7, x_22, x_9, x_136);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
lean_dec(x_184);
x_148 = x_185;
goto block_177;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_12);
x_186 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_187 = lean_unsigned_to_nat(0u);
x_188 = l_Array_forMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__12(x_186, x_187, x_2, x_3, x_147, x_5, x_6, x_7, x_22, x_9, x_136);
lean_dec(x_186);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_12);
lean_dec(x_1);
x_189 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_190 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg(x_189, x_2, x_3, x_147, x_5, x_6, x_7, x_22, x_9, x_136);
lean_dec(x_9);
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_147);
lean_dec(x_3);
lean_dec(x_2);
return x_190;
}
block_177:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_149 = lean_st_ref_get(x_9, x_148);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
lean_dec(x_150);
x_153 = l_Lean_Elab_Tactic_saveAllState___rarg(x_3, x_147, x_5, x_6, x_7, x_22, x_9, x_151);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_157 = lean_ctor_get(x_156, 2);
lean_inc(x_157);
x_158 = l_Lean_PersistentEnvExtension_getState___rarg(x_157, x_152);
lean_dec(x_152);
lean_dec(x_157);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
lean_inc(x_1);
x_160 = l_Lean_Syntax_getKind(x_1);
x_161 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_159, x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_154);
x_162 = lean_st_ref_get(x_9, x_155);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l_Lean_Elab_macroAttribute;
x_167 = lean_ctor_get(x_166, 2);
lean_inc(x_167);
x_168 = l_Lean_PersistentEnvExtension_getState___rarg(x_167, x_165);
lean_dec(x_165);
lean_dec(x_167);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_170 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_169, x_160);
lean_dec(x_160);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_box(0);
x_172 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_171, x_2, x_3, x_147, x_5, x_6, x_7, x_22, x_9, x_164);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_170, 0);
lean_inc(x_173);
lean_dec(x_170);
x_174 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_173, x_2, x_3, x_147, x_5, x_6, x_7, x_22, x_9, x_164);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_160);
x_175 = lean_ctor_get(x_161, 0);
lean_inc(x_175);
lean_dec(x_161);
x_176 = l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_154, x_1, x_175, x_2, x_3, x_147, x_5, x_6, x_7, x_22, x_9, x_155);
return x_176;
}
}
}
}
else
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_191 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_192 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg(x_191, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
return x_192;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_192, 0);
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_192);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_197 = lean_ctor_get(x_8, 0);
x_198 = lean_ctor_get(x_8, 1);
x_199 = lean_ctor_get(x_8, 2);
x_200 = lean_ctor_get(x_8, 3);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_8);
x_201 = l_Lean_replaceRef(x_1, x_200);
x_202 = l_Lean_replaceRef(x_201, x_200);
lean_dec(x_201);
x_203 = l_Lean_replaceRef(x_202, x_200);
lean_dec(x_200);
lean_dec(x_202);
lean_inc(x_203);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
x_204 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_204, 0, x_197);
lean_ctor_set(x_204, 1, x_198);
lean_ctor_set(x_204, 2, x_199);
lean_ctor_set(x_204, 3, x_203);
x_205 = lean_nat_dec_eq(x_198, x_199);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_204);
x_206 = lean_unsigned_to_nat(1u);
x_207 = lean_nat_add(x_198, x_206);
lean_dec(x_198);
lean_inc(x_197);
x_208 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_208, 0, x_197);
lean_ctor_set(x_208, 1, x_207);
lean_ctor_set(x_208, 2, x_199);
lean_ctor_set(x_208, 3, x_203);
x_209 = lean_st_ref_take(x_9, x_10);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_210, 2);
lean_inc(x_214);
x_215 = lean_ctor_get(x_210, 3);
lean_inc(x_215);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 x_216 = x_210;
} else {
 lean_dec_ref(x_210);
 x_216 = lean_box(0);
}
x_217 = lean_nat_add(x_213, x_206);
if (lean_is_scalar(x_216)) {
 x_218 = lean_alloc_ctor(0, 4, 0);
} else {
 x_218 = x_216;
}
lean_ctor_set(x_218, 0, x_212);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set(x_218, 2, x_214);
lean_ctor_set(x_218, 3, x_215);
x_219 = lean_st_ref_set(x_9, x_218, x_211);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec(x_219);
x_221 = lean_ctor_get(x_4, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_4, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_4, 2);
lean_inc(x_223);
x_224 = lean_ctor_get(x_4, 3);
lean_inc(x_224);
x_225 = lean_ctor_get(x_4, 4);
lean_inc(x_225);
x_226 = lean_ctor_get(x_4, 5);
lean_inc(x_226);
x_227 = lean_ctor_get(x_4, 6);
lean_inc(x_227);
x_228 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
x_229 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 x_230 = x_4;
} else {
 lean_dec_ref(x_4);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(0, 8, 2);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_221);
lean_ctor_set(x_231, 1, x_222);
lean_ctor_set(x_231, 2, x_223);
lean_ctor_set(x_231, 3, x_224);
lean_ctor_set(x_231, 4, x_225);
lean_ctor_set(x_231, 5, x_226);
lean_ctor_set(x_231, 6, x_227);
lean_ctor_set(x_231, 7, x_213);
lean_ctor_set_uint8(x_231, sizeof(void*)*8, x_228);
lean_ctor_set_uint8(x_231, sizeof(void*)*8 + 1, x_229);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_262 = lean_ctor_get(x_1, 0);
lean_inc(x_262);
x_263 = l_Lean_nullKind;
x_264 = lean_name_eq(x_262, x_263);
lean_dec(x_262);
if (x_264 == 0)
{
lean_object* x_265; uint8_t x_266; 
x_265 = l___private_Lean_Elab_Util_6__regTraceClasses___closed__3;
x_266 = l_Lean_checkTraceOption(x_197, x_265);
lean_dec(x_197);
if (x_266 == 0)
{
x_232 = x_220;
goto block_261;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_inc(x_1);
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_1);
x_268 = l_Lean_Elab_logTrace___at_Lean_Elab_Tactic_evalTactic___main___spec__9(x_265, x_267, x_2, x_3, x_231, x_5, x_6, x_7, x_208, x_9, x_220);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
lean_dec(x_268);
x_232 = x_269;
goto block_261;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_197);
x_270 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_271 = lean_unsigned_to_nat(0u);
x_272 = l_Array_forMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__12(x_270, x_271, x_2, x_3, x_231, x_5, x_6, x_7, x_208, x_9, x_220);
lean_dec(x_270);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; 
lean_dec(x_197);
lean_dec(x_1);
x_273 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_274 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg(x_273, x_2, x_3, x_231, x_5, x_6, x_7, x_208, x_9, x_220);
lean_dec(x_9);
lean_dec(x_208);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_231);
lean_dec(x_3);
lean_dec(x_2);
return x_274;
}
block_261:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_233 = lean_st_ref_get(x_9, x_232);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_ctor_get(x_234, 0);
lean_inc(x_236);
lean_dec(x_234);
x_237 = l_Lean_Elab_Tactic_saveAllState___rarg(x_3, x_231, x_5, x_6, x_7, x_208, x_9, x_235);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_241 = lean_ctor_get(x_240, 2);
lean_inc(x_241);
x_242 = l_Lean_PersistentEnvExtension_getState___rarg(x_241, x_236);
lean_dec(x_236);
lean_dec(x_241);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
lean_inc(x_1);
x_244 = l_Lean_Syntax_getKind(x_1);
x_245 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_243, x_244);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_238);
x_246 = lean_st_ref_get(x_9, x_239);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = lean_ctor_get(x_247, 0);
lean_inc(x_249);
lean_dec(x_247);
x_250 = l_Lean_Elab_macroAttribute;
x_251 = lean_ctor_get(x_250, 2);
lean_inc(x_251);
x_252 = l_Lean_PersistentEnvExtension_getState___rarg(x_251, x_249);
lean_dec(x_249);
lean_dec(x_251);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
x_254 = l_Lean_SMap_find_x3f___at_Lean_Elab_getMacros___spec__1(x_253, x_244);
lean_dec(x_244);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_box(0);
x_256 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_255, x_2, x_3, x_231, x_5, x_6, x_7, x_208, x_9, x_248);
return x_256;
}
else
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_254, 0);
lean_inc(x_257);
lean_dec(x_254);
x_258 = l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___at_Lean_Elab_Tactic_evalTactic___main___spec__7(x_1, x_257, x_2, x_3, x_231, x_5, x_6, x_7, x_208, x_9, x_248);
return x_258;
}
}
else
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_244);
x_259 = lean_ctor_get(x_245, 0);
lean_inc(x_259);
lean_dec(x_245);
x_260 = l___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_238, x_1, x_259, x_2, x_3, x_231, x_5, x_6, x_7, x_208, x_9, x_239);
return x_260;
}
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_203);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_1);
x_275 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_276 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg(x_275, x_2, x_3, x_4, x_5, x_6, x_7, x_204, x_9, x_10);
lean_dec(x_9);
lean_dec(x_204);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_279 = x_276;
} else {
 lean_dec_ref(x_276);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_278);
return x_280;
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic___main___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalTactic___main___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalTactic___main___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalTactic___main___spec__11(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTactic___main___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTactic___main___spec__10(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Tactic_evalTactic___main___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_logTrace___at_Lean_Elab_Tactic_evalTactic___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalTactic___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_adaptExpander(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = lean_apply_10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_5, 6);
lean_inc(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_13);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_5, 6, x_18);
x_19 = l_Lean_Elab_Tactic_evalTactic___main(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
x_22 = lean_ctor_get(x_5, 2);
x_23 = lean_ctor_get(x_5, 3);
x_24 = lean_ctor_get(x_5, 4);
x_25 = lean_ctor_get(x_5, 5);
x_26 = lean_ctor_get(x_5, 6);
x_27 = lean_ctor_get(x_5, 7);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*8);
x_29 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 1);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
lean_inc(x_13);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
x_32 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set(x_32, 3, x_23);
lean_ctor_set(x_32, 4, x_24);
lean_ctor_set(x_32, 5, x_25);
lean_ctor_set(x_32, 6, x_31);
lean_ctor_set(x_32, 7, x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*8, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*8 + 1, x_29);
x_33 = l_Lean_Elab_Tactic_evalTactic___main(x_13, x_3, x_4, x_32, x_6, x_7, x_8, x_9, x_10, x_14);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_getGoals___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
lean_object* l_Lean_Elab_Tactic_getGoals(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getGoals___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getGoals___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_getGoals___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
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
lean_object* l_Lean_Elab_Tactic_setGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_take(x_3, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_set(x_3, x_1, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
lean_object* l_Lean_Elab_Tactic_setGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_setGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_appendGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_take(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_List_append___rarg(x_12, x_1);
x_15 = lean_st_ref_set(x_3, x_14, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
lean_object* l_Lean_Elab_Tactic_appendGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_appendGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Meta_isExprMVarAssigned___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_7, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_metavar_ctx_is_expr_assigned(x_14, x_1);
x_16 = lean_box(x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_metavar_ctx_is_expr_assigned(x_19, x_1);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
lean_object* l_List_filterAuxM___main___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_16 = l_Lean_Meta_isExprMVarAssigned___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_15;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_10 = x_19;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_11 = _tmp_10;
}
goto _start;
}
else
{
lean_object* x_21; 
lean_free_object(x_1);
lean_dec(x_14);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_1 = x_15;
x_11 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
lean_inc(x_23);
x_25 = l_Lean_Meta_isExprMVarAssigned___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_2);
x_1 = x_24;
x_2 = x_29;
x_11 = x_28;
goto _start;
}
else
{
lean_object* x_31; 
lean_dec(x_23);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_1 = x_24;
x_11 = x_31;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = l_Lean_Elab_Tactic_getGoals___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_List_filterAuxM___main___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__2(x_11, x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_List_reverse___rarg(x_15);
x_18 = l_Lean_Elab_Tactic_setGoals(x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
return x_18;
}
}
lean_object* l_Lean_Meta_isExprMVarAssigned___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_isExprMVarAssigned___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_List_filterAuxM___main___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_filterAuxM___main___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_pruneSolvedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Elab_Tactic_pruneSolvedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_Tactic_getGoals___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
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
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Tactic_getMainGoal___closed__3;
x_14 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_10, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_getMainGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Elab_Tactic_getMainTag___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_7, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_16 = lean_metavar_ctx_find_decl(x_15, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_11);
x_17 = l_Lean_mkMVar(x_1);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__3;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_22, x_6, x_7, x_8, x_9, x_14);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_24);
return x_11;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_1);
x_28 = lean_metavar_ctx_find_decl(x_27, x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = l_Lean_mkMVar(x_1);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_Meta_getMVarDecl___rarg___lambda__1___closed__3;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_34, x_6, x_7, x_8, x_9, x_26);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_26);
return x_37;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_getMainTag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_getMVarDecl___at_Lean_Elab_Tactic_getMainTag___spec__1(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_17);
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
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
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
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Elab_Tactic_getMainTag___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_getMVarDecl___at_Lean_Elab_Tactic_getMainTag___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_getMainTag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainTag(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Tactic_ensureHasNoMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasMVar(x_1);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_st_ref_take(x_7, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = l_Lean_MetavarContext_instantiateMVars(x_17, x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set(x_14, 0, x_20);
x_21 = lean_st_ref_set(x_7, x_14, x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
x_28 = lean_ctor_get(x_14, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_29 = l_Lean_MetavarContext_instantiateMVars(x_26, x_1);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_st_ref_set(x_7, x_32, x_15);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
lean_object* l_Lean_Meta_getMVars___at_Lean_Elab_Tactic_ensureHasNoMVars___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_getMVarsImp(x_1, x_6, x_7, x_8, x_9, x_10);
return x_11;
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
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Tactic_ensureHasNoMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = l_Lean_Meta_getMVarsImp(x_12, x_6, x_7, x_8, x_9, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = l_Lean_Expr_hasExprMVar(x_12);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_12);
x_22 = lean_box(0);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_17);
x_23 = l_Lean_indentExpr(x_12);
x_24 = l_Lean_Elab_Tactic_ensureHasNoMVars___closed__3;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = l_Lean_Expr_hasExprMVar(x_12);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_12);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = l_Lean_indentExpr(x_12);
x_32 = l_Lean_Elab_Tactic_ensureHasNoMVars___closed__3;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
return x_34;
}
}
}
}
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Tactic_ensureHasNoMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Tactic_ensureHasNoMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Meta_getMVars___at_Lean_Elab_Tactic_ensureHasNoMVars___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_getMVars___at_Lean_Elab_Tactic_ensureHasNoMVars___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_ensureHasNoMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
x_13 = l___private_Lean_Meta_Basic_32__withMVarContextImp___rarg(x_1, x_12, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_withMainMVarContext___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l_Lean_Elab_Tactic_withMainMVarContext(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainMVarContext___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_14);
x_15 = lean_apply_1(x_1, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_14, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaMAtMain___rarg), 10, 0);
return x_2;
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_apply_10(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_List_append___rarg(x_13, x_1);
x_15 = l_Lean_Elab_Tactic_setGoals(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
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
lean_inc(x_14);
x_16 = lean_apply_1(x_1, x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 11, 1);
lean_closure_set(x_18, 0, x_15);
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_14, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
lean_object* _init_l_Lean_Elab_Tactic_liftMetaTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
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
lean_inc(x_14);
x_16 = lean_apply_1(x_1, x_14);
x_17 = l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
x_18 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 11, 1);
lean_closure_set(x_20, 0, x_15);
x_21 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_14, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_liftMetaTactic___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Elab_Tactic_done(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_List_isEmpty___rarg(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_free_object(x_10);
x_15 = l_Lean_Elab_Term_reportUnsolvedGoals(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_3);
x_16 = lean_box(0);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = l_List_isEmpty___rarg(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Lean_Elab_Term_reportUnsolvedGoals(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_3);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_done___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_done(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Tactic_evalDone___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_done(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_Tactic_evalDone(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDone___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalDone___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_evalDone___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Tactic_evalDone___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalDone(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("done");
return x_1;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDone___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDone(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_focusAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
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
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Tactic_setGoals(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_20 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Tactic_getGoals___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_List_append___rarg(x_24, x_15);
x_27 = l_Lean_Elab_Tactic_setGoals(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_21);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
lean_object* l_Lean_Elab_Tactic_focusAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_focusAux___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_focus___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_done(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_1);
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
lean_object* _init_l_Lean_Elab_Tactic_focus___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_focus___rarg___lambda__1___boxed), 10, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_focus___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Elab_Tactic_focus___rarg___closed__1;
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Elab_Tactic_focusAux___rarg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_focus(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_focus___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_focus___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_focus___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_try_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Elab_Tactic_saveBacktrackableState___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_14, 0, x_17);
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
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_try_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_try_x3f___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_try___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Elab_Tactic_saveBacktrackableState___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = 1;
x_18 = lean_box(x_17);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = 0;
x_28 = lean_box(x_27);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_try(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_try___rarg), 10, 0);
return x_2;
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = l_Lean_MetavarContext_isAnonymousMVar(x_1, x_4);
if (x_6 == 0)
{
x_3 = x_5;
goto _start;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
x_3 = x_5;
goto _start;
}
}
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_8);
x_10 = l_Lean_MetavarContext_isAnonymousMVar(x_8, x_6);
if (x_10 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_5 = x_7;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_4, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_4, 0);
lean_dec(x_14);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_dec_eq(x_3, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_9);
lean_inc(x_2);
x_17 = l_Lean_Name_appendIndexAfter(x_2, x_9);
x_18 = l_Lean_Name_append___main(x_1, x_17);
x_19 = l_Lean_MetavarContext_renameMVar(x_8, x_6, x_18);
x_20 = lean_nat_add(x_9, x_15);
lean_dec(x_9);
lean_ctor_set(x_4, 1, x_20);
lean_ctor_set(x_4, 0, x_19);
x_5 = x_7;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_inc(x_1);
x_22 = l_Lean_MetavarContext_renameMVar(x_8, x_6, x_1);
x_23 = lean_nat_add(x_9, x_15);
lean_dec(x_9);
lean_ctor_set(x_4, 1, x_23);
lean_ctor_set(x_4, 0, x_22);
x_5 = x_7;
goto _start;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_4);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_dec_eq(x_3, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc(x_9);
lean_inc(x_2);
x_27 = l_Lean_Name_appendIndexAfter(x_2, x_9);
x_28 = l_Lean_Name_append___main(x_1, x_27);
x_29 = l_Lean_MetavarContext_renameMVar(x_8, x_6, x_28);
x_30 = lean_nat_add(x_9, x_25);
lean_dec(x_9);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_4 = x_31;
x_5 = x_7;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_1);
x_33 = l_Lean_MetavarContext_renameMVar(x_8, x_6, x_1);
x_34 = lean_nat_add(x_9, x_25);
lean_dec(x_9);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_4 = x_35;
x_5 = x_7;
goto _start;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_13 = lean_st_ref_get(x_9, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_18 = l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(x_16, x_17, x_3);
x_19 = lean_st_ref_take(x_9, x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2(x_1, x_2, x_18, x_25, x_3);
lean_dec(x_18);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
lean_ctor_set(x_20, 0, x_27);
x_28 = lean_st_ref_set(x_9, x_20, x_21);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
x_37 = lean_ctor_get(x_20, 2);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2(x_1, x_2, x_18, x_39, x_3);
lean_dec(x_18);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set(x_42, 2, x_37);
x_43 = lean_st_ref_set(x_9, x_42, x_21);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldl___main___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_tagUntaggedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalSeq___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_2);
x_15 = lean_nat_dec_lt(x_3, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_17 = lean_array_fget(x_2, x_3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Elab_Tactic_evalTactic___main(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_21;
x_4 = x_19;
x_13 = x_20;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_box(0);
x_16 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalSeq___spec__1(x_14, x_13, x_11, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_13);
return x_16;
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalSeq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalSeq___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Lean_Elab_Tactic_evalSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_evalSeq1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_evalSeq1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSeq1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSeq1___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSeq1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__7;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalTacticSeq1Indented(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_evalTacticSeq1Indented___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalTacticSeq1Indented(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticSeq1Indented");
return x_1;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTacticSeq1Indented___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalTacticSeqBracketed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_box(0);
x_18 = lean_alloc_closure((void*)(l_Array_foldlStepMAux___main___at_Lean_Elab_Tactic_evalSeq___spec__1___boxed), 13, 4);
lean_closure_set(x_18, 0, x_11);
lean_closure_set(x_18, 1, x_15);
lean_closure_set(x_18, 2, x_16);
lean_closure_set(x_18, 3, x_17);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_8, 3);
x_21 = l_Lean_replaceRef(x_12, x_20);
lean_dec(x_12);
x_22 = l_Lean_replaceRef(x_21, x_20);
lean_dec(x_21);
x_23 = l_Lean_replaceRef(x_22, x_20);
lean_dec(x_20);
lean_dec(x_22);
lean_ctor_set(x_8, 3, x_23);
x_24 = l_Lean_Elab_Tactic_focus___rarg(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
x_27 = lean_ctor_get(x_8, 2);
x_28 = lean_ctor_get(x_8, 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_29 = l_Lean_replaceRef(x_12, x_28);
lean_dec(x_12);
x_30 = l_Lean_replaceRef(x_29, x_28);
lean_dec(x_29);
x_31 = l_Lean_replaceRef(x_30, x_28);
lean_dec(x_28);
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 3, x_31);
x_33 = l_Lean_Elab_Tactic_focus___rarg(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_32, x_9, x_10);
return x_33;
}
}
}
lean_object* l_Lean_Elab_Tactic_evalTacticSeqBracketed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalTacticSeqBracketed(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticSeqBracketed");
return x_1;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTacticSeqBracketed___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalFocus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic), 10, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = l_Lean_Elab_Tactic_focus___rarg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
lean_object* l_Lean_Elab_Tactic_evalFocus___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalFocus(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("focus");
return x_1;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalFocus___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFocus(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalParen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Elab_Tactic_evalSeq(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_evalParen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalParen(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalParen___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalParen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalTacticSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Elab_Tactic_evalTactic___main(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_evalTacticSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalTacticSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticSeq");
return x_1;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTacticSeq___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1___rarg), 1, 0);
return x_9;
}
}
lean_object* l_Lean_Elab_Tactic_evalChoiceAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_2, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1___rarg(x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_1, x_2);
x_16 = l_Lean_Elab_Tactic_saveBacktrackableState___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Elab_Tactic_evalTactic___main(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_22, 1);
x_29 = lean_ctor_get(x_22, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
x_31 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_32 = lean_nat_dec_eq(x_31, x_30);
lean_dec(x_30);
if (x_32 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_free_object(x_22);
lean_dec(x_20);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_2, x_33);
lean_dec(x_2);
x_2 = x_34;
x_11 = x_28;
goto _start;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_dec(x_22);
x_37 = lean_ctor_get(x_20, 0);
lean_inc(x_37);
x_38 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_39 = lean_nat_dec_eq(x_38, x_37);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_20);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_20);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_2, x_41);
lean_dec(x_2);
x_2 = x_42;
x_11 = x_36;
goto _start;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Tactic_evalChoiceAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalChoiceAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_evalChoiceAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalChoiceAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_evalChoiceAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalChoiceAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_evalChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Syntax_getArgs(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Elab_Tactic_evalChoiceAux___main(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_evalChoice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalChoice(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalChoice___boxed), 10, 0);
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
lean_object* l_Lean_Elab_Tactic_evalSkip(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSkip___rarg), 1, 0);
return x_10;
}
}
lean_object* l_Lean_Elab_Tactic_evalSkip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_evalSkip(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("skip");
return x_1;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSkip___boxed), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSkip(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__3;
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
lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_20 = l_Lean_Elab_Tactic_saveBacktrackableState___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = l_Lean_Elab_Tactic_evalTactic___main(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
lean_dec(x_21);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = 1;
x_13 = x_25;
x_14 = x_24;
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Elab_Tactic_BacktrackableState_restore(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = 0;
x_13 = x_29;
x_14 = x_28;
goto block_19;
}
block_19:
{
if (x_13 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Elab_Tactic_evalFailIfSuccess___closed__3;
x_18 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalFailIfSuccess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failIfSuccess");
return x_1;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalFailIfSuccess___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalTraceState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_goalsToMessageData(x_11);
x_14 = 0;
x_15 = l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTactic___main___spec__10(x_13, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_15;
}
}
lean_object* l_Lean_Elab_Tactic_evalTraceState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTraceState___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalTraceState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_evalTraceState___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
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
x_1 = lean_mk_string("traceState");
return x_1;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__3() {
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
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalAssumption___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalAssumption___rarg___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
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
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_assumption), 6, 1);
lean_closure_set(x_15, 0, x_13);
x_16 = l_Lean_Elab_Tactic_evalAssumption___rarg___closed__1;
x_17 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 11, 1);
lean_closure_set(x_21, 0, x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_13, x_22, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
return x_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalAssumption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalAssumption___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_evalAssumption___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l_Lean_Meta_assumptionAux___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__2() {
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
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_3__introStep___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_3__introStep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_3__introStep___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_3__introStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
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
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_intro), 7, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_1);
x_17 = l___private_Lean_Elab_Tactic_Basic_3__introStep___closed__1;
x_18 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
x_20 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 11, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
x_24 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_14, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l___private_Lean_Elab_Tactic_Basic_3__introStep___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Tactic_Basic_3__introStep___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = l_Lean_Meta_intro1Core(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("h");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalIntro___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_evalIntro___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Tactic_evalIntro___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Quotation_8__letBindRhss___main___closed__13;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l_Lean_Meta_clear___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Meta_clear___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_194; uint8_t x_195; 
x_194 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__9;
lean_inc(x_1);
x_195 = l_Lean_Syntax_isOfKind(x_1, x_194);
if (x_195 == 0)
{
uint8_t x_196; 
x_196 = 0;
x_11 = x_196;
goto block_193;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_197 = l_Lean_Syntax_getArgs(x_1);
x_198 = lean_array_get_size(x_197);
lean_dec(x_197);
x_199 = lean_unsigned_to_nat(2u);
x_200 = lean_nat_dec_eq(x_198, x_199);
lean_dec(x_198);
x_11 = x_200;
goto block_193;
}
block_193:
{
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1___rarg(x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_164; uint8_t x_165; uint8_t x_166; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_164 = l_Lean_nullKind___closed__2;
lean_inc(x_14);
x_165 = l_Lean_Syntax_isOfKind(x_14, x_164);
if (x_165 == 0)
{
uint8_t x_188; 
x_188 = 0;
x_166 = x_188;
goto block_187;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_189 = l_Lean_Syntax_getArgs(x_14);
x_190 = lean_array_get_size(x_189);
lean_dec(x_189);
x_191 = lean_unsigned_to_nat(0u);
x_192 = lean_nat_dec_eq(x_190, x_191);
lean_dec(x_190);
x_166 = x_192;
goto block_187;
}
block_163:
{
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_16 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_17 = l_Lean_Syntax_inhabited;
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get(x_17, x_16, x_18);
x_20 = lean_array_get_size(x_16);
x_21 = l_Array_extract___rarg(x_16, x_13, x_20);
lean_dec(x_20);
lean_dec(x_16);
x_22 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Array_empty___closed__1;
x_27 = lean_array_push(x_26, x_19);
x_28 = l_Lean_nullKind___closed__2;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__11;
x_31 = lean_array_push(x_30, x_29);
x_32 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__9;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_array_push(x_26, x_33);
x_35 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__16;
x_36 = lean_array_push(x_34, x_35);
x_37 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_21, x_21, x_18, x_26);
lean_dec(x_21);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_array_push(x_30, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_32);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_array_push(x_36, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_array_push(x_26, x_42);
x_44 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__7;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = !lean_is_exclusive(x_4);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_4, 6);
lean_inc(x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_4, 6, x_49);
x_50 = l_Lean_Elab_Tactic_evalTactic___main(x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_51 = lean_ctor_get(x_4, 0);
x_52 = lean_ctor_get(x_4, 1);
x_53 = lean_ctor_get(x_4, 2);
x_54 = lean_ctor_get(x_4, 3);
x_55 = lean_ctor_get(x_4, 4);
x_56 = lean_ctor_get(x_4, 5);
x_57 = lean_ctor_get(x_4, 6);
x_58 = lean_ctor_get(x_4, 7);
x_59 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
x_60 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_4);
lean_inc(x_45);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_45);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
x_63 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_63, 0, x_51);
lean_ctor_set(x_63, 1, x_52);
lean_ctor_set(x_63, 2, x_53);
lean_ctor_set(x_63, 3, x_54);
lean_ctor_set(x_63, 4, x_55);
lean_ctor_set(x_63, 5, x_56);
lean_ctor_set(x_63, 6, x_62);
lean_ctor_set(x_63, 7, x_58);
lean_ctor_set_uint8(x_63, sizeof(void*)*8, x_59);
lean_ctor_set_uint8(x_63, sizeof(void*)*8 + 1, x_60);
x_64 = l_Lean_Elab_Tactic_evalTactic___main(x_45, x_2, x_3, x_63, x_5, x_6, x_7, x_8, x_9, x_25);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Lean_Syntax_getArg(x_14, x_65);
lean_dec(x_14);
x_67 = l_Lean_identKind___closed__2;
lean_inc(x_66);
x_68 = l_Lean_Syntax_isOfKind(x_66, x_67);
if (x_68 == 0)
{
uint8_t x_69; lean_object* x_155; uint8_t x_156; 
x_155 = l_Lean_mkHole___closed__2;
lean_inc(x_66);
x_156 = l_Lean_Syntax_isOfKind(x_66, x_155);
if (x_156 == 0)
{
uint8_t x_157; 
x_157 = 0;
x_69 = x_157;
goto block_154;
}
else
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_158 = l_Lean_Syntax_getArgs(x_66);
x_159 = lean_array_get_size(x_158);
lean_dec(x_158);
x_160 = lean_nat_dec_eq(x_159, x_13);
lean_dec(x_159);
x_69 = x_160;
goto block_154;
}
block_154:
{
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_70 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Elab_Tactic_evalIntro___closed__4;
x_77 = l_Lean_addMacroScope(x_74, x_76, x_71);
x_78 = lean_box(0);
x_79 = l_Lean_SourceInfo_inhabited___closed__1;
x_80 = l_Lean_Elab_Tactic_evalIntro___closed__3;
x_81 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_81, 2, x_77);
lean_ctor_set(x_81, 3, x_78);
x_82 = l_Array_empty___closed__1;
lean_inc(x_81);
x_83 = lean_array_push(x_82, x_81);
x_84 = l_Lean_nullKind___closed__2;
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__11;
lean_inc(x_85);
x_87 = lean_array_push(x_86, x_85);
x_88 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__9;
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = lean_array_push(x_82, x_89);
x_91 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__16;
x_92 = lean_array_push(x_90, x_91);
x_93 = l_Lean_Elab_Tactic_evalIntro___closed__5;
x_94 = lean_array_push(x_93, x_81);
x_95 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__6;
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_array_push(x_82, x_96);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_84);
lean_ctor_set(x_98, 1, x_97);
x_99 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__4;
x_100 = lean_array_push(x_99, x_98);
x_101 = l___private_Lean_Elab_Quotation_8__letBindRhss___main___closed__13;
x_102 = lean_array_push(x_100, x_101);
x_103 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__9;
x_104 = lean_array_push(x_102, x_103);
x_105 = lean_array_push(x_82, x_66);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_84);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_array_push(x_82, x_106);
x_108 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_109 = lean_array_push(x_107, x_108);
x_110 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__12;
x_111 = lean_array_push(x_109, x_110);
x_112 = l_Lean_Elab_Tactic_evalIntro___closed__6;
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
x_114 = lean_array_push(x_82, x_113);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_84);
lean_ctor_set(x_115, 1, x_114);
x_116 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__16;
x_117 = lean_array_push(x_116, x_115);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_84);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_array_push(x_104, x_118);
x_120 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__14;
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_array_push(x_92, x_121);
x_123 = lean_array_push(x_122, x_91);
x_124 = l_Lean_Elab_Tactic_evalIntro___closed__9;
x_125 = lean_array_push(x_124, x_85);
x_126 = l_Lean_Elab_Tactic_evalIntro___closed__7;
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
x_128 = lean_array_push(x_123, x_127);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_84);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_array_push(x_82, x_129);
x_131 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__7;
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_133 = !lean_is_exclusive(x_4);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_4, 6);
lean_inc(x_132);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_1);
lean_ctor_set(x_135, 1, x_132);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
lean_ctor_set(x_4, 6, x_136);
x_137 = l_Lean_Elab_Tactic_evalTactic___main(x_132, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_138 = lean_ctor_get(x_4, 0);
x_139 = lean_ctor_get(x_4, 1);
x_140 = lean_ctor_get(x_4, 2);
x_141 = lean_ctor_get(x_4, 3);
x_142 = lean_ctor_get(x_4, 4);
x_143 = lean_ctor_get(x_4, 5);
x_144 = lean_ctor_get(x_4, 6);
x_145 = lean_ctor_get(x_4, 7);
x_146 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
x_147 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_4);
lean_inc(x_132);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_1);
lean_ctor_set(x_148, 1, x_132);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_144);
x_150 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_150, 0, x_138);
lean_ctor_set(x_150, 1, x_139);
lean_ctor_set(x_150, 2, x_140);
lean_ctor_set(x_150, 3, x_141);
lean_ctor_set(x_150, 4, x_142);
lean_ctor_set(x_150, 5, x_143);
lean_ctor_set(x_150, 6, x_149);
lean_ctor_set(x_150, 7, x_145);
lean_ctor_set_uint8(x_150, sizeof(void*)*8, x_146);
lean_ctor_set_uint8(x_150, sizeof(void*)*8 + 1, x_147);
x_151 = l_Lean_Elab_Tactic_evalTactic___main(x_132, x_2, x_3, x_150, x_5, x_6, x_7, x_8, x_9, x_75);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_66);
lean_dec(x_1);
x_152 = l_Lean_mkThunk___closed__1;
x_153 = l___private_Lean_Elab_Tactic_Basic_3__introStep(x_152, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_153;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_1);
x_161 = l_Lean_Syntax_getId(x_66);
lean_dec(x_66);
x_162 = l___private_Lean_Elab_Tactic_Basic_3__introStep(x_161, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_162;
}
}
}
block_187:
{
if (x_166 == 0)
{
if (x_165 == 0)
{
uint8_t x_167; 
x_167 = 0;
x_15 = x_167;
goto block_163;
}
else
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = l_Lean_Syntax_getArgs(x_14);
x_169 = lean_array_get_size(x_168);
lean_dec(x_168);
x_170 = lean_nat_dec_eq(x_169, x_13);
lean_dec(x_169);
x_15 = x_170;
goto block_163;
}
}
else
{
lean_object* x_171; 
lean_dec(x_14);
lean_dec(x_1);
x_171 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_dec(x_172);
lean_inc(x_174);
x_176 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntro___lambda__1), 6, 1);
lean_closure_set(x_176, 0, x_174);
x_177 = l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
x_178 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_178, 0, x_176);
lean_closure_set(x_178, 1, x_177);
x_179 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_179, 0, x_178);
x_180 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 11, 1);
lean_closure_set(x_180, 0, x_175);
x_181 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_181, 0, x_179);
lean_closure_set(x_181, 1, x_180);
x_182 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_174, x_181, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_173);
return x_182;
}
else
{
uint8_t x_183; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_183 = !lean_is_exclusive(x_171);
if (x_183 == 0)
{
return x_171;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_171, 0);
x_185 = lean_ctor_get(x_171, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_171);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
}
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntro), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntro(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__9;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntroMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = l_Lean_Syntax_getArg(x_1, x_33);
x_35 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_st_ref_get(x_9, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_st_ref_get(x_9, x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_8, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_8, 2);
lean_inc(x_47);
lean_inc(x_41);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_5__expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_48, 0, x_41);
x_49 = x_48;
x_50 = lean_environment_main_module(x_41);
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_36);
lean_ctor_set(x_51, 3, x_46);
lean_ctor_set(x_51, 4, x_47);
x_52 = l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic(x_1, x_34, x_51, x_45);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_st_ref_take(x_9, x_44);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_56, 1);
lean_dec(x_59);
lean_ctor_set(x_56, 1, x_54);
x_60 = lean_st_ref_set(x_9, x_56, x_57);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_11 = x_53;
x_12 = x_61;
goto block_32;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_56, 0);
x_63 = lean_ctor_get(x_56, 2);
x_64 = lean_ctor_get(x_56, 3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_56);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_54);
lean_ctor_set(x_65, 2, x_63);
lean_ctor_set(x_65, 3, x_64);
x_66 = lean_st_ref_set(x_9, x_65, x_57);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_11 = x_53;
x_12 = x_67;
goto block_32;
}
block_32:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 6);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_4, 6, x_16);
x_17 = l_Lean_Elab_Tactic_evalTactic___main(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
x_20 = lean_ctor_get(x_4, 2);
x_21 = lean_ctor_get(x_4, 3);
x_22 = lean_ctor_get(x_4, 4);
x_23 = lean_ctor_get(x_4, 5);
x_24 = lean_ctor_get(x_4, 6);
x_25 = lean_ctor_get(x_4, 7);
x_26 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
x_27 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
lean_inc(x_11);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_11);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
x_30 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_19);
lean_ctor_set(x_30, 2, x_20);
lean_ctor_set(x_30, 3, x_21);
lean_ctor_set(x_30, 4, x_22);
lean_ctor_set(x_30, 5, x_23);
lean_ctor_set(x_30, 6, x_29);
lean_ctor_set(x_30, 7, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*8, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*8 + 1, x_27);
x_31 = l_Lean_Elab_Tactic_evalTactic___main(x_11, x_2, x_3, x_30, x_5, x_6, x_7, x_8, x_9, x_12);
return x_31;
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("introMatch");
return x_1;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntroMatch), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_4__getIntrosSize___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l___private_Lean_Elab_Tactic_Basic_4__getIntrosSize___main(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
return x_5;
}
case 8:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 3);
x_7 = l___private_Lean_Elab_Tactic_Basic_4__getIntrosSize___main(x_6);
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
lean_object* l___private_Lean_Elab_Tactic_Basic_4__getIntrosSize___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Basic_4__getIntrosSize___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_4__getIntrosSize(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Basic_4__getIntrosSize___main(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_4__getIntrosSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Basic_4__getIntrosSize(x_1);
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
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_8 = lean_array_get_size(x_1);
x_9 = x_1;
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_umapMAux___main___at_Lean_Elab_Tactic_evalIntros___spec__1(x_10, x_9);
x_12 = x_11;
x_13 = l_Array_toList___rarg(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = l_Lean_Meta_introNCore(x_2, x_8, x_13, x_14, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_getMVarType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_instantiateMVars___at_Lean_Meta_instantiateLocalDeclMVars___spec__1(x_8, x_2, x_3, x_4, x_5, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_Tactic_Basic_4__getIntrosSize___main(x_11);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = 0;
x_16 = l_Lean_Meta_introNCore(x_1, x_13, x_14, x_15, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_14);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
uint8_t x_26; 
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
else
{
uint8_t x_30; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
return x_7;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalIntros___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("intros");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalIntros___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l_Lean_Elab_Tactic_evalIntros___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntros(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_Elab_Tactic_evalIntros___closed__2;
lean_inc(x_1);
x_59 = l_Lean_Syntax_isOfKind(x_1, x_58);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = 0;
x_11 = x_60;
goto block_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = l_Lean_Syntax_getArgs(x_1);
x_62 = lean_array_get_size(x_61);
lean_dec(x_61);
x_63 = lean_unsigned_to_nat(2u);
x_64 = lean_nat_dec_eq(x_62, x_63);
lean_dec(x_62);
x_11 = x_64;
goto block_57;
}
block_57:
{
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1___rarg(x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_50; uint8_t x_51; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_50 = l_Lean_nullKind___closed__2;
lean_inc(x_14);
x_51 = l_Lean_Syntax_isOfKind(x_14, x_50);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = 0;
x_15 = x_52;
goto block_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = l_Lean_Syntax_getArgs(x_14);
x_54 = lean_array_get_size(x_53);
lean_dec(x_53);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_nat_dec_eq(x_54, x_55);
lean_dec(x_54);
x_15 = x_56;
goto block_49;
}
block_49:
{
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
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
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntros___lambda__1), 7, 2);
lean_closure_set(x_22, 0, x_16);
lean_closure_set(x_22, 1, x_20);
x_23 = l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
x_24 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 11, 1);
lean_closure_set(x_26, 0, x_21);
x_27 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_27, 0, x_25);
lean_closure_set(x_27, 1, x_26);
x_28 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_20, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_14);
x_33 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
lean_inc(x_36);
x_38 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntros___lambda__2), 6, 1);
lean_closure_set(x_38, 0, x_36);
x_39 = l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
x_40 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_40, 0, x_38);
lean_closure_set(x_40, 1, x_39);
x_41 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 11, 1);
lean_closure_set(x_42, 0, x_37);
x_43 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_43, 0, x_41);
lean_closure_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_36, x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
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
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_33);
if (x_45 == 0)
{
return x_33;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_33, 0);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_33);
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
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntros), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntros(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_evalIntros___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_8, 3);
x_13 = l_Lean_replaceRef(x_1, x_12);
x_14 = l_Lean_replaceRef(x_13, x_12);
lean_dec(x_13);
x_15 = l_Lean_replaceRef(x_14, x_12);
lean_dec(x_12);
lean_dec(x_14);
lean_ctor_set(x_8, 3, x_15);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l_Lean_Elab_Term_isLocalIdent_x3f(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_20 = l_System_FilePath_dirName___closed__1;
x_21 = l_Lean_Name_toStringWithSep___main(x_20, x_19);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_Meta_clear___lambda__1___closed__6;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_8);
lean_dec(x_6);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_17, 0);
lean_inc(x_31);
lean_dec(x_17);
x_32 = l_Lean_Expr_fvarId_x21(x_31);
lean_dec(x_31);
lean_ctor_set(x_16, 0, x_32);
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_dec(x_16);
x_34 = lean_ctor_get(x_17, 0);
lean_inc(x_34);
lean_dec(x_17);
x_35 = l_Lean_Expr_fvarId_x21(x_34);
lean_dec(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_8, 0);
x_38 = lean_ctor_get(x_8, 1);
x_39 = lean_ctor_get(x_8, 2);
x_40 = lean_ctor_get(x_8, 3);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_8);
x_41 = l_Lean_replaceRef(x_1, x_40);
x_42 = l_Lean_replaceRef(x_41, x_40);
lean_dec(x_41);
x_43 = l_Lean_replaceRef(x_42, x_40);
lean_dec(x_40);
lean_dec(x_42);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_38);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_43);
lean_inc(x_6);
lean_inc(x_1);
x_45 = l_Lean_Elab_Term_isLocalIdent_x3f(x_1, x_4, x_5, x_6, x_7, x_44, x_9, x_10);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_49 = l_System_FilePath_dirName___closed__1;
x_50 = l_Lean_Name_toStringWithSep___main(x_49, x_48);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_Meta_clear___lambda__1___closed__6;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg(x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_44, x_9, x_47);
lean_dec(x_44);
lean_dec(x_6);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_44);
lean_dec(x_6);
lean_dec(x_1);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_59 = x_45;
} else {
 lean_dec_ref(x_45);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_46, 0);
lean_inc(x_60);
lean_dec(x_46);
x_61 = l_Lean_Expr_fvarId_x21(x_60);
lean_dec(x_60);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
return x_62;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_getFVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getFVarId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_getFVarIds___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_1, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_14 = x_2;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_2, x_1);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_fset(x_2, x_1, x_17);
x_19 = x_16;
lean_inc(x_9);
lean_inc(x_7);
x_20 = l_Lean_Elab_Tactic_getFVarId(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_1, x_23);
x_25 = x_21;
x_26 = lean_array_fset(x_18, x_1, x_25);
lean_dec(x_1);
x_1 = x_24;
x_2 = x_26;
x_11 = x_22;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = x_1;
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Tactic_getFVarIds___spec__1___boxed), 11, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_11);
x_14 = x_13;
x_15 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_getFVarIds___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_umapMAux___main___at_Lean_Elab_Tactic_getFVarIds___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalRevert___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l_Lean_Meta_revert___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_evalRevert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_44; uint8_t x_45; 
x_44 = l_Lean_Elab_Tactic_evalRevert___closed__1;
lean_inc(x_1);
x_45 = l_Lean_Syntax_isOfKind(x_1, x_44);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = 0;
x_11 = x_46;
goto block_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = l_Lean_Syntax_getArgs(x_1);
x_48 = lean_array_get_size(x_47);
lean_dec(x_47);
x_49 = lean_unsigned_to_nat(2u);
x_50 = lean_nat_dec_eq(x_48, x_49);
lean_dec(x_48);
x_11 = x_50;
goto block_43;
}
block_43:
{
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1___rarg(x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Lean_Elab_Tactic_getFVarIds(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_25 = l_Lean_Meta_revert(x_19, x_22, x_24, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_20);
x_30 = l_Lean_Elab_Tactic_setGoals(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
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
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
return x_16;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_16, 0);
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_16);
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
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRevert), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRevert(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_evalRevert___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Name_inhabited;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_local_ctx_find(x_1, x_11);
lean_inc(x_3);
lean_inc(x_1);
x_13 = lean_local_ctx_find(x_1, x_3);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Name_quickLt(x_11, x_3);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_swap(x_4, x_5, x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_21 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_4 = x_18;
x_5 = x_20;
x_6 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_11);
x_23 = lean_array_swap(x_4, x_5, x_6);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_26 = lean_nat_add(x_6, x_24);
lean_dec(x_6);
x_4 = x_23;
x_5 = x_25;
x_6 = x_26;
goto _start;
}
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_6, x_28);
lean_dec(x_6);
x_6 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
x_33 = l_Lean_LocalDecl_index(x_32);
lean_dec(x_32);
x_34 = l_Lean_LocalDecl_index(x_31);
lean_dec(x_31);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_6, x_36);
lean_dec(x_6);
x_6 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_array_swap(x_4, x_5, x_6);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_5, x_40);
lean_dec(x_5);
x_42 = lean_nat_add(x_6, x_40);
lean_dec(x_6);
x_4 = x_39;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Name_inhabited;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_local_ctx_find(x_1, x_11);
lean_inc(x_3);
lean_inc(x_1);
x_13 = lean_local_ctx_find(x_1, x_3);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Name_quickLt(x_11, x_3);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_swap(x_4, x_5, x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_21 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_4 = x_18;
x_5 = x_20;
x_6 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_11);
x_23 = lean_array_swap(x_4, x_5, x_6);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_26 = lean_nat_add(x_6, x_24);
lean_dec(x_6);
x_4 = x_23;
x_5 = x_25;
x_6 = x_26;
goto _start;
}
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_6, x_28);
lean_dec(x_6);
x_6 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
x_33 = l_Lean_LocalDecl_index(x_32);
lean_dec(x_32);
x_34 = l_Lean_LocalDecl_index(x_31);
lean_dec(x_31);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_6, x_36);
lean_dec(x_6);
x_6 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_array_swap(x_4, x_5, x_6);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_5, x_40);
lean_dec(x_5);
x_42 = lean_nat_add(x_6, x_40);
lean_dec(x_6);
x_4 = x_39;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Name_inhabited;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_local_ctx_find(x_1, x_11);
lean_inc(x_3);
lean_inc(x_1);
x_13 = lean_local_ctx_find(x_1, x_3);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Name_quickLt(x_11, x_3);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_swap(x_4, x_5, x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_21 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_4 = x_18;
x_5 = x_20;
x_6 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_11);
x_23 = lean_array_swap(x_4, x_5, x_6);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_26 = lean_nat_add(x_6, x_24);
lean_dec(x_6);
x_4 = x_23;
x_5 = x_25;
x_6 = x_26;
goto _start;
}
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_6, x_28);
lean_dec(x_6);
x_6 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
x_33 = l_Lean_LocalDecl_index(x_32);
lean_dec(x_32);
x_34 = l_Lean_LocalDecl_index(x_31);
lean_dec(x_31);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_6, x_36);
lean_dec(x_6);
x_6 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_array_swap(x_4, x_5, x_6);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_5, x_40);
lean_dec(x_5);
x_42 = lean_nat_add(x_6, x_40);
lean_dec(x_6);
x_4 = x_39;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Name_inhabited;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_local_ctx_find(x_1, x_11);
lean_inc(x_3);
lean_inc(x_1);
x_13 = lean_local_ctx_find(x_1, x_3);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Name_quickLt(x_11, x_3);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_swap(x_4, x_5, x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_21 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_4 = x_18;
x_5 = x_20;
x_6 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_11);
x_23 = lean_array_swap(x_4, x_5, x_6);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_26 = lean_nat_add(x_6, x_24);
lean_dec(x_6);
x_4 = x_23;
x_5 = x_25;
x_6 = x_26;
goto _start;
}
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_6, x_28);
lean_dec(x_6);
x_6 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
x_33 = l_Lean_LocalDecl_index(x_32);
lean_dec(x_32);
x_34 = l_Lean_LocalDecl_index(x_31);
lean_dec(x_31);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_6, x_36);
lean_dec(x_6);
x_6 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_array_swap(x_4, x_5, x_6);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_5, x_40);
lean_dec(x_5);
x_42 = lean_nat_add(x_6, x_40);
lean_dec(x_6);
x_4 = x_39;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Name_inhabited;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_local_ctx_find(x_1, x_11);
lean_inc(x_3);
lean_inc(x_1);
x_13 = lean_local_ctx_find(x_1, x_3);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Name_quickLt(x_11, x_3);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_swap(x_4, x_5, x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_21 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_4 = x_18;
x_5 = x_20;
x_6 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_11);
x_23 = lean_array_swap(x_4, x_5, x_6);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_26 = lean_nat_add(x_6, x_24);
lean_dec(x_6);
x_4 = x_23;
x_5 = x_25;
x_6 = x_26;
goto _start;
}
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_6, x_28);
lean_dec(x_6);
x_6 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
x_33 = l_Lean_LocalDecl_index(x_32);
lean_dec(x_32);
x_34 = l_Lean_LocalDecl_index(x_31);
lean_dec(x_31);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_6, x_36);
lean_dec(x_6);
x_6 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_array_swap(x_4, x_5, x_6);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_5, x_40);
lean_dec(x_5);
x_42 = lean_nat_add(x_6, x_40);
lean_dec(x_6);
x_4 = x_39;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Name_inhabited;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_local_ctx_find(x_1, x_11);
lean_inc(x_3);
lean_inc(x_1);
x_13 = lean_local_ctx_find(x_1, x_3);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Name_quickLt(x_11, x_3);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_swap(x_4, x_5, x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_21 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_4 = x_18;
x_5 = x_20;
x_6 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_11);
x_23 = lean_array_swap(x_4, x_5, x_6);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_26 = lean_nat_add(x_6, x_24);
lean_dec(x_6);
x_4 = x_23;
x_5 = x_25;
x_6 = x_26;
goto _start;
}
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_6, x_28);
lean_dec(x_6);
x_6 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
x_33 = l_Lean_LocalDecl_index(x_32);
lean_dec(x_32);
x_34 = l_Lean_LocalDecl_index(x_31);
lean_dec(x_31);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_6, x_36);
lean_dec(x_6);
x_6 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_array_swap(x_4, x_5, x_6);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_5, x_40);
lean_dec(x_5);
x_42 = lean_nat_add(x_6, x_40);
lean_dec(x_6);
x_4 = x_39;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Name_inhabited;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_local_ctx_find(x_1, x_11);
lean_inc(x_3);
lean_inc(x_1);
x_13 = lean_local_ctx_find(x_1, x_3);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Name_quickLt(x_11, x_3);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_swap(x_4, x_5, x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_21 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_4 = x_18;
x_5 = x_20;
x_6 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_11);
x_23 = lean_array_swap(x_4, x_5, x_6);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_26 = lean_nat_add(x_6, x_24);
lean_dec(x_6);
x_4 = x_23;
x_5 = x_25;
x_6 = x_26;
goto _start;
}
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_6, x_28);
lean_dec(x_6);
x_6 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
x_33 = l_Lean_LocalDecl_index(x_32);
lean_dec(x_32);
x_34 = l_Lean_LocalDecl_index(x_31);
lean_dec(x_31);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_6, x_36);
lean_dec(x_6);
x_6 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_array_swap(x_4, x_5, x_6);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_5, x_40);
lean_dec(x_5);
x_42 = lean_nat_add(x_6, x_40);
lean_dec(x_6);
x_4 = x_39;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Name_inhabited;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_local_ctx_find(x_1, x_11);
lean_inc(x_3);
lean_inc(x_1);
x_13 = lean_local_ctx_find(x_1, x_3);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Name_quickLt(x_11, x_3);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_swap(x_4, x_5, x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_21 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_4 = x_18;
x_5 = x_20;
x_6 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_11);
x_23 = lean_array_swap(x_4, x_5, x_6);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_26 = lean_nat_add(x_6, x_24);
lean_dec(x_6);
x_4 = x_23;
x_5 = x_25;
x_6 = x_26;
goto _start;
}
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_6, x_28);
lean_dec(x_6);
x_6 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
x_33 = l_Lean_LocalDecl_index(x_32);
lean_dec(x_32);
x_34 = l_Lean_LocalDecl_index(x_31);
lean_dec(x_31);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_6, x_36);
lean_dec(x_6);
x_6 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_array_swap(x_4, x_5, x_6);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_5, x_40);
lean_dec(x_5);
x_42 = lean_nat_add(x_6, x_40);
lean_dec(x_6);
x_4 = x_39;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Name_inhabited;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_local_ctx_find(x_1, x_11);
lean_inc(x_3);
lean_inc(x_1);
x_13 = lean_local_ctx_find(x_1, x_3);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Name_quickLt(x_11, x_3);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_swap(x_4, x_5, x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_21 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_4 = x_18;
x_5 = x_20;
x_6 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_11);
x_23 = lean_array_swap(x_4, x_5, x_6);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_26 = lean_nat_add(x_6, x_24);
lean_dec(x_6);
x_4 = x_23;
x_5 = x_25;
x_6 = x_26;
goto _start;
}
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_6, x_28);
lean_dec(x_6);
x_6 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
x_33 = l_Lean_LocalDecl_index(x_32);
lean_dec(x_32);
x_34 = l_Lean_LocalDecl_index(x_31);
lean_dec(x_31);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_6, x_36);
lean_dec(x_6);
x_6 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_array_swap(x_4, x_5, x_6);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_5, x_40);
lean_dec(x_5);
x_42 = lean_nat_add(x_6, x_40);
lean_dec(x_6);
x_4 = x_39;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Name_inhabited;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_local_ctx_find(x_1, x_11);
lean_inc(x_3);
lean_inc(x_1);
x_13 = lean_local_ctx_find(x_1, x_3);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Name_quickLt(x_11, x_3);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_swap(x_4, x_5, x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_21 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_4 = x_18;
x_5 = x_20;
x_6 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_11);
x_23 = lean_array_swap(x_4, x_5, x_6);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_26 = lean_nat_add(x_6, x_24);
lean_dec(x_6);
x_4 = x_23;
x_5 = x_25;
x_6 = x_26;
goto _start;
}
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_6, x_28);
lean_dec(x_6);
x_6 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
x_33 = l_Lean_LocalDecl_index(x_32);
lean_dec(x_32);
x_34 = l_Lean_LocalDecl_index(x_31);
lean_dec(x_31);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_6, x_36);
lean_dec(x_6);
x_6 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_array_swap(x_4, x_5, x_6);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_5, x_40);
lean_dec(x_5);
x_42 = lean_nat_add(x_6, x_40);
lean_dec(x_6);
x_4 = x_39;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Name_inhabited;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_local_ctx_find(x_1, x_11);
lean_inc(x_3);
lean_inc(x_1);
x_13 = lean_local_ctx_find(x_1, x_3);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Name_quickLt(x_11, x_3);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_swap(x_4, x_5, x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_21 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_4 = x_18;
x_5 = x_20;
x_6 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_11);
x_23 = lean_array_swap(x_4, x_5, x_6);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_26 = lean_nat_add(x_6, x_24);
lean_dec(x_6);
x_4 = x_23;
x_5 = x_25;
x_6 = x_26;
goto _start;
}
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_6, x_28);
lean_dec(x_6);
x_6 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
x_33 = l_Lean_LocalDecl_index(x_32);
lean_dec(x_32);
x_34 = l_Lean_LocalDecl_index(x_31);
lean_dec(x_31);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_6, x_36);
lean_dec(x_6);
x_6 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_array_swap(x_4, x_5, x_6);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_5, x_40);
lean_dec(x_5);
x_42 = lean_nat_add(x_6, x_40);
lean_dec(x_6);
x_4 = x_39;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Name_inhabited;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_local_ctx_find(x_1, x_11);
lean_inc(x_3);
lean_inc(x_1);
x_13 = lean_local_ctx_find(x_1, x_3);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Name_quickLt(x_11, x_3);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_swap(x_4, x_5, x_6);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_21 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_4 = x_18;
x_5 = x_20;
x_6 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_11);
x_23 = lean_array_swap(x_4, x_5, x_6);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_26 = lean_nat_add(x_6, x_24);
lean_dec(x_6);
x_4 = x_23;
x_5 = x_25;
x_6 = x_26;
goto _start;
}
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_6, x_28);
lean_dec(x_6);
x_6 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
x_33 = l_Lean_LocalDecl_index(x_32);
lean_dec(x_32);
x_34 = l_Lean_LocalDecl_index(x_31);
lean_dec(x_31);
x_35 = lean_nat_dec_lt(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_6, x_36);
lean_dec(x_6);
x_6 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_array_swap(x_4, x_5, x_6);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_5, x_40);
lean_dec(x_5);
x_42 = lean_nat_add(x_6, x_40);
lean_dec(x_6);
x_4 = x_39;
x_5 = x_41;
x_6 = x_42;
goto _start;
}
}
}
}
}
}
lean_object* l_Array_qsortAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_3, x_4);
if (x_14 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_15 = lean_nat_add(x_3, x_4);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_div(x_15, x_16);
lean_dec(x_15);
x_86 = l_Lean_Name_inhabited;
x_87 = lean_array_get(x_86, x_2, x_17);
x_88 = lean_array_get(x_86, x_2, x_3);
lean_inc(x_87);
lean_inc(x_1);
x_89 = lean_local_ctx_find(x_1, x_87);
lean_inc(x_88);
lean_inc(x_1);
x_90 = lean_local_ctx_find(x_1, x_88);
if (lean_obj_tag(x_89) == 0)
{
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = l_Lean_Name_quickLt(x_87, x_88);
lean_dec(x_88);
lean_dec(x_87);
if (x_91 == 0)
{
x_18 = x_2;
goto block_85;
}
else
{
lean_object* x_92; 
x_92 = lean_array_swap(x_2, x_3, x_17);
x_18 = x_92;
goto block_85;
}
}
else
{
lean_object* x_93; 
lean_dec(x_90);
lean_dec(x_88);
lean_dec(x_87);
x_93 = lean_array_swap(x_2, x_3, x_17);
x_18 = x_93;
goto block_85;
}
}
else
{
lean_dec(x_88);
lean_dec(x_87);
if (lean_obj_tag(x_90) == 0)
{
lean_dec(x_89);
x_18 = x_2;
goto block_85;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
lean_dec(x_89);
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
lean_dec(x_90);
x_96 = l_Lean_LocalDecl_index(x_95);
lean_dec(x_95);
x_97 = l_Lean_LocalDecl_index(x_94);
lean_dec(x_94);
x_98 = lean_nat_dec_lt(x_96, x_97);
lean_dec(x_97);
lean_dec(x_96);
if (x_98 == 0)
{
x_18 = x_2;
goto block_85;
}
else
{
lean_object* x_99; 
x_99 = lean_array_swap(x_2, x_3, x_17);
x_18 = x_99;
goto block_85;
}
}
}
block_85:
{
lean_object* x_19; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_45 = l_Lean_Name_inhabited;
x_46 = lean_array_get(x_45, x_18, x_4);
x_70 = lean_array_get(x_45, x_18, x_3);
lean_inc(x_46);
lean_inc(x_1);
x_71 = lean_local_ctx_find(x_1, x_46);
lean_inc(x_70);
lean_inc(x_1);
x_72 = lean_local_ctx_find(x_1, x_70);
if (lean_obj_tag(x_71) == 0)
{
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = l_Lean_Name_quickLt(x_46, x_70);
lean_dec(x_70);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_box(0);
x_47 = x_74;
goto block_69;
}
else
{
lean_object* x_75; 
lean_dec(x_46);
x_75 = lean_box(0);
x_19 = x_75;
goto block_44;
}
}
else
{
lean_object* x_76; 
lean_dec(x_72);
lean_dec(x_70);
lean_dec(x_46);
x_76 = lean_box(0);
x_19 = x_76;
goto block_44;
}
}
else
{
lean_dec(x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_77; 
lean_dec(x_71);
x_77 = lean_box(0);
x_47 = x_77;
goto block_69;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = lean_ctor_get(x_71, 0);
lean_inc(x_78);
lean_dec(x_71);
x_79 = lean_ctor_get(x_72, 0);
lean_inc(x_79);
lean_dec(x_72);
x_80 = l_Lean_LocalDecl_index(x_79);
lean_dec(x_79);
x_81 = l_Lean_LocalDecl_index(x_78);
lean_dec(x_78);
x_82 = lean_nat_dec_lt(x_80, x_81);
lean_dec(x_81);
lean_dec(x_80);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_box(0);
x_47 = x_83;
goto block_69;
}
else
{
lean_object* x_84; 
lean_dec(x_46);
x_84 = lean_box(0);
x_19 = x_84;
goto block_44;
}
}
}
block_44:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
x_20 = lean_array_swap(x_18, x_3, x_4);
x_21 = l_Lean_Name_inhabited;
x_22 = lean_array_get(x_21, x_20, x_17);
x_23 = lean_array_get(x_21, x_20, x_4);
lean_inc(x_22);
lean_inc(x_1);
x_24 = lean_local_ctx_find(x_1, x_22);
lean_inc(x_23);
lean_inc(x_1);
x_25 = lean_local_ctx_find(x_1, x_23);
if (lean_obj_tag(x_24) == 0)
{
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Name_quickLt(x_22, x_23);
lean_dec(x_22);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_17);
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_27 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__2(x_1, x_4, x_23, x_20, x_3, x_3);
x_5 = x_27;
goto block_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_23);
x_28 = lean_array_swap(x_20, x_17, x_4);
lean_dec(x_17);
x_29 = lean_array_get(x_21, x_28, x_4);
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_30 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__3(x_1, x_4, x_29, x_28, x_3, x_3);
x_5 = x_30;
goto block_13;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
x_31 = lean_array_swap(x_20, x_17, x_4);
lean_dec(x_17);
x_32 = lean_array_get(x_21, x_31, x_4);
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_33 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__4(x_1, x_4, x_32, x_31, x_3, x_3);
x_5 = x_33;
goto block_13;
}
}
else
{
lean_dec(x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_17);
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_34 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__5(x_1, x_4, x_23, x_20, x_3, x_3);
x_5 = x_34;
goto block_13;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_24, 0);
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
lean_dec(x_25);
x_37 = l_Lean_LocalDecl_index(x_36);
lean_dec(x_36);
x_38 = l_Lean_LocalDecl_index(x_35);
lean_dec(x_35);
x_39 = lean_nat_dec_lt(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_17);
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_40 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__6(x_1, x_4, x_23, x_20, x_3, x_3);
x_5 = x_40;
goto block_13;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_23);
x_41 = lean_array_swap(x_20, x_17, x_4);
lean_dec(x_17);
x_42 = lean_array_get(x_21, x_41, x_4);
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_43 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__7(x_1, x_4, x_42, x_41, x_3, x_3);
x_5 = x_43;
goto block_13;
}
}
}
}
block_69:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_47);
x_48 = lean_array_get(x_45, x_18, x_17);
lean_inc(x_48);
lean_inc(x_1);
x_49 = lean_local_ctx_find(x_1, x_48);
lean_inc(x_46);
lean_inc(x_1);
x_50 = lean_local_ctx_find(x_1, x_46);
if (lean_obj_tag(x_49) == 0)
{
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = l_Lean_Name_quickLt(x_48, x_46);
lean_dec(x_48);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_17);
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_52 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__8(x_1, x_4, x_46, x_18, x_3, x_3);
x_5 = x_52;
goto block_13;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_46);
x_53 = lean_array_swap(x_18, x_17, x_4);
lean_dec(x_17);
x_54 = lean_array_get(x_45, x_53, x_4);
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_55 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__9(x_1, x_4, x_54, x_53, x_3, x_3);
x_5 = x_55;
goto block_13;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_46);
x_56 = lean_array_swap(x_18, x_17, x_4);
lean_dec(x_17);
x_57 = lean_array_get(x_45, x_56, x_4);
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_58 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__10(x_1, x_4, x_57, x_56, x_3, x_3);
x_5 = x_58;
goto block_13;
}
}
else
{
lean_dec(x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_59; 
lean_dec(x_49);
lean_dec(x_17);
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_59 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__11(x_1, x_4, x_46, x_18, x_3, x_3);
x_5 = x_59;
goto block_13;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_49, 0);
lean_inc(x_60);
lean_dec(x_49);
x_61 = lean_ctor_get(x_50, 0);
lean_inc(x_61);
lean_dec(x_50);
x_62 = l_Lean_LocalDecl_index(x_61);
lean_dec(x_61);
x_63 = l_Lean_LocalDecl_index(x_60);
lean_dec(x_60);
x_64 = lean_nat_dec_lt(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_17);
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_65 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__12(x_1, x_4, x_46, x_18, x_3, x_3);
x_5 = x_65;
goto block_13;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_46);
x_66 = lean_array_swap(x_18, x_17, x_4);
lean_dec(x_17);
x_67 = lean_array_get(x_45, x_66, x_4);
lean_inc_n(x_3, 2);
lean_inc(x_1);
x_68 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__13(x_1, x_4, x_67, x_66, x_3, x_3);
x_5 = x_68;
goto block_13;
}
}
}
}
}
}
block_13:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_nat_dec_le(x_4, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_9 = l_Array_qsortAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__1(x_1, x_7, x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
x_2 = x_9;
x_3 = x_11;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_qsortAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__1(x_2, x_1, x_15, x_14);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___lambda__1___boxed), 8, 0);
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___lambda__2___boxed), 11, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___closed__2;
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Tactic_withMainMVarContext___rarg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__8(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__10(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__11(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__12(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__13(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_qsortAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsortAux___main___at___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_evalClear___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_1);
x_13 = l_Lean_Elab_Tactic_setGoals(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_evalClear___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_2, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_fget(x_1, x_2);
x_17 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_clear), 7, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_16);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg___boxed), 10, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_Array_forMAux___main___at_Lean_Elab_Tactic_evalClear___spec__1___lambda__1___boxed), 11, 1);
lean_closure_set(x_24, 0, x_21);
x_25 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_24);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_26 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_20, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_2, x_28);
lean_dec(x_2);
x_2 = x_29;
x_11 = x_27;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_35; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_17);
if (x_35 == 0)
{
return x_17;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_17, 0);
x_37 = lean_ctor_get(x_17, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_17);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalClear(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Elab_Tactic_evalIntro___closed__7;
lean_inc(x_1);
x_34 = l_Lean_Syntax_isOfKind(x_1, x_33);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = 0;
x_11 = x_35;
goto block_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = l_Lean_Syntax_getArgs(x_1);
x_37 = lean_array_get_size(x_36);
lean_dec(x_36);
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_dec_eq(x_37, x_38);
lean_dec(x_37);
x_11 = x_39;
goto block_32;
}
block_32:
{
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1___rarg(x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_Elab_Tactic_getFVarIds(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_forMAux___main___at_Lean_Elab_Tactic_evalClear___spec__1(x_20, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_20);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_evalClear___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at_Lean_Elab_Tactic_evalClear___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_evalClear___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at_Lean_Elab_Tactic_evalClear___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalClear), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalClear(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_evalIntro___closed__7;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_14 = lean_apply_7(x_1, x_2, x_4, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_3);
x_18 = l_Lean_Elab_Tactic_setGoals(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
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
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_2);
x_14 = lean_nat_dec_lt(x_3, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fget(x_2, x_3);
x_18 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
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
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getFVarId___boxed), 10, 1);
lean_closure_set(x_23, 0, x_17);
lean_inc(x_21);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1___lambda__1___boxed), 13, 3);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_21);
lean_closure_set(x_24, 2, x_22);
x_25 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_24);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_26 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainMVarContext___spec__1___rarg(x_21, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_3, x_28);
lean_dec(x_3);
x_3 = x_29;
x_12 = x_27;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
uint8_t x_35; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_forEachVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1(x_2, x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_forEachVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_forEachVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalSubst___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l_Lean_Meta_substCore___lambda__5___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalSubst___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_subst), 7, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_evalSubst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalSubst___closed__1;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = l_Lean_Syntax_getArgs(x_1);
x_15 = lean_array_get_size(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1___rarg(x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
lean_dec(x_1);
x_21 = l_Lean_Syntax_getArgs(x_20);
lean_dec(x_20);
x_22 = l_Lean_Elab_Tactic_evalSubst___closed__2;
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_forMAux___main___at_Lean_Elab_Tactic_forEachVar___spec__1(x_22, x_21, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_21);
return x_24;
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSubst), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSubst(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_evalSubst___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_List_findM_x3f___main___at___private_Lean_Elab_Tactic_Basic_6__findTag_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_14);
x_16 = l_Lean_Meta_getMVarDecl___at_Lean_Elab_Tactic_getMainTag___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Name_isSuffixOf___main(x_1, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_free_object(x_16);
lean_dec(x_14);
x_2 = x_15;
x_11 = x_19;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Name_isSuffixOf___main(x_1, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_dec(x_14);
x_2 = x_15;
x_11 = x_25;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_14);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_15);
lean_dec(x_14);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
lean_object* l_List_findM_x3f___main___at___private_Lean_Elab_Tactic_Basic_6__findTag_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_14);
x_16 = l_Lean_Meta_getMVarDecl___at_Lean_Elab_Tactic_getMainTag___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Name_isPrefixOf___main(x_1, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_free_object(x_16);
lean_dec(x_14);
x_2 = x_15;
x_11 = x_19;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Name_isPrefixOf___main(x_1, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_dec(x_14);
x_2 = x_15;
x_11 = x_25;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_14);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_15);
lean_dec(x_14);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_6__findTag_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_1);
x_12 = l_List_findM_x3f___main___at___private_Lean_Elab_Tactic_Basic_6__findTag_x3f___spec__1(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_findM_x3f___main___at___private_Lean_Elab_Tactic_Basic_6__findTag_x3f___spec__2(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_23 = x_13;
} else {
 lean_dec_ref(x_13);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(1, 1, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
}
else
{
uint8_t x_26; 
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
lean_object* l_List_findM_x3f___main___at___private_Lean_Elab_Tactic_Basic_6__findTag_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_findM_x3f___main___at___private_Lean_Elab_Tactic_Basic_6__findTag_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_List_findM_x3f___main___at___private_Lean_Elab_Tactic_Basic_6__findTag_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_findM_x3f___main___at___private_Lean_Elab_Tactic_Basic_6__findTag_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_6__findTag_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Basic_6__findTag_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__1(x_5, x_2);
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
x_11 = l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__1(x_9, x_2);
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
lean_object* _init_l_Lean_Elab_Tactic_evalCase___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("case");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalCase___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l_Lean_Elab_Tactic_evalCase___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_evalCase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_69; uint8_t x_70; 
x_69 = l_Lean_Elab_Tactic_evalCase___closed__5;
lean_inc(x_1);
x_70 = l_Lean_Syntax_isOfKind(x_1, x_69);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = 0;
x_11 = x_71;
goto block_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = l_Lean_Syntax_getArgs(x_1);
x_73 = lean_array_get_size(x_72);
lean_dec(x_72);
x_74 = lean_unsigned_to_nat(4u);
x_75 = lean_nat_dec_eq(x_73, x_74);
lean_dec(x_73);
x_11 = x_75;
goto block_68;
}
block_68:
{
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1___rarg(x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2;
lean_inc(x_16);
x_18 = l_Lean_Syntax_isOfKind(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1___rarg(x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l_Lean_Syntax_getId(x_14);
lean_dec(x_14);
x_21 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_22);
x_24 = l___private_Lean_Elab_Tactic_Basic_6__findTag_x3f(x_22, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
lean_dec(x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_16);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Tactic_evalCase___closed__3;
x_28 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main___spec__2___rarg(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
lean_dec(x_25);
x_31 = l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__1(x_22, x_30);
x_32 = lean_box(0);
lean_inc(x_30);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Elab_Tactic_setGoals(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_30);
x_36 = l_Lean_Meta_getMVarTag(x_30, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_box(0);
lean_inc(x_30);
x_40 = l_Lean_Meta_setMVarTag(x_30, x_39, x_6, x_7, x_8, x_9, x_38);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_42 = l_Lean_Elab_Tactic_evalTactic___main(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_Meta_setMVarTag(x_30, x_37, x_6, x_7, x_8, x_9, x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
lean_inc(x_4);
x_46 = l_Lean_Elab_Tactic_done(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Elab_Tactic_setGoals(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_47);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_31);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = lean_ctor_get(x_42, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_dec(x_42);
x_55 = l_Lean_Meta_setMVarTag(x_30, x_37, x_6, x_7, x_8, x_9, x_54);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set_tag(x_55, 1);
lean_ctor_set(x_55, 0, x_53);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_36);
if (x_60 == 0)
{
return x_36;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_36, 0);
x_62 = lean_ctor_get(x_36, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_36);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_24);
if (x_64 == 0)
{
return x_24;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_24, 0);
x_66 = lean_ctor_get(x_24, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_24);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
}
}
lean_object* l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_erase___main___at_Lean_Elab_Tactic_evalCase___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCase), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCase(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_evalCase___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalOrelse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("orelse");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalOrelse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l_Lean_Elab_Tactic_evalOrelse___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_evalOrelse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalOrelse___closed__2;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = l_Lean_Syntax_getArgs(x_1);
x_15 = lean_array_get_size(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(3u);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___main___spec__1___rarg(x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
lean_dec(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = l_Lean_Elab_Tactic_evalTactic___main(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_Tactic_evalTactic___main(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
return x_25;
}
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalOrelse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalOrelse), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalOrelse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_evalOrelse___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalOrelse___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l___private_Lean_Elab_Tactic_Basic_7__regTraceClasses___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_6__regTraceClasses___closed__1;
x_2 = l_Lean_Meta_registerHygienicIntro___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_7__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Tactic_Basic_7__regTraceClasses___closed__1;
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
lean_object* l_Lean_Elab_Tactic_TacticM_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_st_mk_ref(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = lean_apply_9(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_12, x_16);
lean_dec(x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_12);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_TacticM_run___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_run_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_st_mk_ref(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = lean_apply_9(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_12, x_16);
lean_dec(x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_12);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_run_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_TacticM_run_x27___rarg), 10, 0);
return x_2;
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
lean_object* initialize_Lean_Elab_Binders(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Tactic_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
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
res = initialize_Lean_Elab_Binders(lean_io_mk_world());
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
l_Lean_Elab_Tactic_State_inhabited = _init_l_Lean_Elab_Tactic_State_inhabited();
lean_mark_persistent(l_Lean_Elab_Tactic_State_inhabited);
l_Lean_Elab_Tactic_monadExcept___closed__1 = _init_l_Lean_Elab_Tactic_monadExcept___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_monadExcept___closed__1);
l_Lean_Elab_Tactic_monadExcept___closed__2 = _init_l_Lean_Elab_Tactic_monadExcept___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_monadExcept___closed__2);
l_Lean_Elab_Tactic_monadExcept___closed__3 = _init_l_Lean_Elab_Tactic_monadExcept___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_monadExcept___closed__3);
l_Lean_Elab_Tactic_monadExcept = _init_l_Lean_Elab_Tactic_monadExcept();
lean_mark_persistent(l_Lean_Elab_Tactic_monadExcept);
l_Lean_Elab_Tactic_hasOrElse___closed__1 = _init_l_Lean_Elab_Tactic_hasOrElse___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_hasOrElse___closed__1);
l_Lean_Elab_Tactic_SavedState_inhabited___closed__1 = _init_l_Lean_Elab_Tactic_SavedState_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_SavedState_inhabited___closed__1);
l_Lean_Elab_Tactic_SavedState_inhabited = _init_l_Lean_Elab_Tactic_SavedState_inhabited();
lean_mark_persistent(l_Lean_Elab_Tactic_SavedState_inhabited);
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
l_Lean_Elab_Tactic_mkTacticAttribute___closed__7 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__7);
res = l_Lean_Elab_Tactic_mkTacticAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_tacticElabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute);
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__1 = _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__1);
l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__2 = _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__2);
l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__3 = _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__3);
l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__4 = _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__4);
l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__5 = _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__5);
l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__6 = _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__6);
l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__7 = _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__7);
l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__8 = _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__8);
l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__9 = _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__9);
l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__10 = _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__10);
l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__11 = _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__11);
l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__12 = _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__12);
l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__13 = _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__13);
l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__14 = _init_l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_2__expandTacticMacroFns___main___closed__14);
l_Lean_Elab_Tactic_evalTactic___main___closed__1 = _init_l_Lean_Elab_Tactic_evalTactic___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___main___closed__1);
l_Lean_Elab_Tactic_evalTactic___main___closed__2 = _init_l_Lean_Elab_Tactic_evalTactic___main___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___main___closed__2);
l_Lean_Elab_Tactic_evalTactic___main___closed__3 = _init_l_Lean_Elab_Tactic_evalTactic___main___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___main___closed__3);
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
l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__3);
res = l___regBuiltin_Lean_Elab_Tactic_evalDone(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_focus___rarg___closed__1 = _init_l_Lean_Elab_Tactic_focus___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_focus___rarg___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalSeq1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__3);
res = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__3);
res = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__3);
res = l___regBuiltin_Lean_Elab_Tactic_evalFocus(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__2);
res = l___regBuiltin_Lean_Elab_Tactic_evalParen(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__3);
res = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalChoice(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__3);
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
l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__3);
res = l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__3);
res = l___regBuiltin_Lean_Elab_Tactic_evalTraceState(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalAssumption___rarg___closed__1 = _init_l_Lean_Elab_Tactic_evalAssumption___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalAssumption___rarg___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__2);
res = l___regBuiltin_Lean_Elab_Tactic_evalAssumption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Basic_3__introStep___closed__1 = _init_l___private_Lean_Elab_Tactic_Basic_3__introStep___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_3__introStep___closed__1);
l_Lean_Elab_Tactic_evalIntro___closed__1 = _init_l_Lean_Elab_Tactic_evalIntro___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__1);
l_Lean_Elab_Tactic_evalIntro___closed__2 = _init_l_Lean_Elab_Tactic_evalIntro___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__2);
l_Lean_Elab_Tactic_evalIntro___closed__3 = _init_l_Lean_Elab_Tactic_evalIntro___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__3);
l_Lean_Elab_Tactic_evalIntro___closed__4 = _init_l_Lean_Elab_Tactic_evalIntro___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__4);
l_Lean_Elab_Tactic_evalIntro___closed__5 = _init_l_Lean_Elab_Tactic_evalIntro___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__5);
l_Lean_Elab_Tactic_evalIntro___closed__6 = _init_l_Lean_Elab_Tactic_evalIntro___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__6);
l_Lean_Elab_Tactic_evalIntro___closed__7 = _init_l_Lean_Elab_Tactic_evalIntro___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__7);
l_Lean_Elab_Tactic_evalIntro___closed__8 = _init_l_Lean_Elab_Tactic_evalIntro___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__8);
l_Lean_Elab_Tactic_evalIntro___closed__9 = _init_l_Lean_Elab_Tactic_evalIntro___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__9);
l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalIntro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__3);
res = l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalIntros___closed__1 = _init_l_Lean_Elab_Tactic_evalIntros___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntros___closed__1);
l_Lean_Elab_Tactic_evalIntros___closed__2 = _init_l_Lean_Elab_Tactic_evalIntros___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntros___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalIntros(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalRevert___closed__1 = _init_l_Lean_Elab_Tactic_evalRevert___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRevert___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalRevert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___closed__1 = _init_l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___closed__1);
l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___closed__2 = _init_l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_5__sortFVarIds___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalClear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalSubst___closed__1 = _init_l_Lean_Elab_Tactic_evalSubst___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSubst___closed__1);
l_Lean_Elab_Tactic_evalSubst___closed__2 = _init_l_Lean_Elab_Tactic_evalSubst___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSubst___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalSubst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalCase___closed__1 = _init_l_Lean_Elab_Tactic_evalCase___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalCase___closed__1);
l_Lean_Elab_Tactic_evalCase___closed__2 = _init_l_Lean_Elab_Tactic_evalCase___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalCase___closed__2);
l_Lean_Elab_Tactic_evalCase___closed__3 = _init_l_Lean_Elab_Tactic_evalCase___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalCase___closed__3);
l_Lean_Elab_Tactic_evalCase___closed__4 = _init_l_Lean_Elab_Tactic_evalCase___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalCase___closed__4);
l_Lean_Elab_Tactic_evalCase___closed__5 = _init_l_Lean_Elab_Tactic_evalCase___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalCase___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalCase(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalOrelse___closed__1 = _init_l_Lean_Elab_Tactic_evalOrelse___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalOrelse___closed__1);
l_Lean_Elab_Tactic_evalOrelse___closed__2 = _init_l_Lean_Elab_Tactic_evalOrelse___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalOrelse___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalOrelse___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalOrelse___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalOrelse___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalOrelse(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Basic_7__regTraceClasses___closed__1 = _init_l___private_Lean_Elab_Tactic_Basic_7__regTraceClasses___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_7__regTraceClasses___closed__1);
res = l___private_Lean_Elab_Tactic_Basic_7__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
