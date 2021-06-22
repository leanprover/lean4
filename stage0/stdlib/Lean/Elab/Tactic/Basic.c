// Lean compiler output
// Module: Lean.Elab.Tactic.Basic
// Imports: Init Lean.Util.CollectMVars Lean.Parser.Command Lean.Meta.PPGoal Lean.Meta.Tactic.Assumption Lean.Meta.Tactic.Contradiction Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Clear Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Subst Lean.Elab.Util Lean.Elab.Term Lean.Elab.Binders
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
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2;
static lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__3;
static lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__3;
lean_object* l_Lean_Elab_Tactic_withCaseRef(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__2;
lean_object* l_Lean_Elab_Tactic_expandTacticMacro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTacticAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__1;
size_t l_USize_add(size_t, size_t);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__4;
lean_object* l_Lean_pushScope___at_Lean_Elab_Tactic_evalOpen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__1;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focus_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntroMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenRenaming___at_Lean_Elab_Tactic_evalOpen___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__5;
static lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__20;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__15;
static lean_object* l_Lean_Elab_Tactic_evalTacticAux___closed__1;
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__3;
lean_object* l_Lean_Elab_Tactic_evalRotateRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_throwNoGoalsToBeSolved___spec__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticSeq1Indented(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_forEachVar___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withCaseRef___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntros___closed__1;
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__5(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Elab_Tactic_adaptExpander___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__10;
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__32;
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSkip___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_popScope___at_Lean_Elab_Tactic_evalOpen___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* l_Lean_Elab_admitGoal___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalChoiceAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__41;
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__13;
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop_match__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__38;
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__21;
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFocus___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
lean_object* l_Lean_Elab_Tactic_evalCase_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSkip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalContradiction___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*);
lean_object* l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Tactic_elabSetOption___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalCase___closed__6;
lean_object* l_Lean_Elab_Tactic_evalClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabSetOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__19(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__23;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_appendGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_pruneSolvedGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focus(lean_object*);
lean_object* l_Array_qpartition_loop___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_focusAndDone(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenOnly___at_Lean_Elab_Tactic_evalOpen___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__5;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_adaptExpander___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__6;
lean_object* l_List_findM_x3f___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalUnknown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__43;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalCase___closed__1;
lean_object* l_Lean_Elab_Tactic_evalTacticAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_done(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Elab_goalsToMessageData___spec__1(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__5;
lean_object* l_Lean_Elab_Tactic_evalTacticSeq1Indented___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalUnknown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__2;
lean_object* l_List_filterAuxM___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__40;
lean_object* l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAllGoals(lean_object*);
lean_object* l_Lean_Elab_Tactic_forEachVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__2;
lean_object* l_id___rarg___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__3;
static lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__10;
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__36;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Array_qpartition_loop___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarId_match__1(lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_evalOpen___spec__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__5;
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27(lean_object*);
static lean_object* l_Lean_Elab_goalsToMessageData___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__39;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__1;
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__9;
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__12;
lean_object* l_Lean_Meta_subst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getIntrosSize_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__5;
lean_object* l_Lean_Elab_Tactic_evalIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalCase___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__35;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__3;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Tactic_evalIntro___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__7;
static lean_object* l_Lean_Elab_Tactic_evalCase___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f_match__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__3;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Tactic_tryCatch(lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__18(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__4;
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop_match__2(lean_object*);
lean_object* l_List_rotateLeft___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__21(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getGoals___boxed(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalClear___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRotateRight(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFocus___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__5;
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__8;
static lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__4;
lean_object* l_Lean_Elab_Tactic_evalDone___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__3;
lean_object* l_Lean_Elab_Tactic_evalTacticAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented(lean_object*);
lean_object* l_Lean_MetavarContext_renameMVar(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__4;
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__4;
lean_object* l_Lean_Elab_Tactic_evalTacticAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabSetOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__1___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__16;
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__7(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__4;
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__7;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTraceState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalContradiction___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__3;
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__1;
uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_102_(uint8_t, uint8_t);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Tactic_evalIntro___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalContradiction___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_done___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__1;
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabSetOption___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarId_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withPPInaccessibleNames___at_Lean_Elab_Term_reportUnsolvedGoals___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_evalAllGoals___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_getFVarId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__2;
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalIntros___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__2;
static lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_elabSetOption(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__4;
lean_object* l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____spec__1(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalUnknown(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalFirst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__7;
lean_object* l_Lean_Elab_Tactic_saveState(lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_Elab_Tactic_tryCatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalClear(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_getFVarId___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__2;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3___closed__1;
lean_object* l_Lean_ScopedEnvExtension_popScope___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__5;
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__11;
lean_object* l_Lean_Elab_Tactic_closeMainGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__31;
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalSeq1___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAssumption(lean_object*);
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenHiding___at_Lean_Elab_Tactic_evalOpen___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalSubst___closed__3;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__2___closed__2;
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_goalsToMessageData___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Elab_Tactic_focus_match__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalCase___closed__4;
lean_object* l_Lean_ResolveName_resolveNamespace_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__5;
lean_object* lean_local_ctx_num_indices(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__1;
lean_object* l_Lean_Elab_Tactic_evalContradiction___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__4;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalOpen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getOptRotation___boxed(lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__7___rarg___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__1;
static lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__3;
static lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__5;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Array_qsort_sort___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__1___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__4;
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__15;
lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__18;
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticAux_match__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__4;
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__4;
lean_object* l_Lean_getOptionDecl(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_closeMainGoal___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTraceState(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__3;
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__2(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__2;
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_evalAllGoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__4;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalChoice(lean_object*);
static lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__3;
lean_object* l_Lean_Elab_Tactic_focus___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFirst_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__3;
lean_object* lean_local_ctx_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticSeqBracketed___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__3;
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__6(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM;
lean_object* l_Lean_Elab_Tactic_evalFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instMonadTacticM;
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
static uint32_t l_Lean_Elab_Tactic_tacticElabAttribute___lambda__2___closed__1;
lean_object* l_Lean_Elab_Tactic_withTacticInfoContext(lean_object*);
lean_object* l_Lean_Elab_Tactic_withCaseRef___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__11;
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabSetOption___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_findM_x3f___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalTacticAux___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__46;
lean_object* l_List_foldl___at_Array_appendList___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_getFVarIds___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess(lean_object*);
lean_object* l_Lean_Elab_Tactic_closeUsingOrAdmit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__1;
lean_object* l_Lean_Elab_Tactic_mkTacticInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_orElse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__3;
lean_object* l_Lean_Elab_Tactic_evalIntro_introStep_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalOpen___spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSkip(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_focusAndDone___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Array_qsort_sort___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalDone___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__2;
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__1;
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__34;
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalOpen___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_instOrElseTacticM___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalManyTacticOptSemi___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalDone___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__8;
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__1;
lean_object* l_List_forM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortTacticExceptionId;
lean_object* l_Lean_Elab_Tactic_getGoals___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenOnly___at_Lean_Elab_Tactic_evalOpen___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDone(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__2;
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__4;
lean_object* l_Lean_ScopedEnvExtension_pushScope___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFirst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getGoals___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__4;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalTacticAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__4;
lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalContradiction___rarg___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__1;
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_Elab_Term_reportUnsolvedGoals___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__1;
lean_object* l_Lean_popScope___at_Lean_Elab_Tactic_evalOpen___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__1;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__2;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Tactic_saveTacticInfoForToken(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_admitGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__4;
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCase___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__4;
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalChoice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_closeMainGoal___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainContext___spec__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__9;
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__26;
lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__2;
lean_object* l_Lean_Elab_Tactic_evalTacticSeqBracketed___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__12;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__2;
static lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__1;
lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27(lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__2;
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalParen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__5;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSeq1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__3;
lean_object* l_Lean_Elab_Tactic_withCaseRef___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__4;
lean_object* l_Lean_Elab_Tactic_getMainModule___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__8___boxed(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__4;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSubst(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__5;
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed(lean_object*);
lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainModule___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__2;
lean_object* l_Lean_Elab_Tactic_evalChoice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntros(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTraceState(lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__2;
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__6;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Meta_contradiction(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Tactic_evalIntro___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCase_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getIntrosSize(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__44;
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFirst___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalAllGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__5;
static lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess___closed__2;
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__3;
lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__5;
static lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___closed__2;
static lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__4;
lean_object* l_Lean_Elab_Tactic_evalRotateLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___closed__1;
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__3;
lean_object* l_List_erase___at_Lean_Elab_Tactic_evalCase___spec__1(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__4;
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFirst(lean_object*);
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__13;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__5;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__2;
lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns_loop_match__1(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTacticAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__3;
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
static lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__3;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalAssumption___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFirst_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__4;
lean_object* l_Lean_Elab_Tactic_forEachVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__4;
static lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__1;
lean_object* l_Lean_Elab_Tactic_evalRevert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFocus(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getIntrosSize_match__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__3;
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalClear___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__1___closed__2;
uint8_t l_Lean_Syntax_isNodeOf(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalClear___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1(lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__1;
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__1;
lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27___boxed(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntros___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_appendGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_activateScoped___at_Lean_Elab_Tactic_evalOpen___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__1;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_evalOpen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__1;
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tryTactic_x3f(lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__2;
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalSeq1___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__24;
lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal_loop_match__1(lean_object*);
lean_object* l_Lean_Meta_withPPInaccessibleNames___at_Lean_Elab_Term_reportUnsolvedGoals___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_goalsToMessageData(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds___boxed__const__1;
lean_object* l_Lean_Elab_Tactic_focusAndDone___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_isAnonymousMVar(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__2;
lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__4;
lean_object* l_Lean_Elab_Tactic_evalTacticAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalContradiction(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSeq1(lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess___closed__1;
lean_object* l_Lean_Elab_Tactic_evalRotateRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__1;
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds_match__1(lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__3;
lean_object* l_Lean_Elab_Tactic_evalParen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Elab_Tactic_liftMetaTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__4;
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCase_match__2___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFocus(lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__5;
lean_object* lean_environment_main_module(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__1;
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSubst___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__37;
static lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalRevert___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2;
lean_object* l_List_rotateRight___rarg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__2;
lean_object* l_Lean_Elab_Tactic_evalCase___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__4___closed__1;
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__4___boxed(lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__3;
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__42;
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__4;
lean_object* l_Lean_Elab_Tactic_evalFirst___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCase_match__3(lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__11;
lean_object* l_Lean_Elab_Tactic_evalRotateLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalTacticAux___closed__2;
lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__4;
lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1;
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__1;
lean_object* l_Lean_Elab_Tactic_evalAssumption(lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__8;
lean_object* l_Lean_Elab_Tactic_evalIntro_introStep___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalCase___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__17;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalManyTacticOptSemi___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__2;
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenRenaming___at_Lean_Elab_Tactic_evalOpen___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_setGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__27;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___closed__2;
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_traceAtCmdPos___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_insertCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withPPInaccessibleNamesImp___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__10;
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Tactic_evalIntro___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__9;
lean_object* l_List_filterAuxM___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenSimple___at_Lean_Elab_Tactic_evalOpen___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntros_match__1(lean_object*);
lean_object* l_Lean_Meta_isExprMVarAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCase___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__45;
lean_object* l_Lean_Elab_Tactic_evalChoiceAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__10;
static lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__6;
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__33;
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__5;
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__13;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__2;
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_findM_x3f___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMacroExpansion___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__5;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__30;
lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Tactic_elabSetOption___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___closed__1;
static lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRevert(lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_getFVarIds___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro_introStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalOpen___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__14;
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getIntrosSize___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__1;
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_instMonadTacticM___closed__6;
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__5;
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux(lean_object*);
lean_object* l_Lean_Elab_Tactic_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__9;
lean_object* l_Lean_Elab_Tactic_evalCase_match__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTraceState___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalCase___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__22;
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro_introStep___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalIntros___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_closeMainGoal(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__7___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_tryTactic___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_5545_(lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__4;
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_throwNoGoalsToBeSolved___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__8(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__29;
lean_object* l_Lean_Elab_Tactic_getMainTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_forEachVar___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__3;
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instInhabitedState;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTraceState___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalDone(lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__3;
static lean_object* l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntro(lean_object*);
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_DataValue_sameCtor(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tryTactic_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_throwNoGoalsToBeSolved___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__19;
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__15;
lean_object* l_List_findM_x3f___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalFirst___spec__1___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__5;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__6;
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__28;
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalManyTacticOptSemi(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSubst___closed__1;
lean_object* l_Lean_Elab_Tactic_evalIntros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tryTactic(lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__7___boxed(lean_object*);
lean_object* l_Lean_Syntax_toNat(lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTacticSeqBracketed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__1;
lean_object* l_Lean_Elab_Tactic_evalSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__1;
lean_object* l_Lean_Elab_Tactic_saveState___boxed(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__14;
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getOptRotation(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__3;
lean_object* l_Lean_Elab_Tactic_instOrElseTacticM(lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__5___boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__3;
lean_object* l_Array_qsort_sort___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenSimple___at_Lean_Elab_Tactic_evalOpen___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMacroExpansion(lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_scopedEnvExtensionsRef;
static lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__2;
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__3;
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__4;
lean_object* l_List_erase___at_Lean_Elab_Tactic_evalCase___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro_introStep_match__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__3;
lean_object* l_Lean_Elab_Tactic_adaptExpander___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__3;
uint8_t l_Lean_Elab_isAbortTacticException(lean_object*);
static lean_object* l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop_match__3(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__2;
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_getFVarId___closed__1;
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalIntros___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___closed__1;
lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_Tactic_elabSetOption___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_pushScope___at_Lean_Elab_Tactic_evalOpen___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntros_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__3;
lean_object* l_Lean_Elab_Tactic_getMainModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__6;
lean_object* l_Lean_Elab_Tactic_getFVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalManyTacticOptSemi___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Tactic_elabSetOption___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalCase(lean_object*);
lean_object* l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalCase___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__12;
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__3;
lean_object* l_Lean_Elab_Tactic_evalCase_match__2(lean_object*);
lean_object* l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalRevert___closed__2;
lean_object* l_Lean_Elab_Tactic_orElse(lean_object*);
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__25;
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__16;
static lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__2;
static lean_object* l_Lean_Elab_Tactic_getFVarId___closed__2;
lean_object* l_Lean_Elab_Tactic_getGoals(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__1;
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalClear___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__1;
lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_Tactic_elabSetOption___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Tactic_elabSetOption___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__3;
lean_object* l_Lean_Elab_Tactic_mkTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_activateScoped___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_Elab_Term_reportUnsolvedGoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandTacticMacro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__5;
static lean_object* l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalContradiction(lean_object*);
static lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__7___closed__1;
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_evalOpen___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalParen(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalFirst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalIntro___closed__6;
lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
static lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_5545____closed__1;
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenHiding___at_Lean_Elab_Tactic_evalOpen___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSeq1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalOpen___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_activateScoped___at_Lean_Elab_Tactic_evalOpen___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_forEachVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_forEachVar___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__5;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalAllGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSkip___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__5;
lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg(lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalOpen(lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__4(lean_object*);
lean_object* l_Lean_Elab_admitGoal___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_inferType(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Meta_mkSorry(x_9, x_11, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_assignExprMVar(x_2, x_13, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
else
{
uint8_t x_16; 
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
else
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l_Lean_Elab_admitGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_7 = l_Lean_mkMVar(x_1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_admitGoal___lambda__1), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__1___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
lean_object* l_List_map___at_Lean_Elab_goalsToMessageData___spec__1(lean_object* x_1) {
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
x_7 = l_List_map___at_Lean_Elab_goalsToMessageData___spec__1(x_5);
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
x_11 = l_List_map___at_Lean_Elab_goalsToMessageData___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_Elab_goalsToMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_goalsToMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_goalsToMessageData___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_goalsToMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_List_map___at_Lean_Elab_goalsToMessageData___spec__1(x_1);
x_3 = l_Lean_Elab_goalsToMessageData___closed__2;
x_4 = l_Lean_MessageData_joinSep(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_List_forM___at_Lean_Elab_Term_reportUnsolvedGoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_admitGoal(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_1 = x_12;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
lean_object* l_Lean_Meta_withPPInaccessibleNames___at_Lean_Elab_Term_reportUnsolvedGoals___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_1, x_3, x_4);
x_11 = l_Lean_Meta_withPPInaccessibleNamesImp___rarg(x_2, x_10, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = 2;
x_11 = l_Lean_Elab_log___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_List_forM___at_Lean_Elab_Term_reportUnsolvedGoals___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unsolvedGoals");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__2;
x_2 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unsolved goals\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_inc(x_1);
x_9 = l_Lean_Elab_goalsToMessageData(x_1);
x_10 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__6;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__4;
x_15 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_reportUnsolvedGoals___lambda__1___boxed), 9, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_1);
x_17 = 1;
x_18 = l_Lean_Meta_withPPInaccessibleNames___at_Lean_Elab_Term_reportUnsolvedGoals___spec__2(x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
}
lean_object* l_List_forM___at_Lean_Elab_Term_reportUnsolvedGoals___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___at_Lean_Elab_Term_reportUnsolvedGoals___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_withPPInaccessibleNames___at_Lean_Elab_Term_reportUnsolvedGoals___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_withPPInaccessibleNames___at_Lean_Elab_Term_reportUnsolvedGoals___spec__2(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_reportUnsolvedGoals___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = lean_apply_9(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_apply_1(x_3, x_16);
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
x_20 = lean_apply_1(x_3, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_3);
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
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = lean_apply_9(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_3);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
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
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = lean_apply_9(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_apply_9(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_apply_1(x_15, x_19);
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
x_23 = lean_apply_1(x_15, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_15);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = lean_apply_9(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_apply_9(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
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
lean_dec(x_15);
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
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = lean_apply_9(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_9(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = lean_apply_9(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_apply_10(x_4, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instMonadTacticM___lambda__1), 13, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instMonadTacticM___lambda__2), 13, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_instMonadTacticM___closed__1;
x_2 = l_Lean_Elab_Tactic_instMonadTacticM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instMonadTacticM___lambda__3___boxed), 11, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instMonadTacticM___lambda__4), 13, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instMonadTacticM___lambda__5), 13, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instMonadTacticM___lambda__6), 13, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Tactic_instMonadTacticM___closed__3;
x_2 = l_Lean_Elab_Tactic_instMonadTacticM___closed__4;
x_3 = l_Lean_Elab_Tactic_instMonadTacticM___closed__5;
x_4 = l_Lean_Elab_Tactic_instMonadTacticM___closed__6;
x_5 = l_Lean_Elab_Tactic_instMonadTacticM___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instMonadTacticM___lambda__7), 13, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_instMonadTacticM___closed__8;
x_2 = l_Lean_Elab_Tactic_instMonadTacticM___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadTacticM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_instMonadTacticM___closed__10;
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_instMonadTacticM___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_instMonadTacticM___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_Elab_Tactic_getGoals___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_1, x_10);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_3, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_set(x_3, x_1, x_14);
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
lean_object* l_List_filterAuxM___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_16 = l_Lean_Meta_isExprMVarAssigned(x_14, x_7, x_8, x_9, x_10, x_11);
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
x_25 = l_Lean_Meta_isExprMVarAssigned(x_23, x_7, x_8, x_9, x_10, x_11);
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
x_14 = l_List_filterAuxM___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(x_11, x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
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
lean_object* l_List_filterAuxM___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_filterAuxM___at_Lean_Elab_Tactic_pruneSolvedGoals___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_mk_ref(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_14);
x_16 = lean_apply_9(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_9, x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_14, x_20);
lean_dec(x_14);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_21, 0, x_24);
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
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_9);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore___rarg), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_mk_ref(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_14);
x_16 = lean_apply_9(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_9, x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_14, x_20);
lean_dec(x_14);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_17);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_9);
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
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_TacticM_runCore_x27___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_run___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_23 = lean_st_ref_get(x_8, x_9);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_get(x_4, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_8, x_27);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_take(x_4, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_107; 
x_35 = lean_ctor_get(x_32, 1);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_32, 1, x_36);
x_37 = lean_st_ref_set(x_4, x_32, x_33);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_box(0);
lean_inc(x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_36);
x_67 = lean_st_ref_get(x_8, x_38);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_st_mk_ref(x_41, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_70);
lean_inc(x_40);
x_107 = lean_apply_9(x_2, x_40, x_70, x_3, x_4, x_5, x_6, x_7, x_8, x_71);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_40, x_70, x_3, x_4, x_5, x_6, x_7, x_8, x_108);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_40);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_72 = x_110;
x_73 = x_111;
goto block_106;
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
lean_dec(x_107);
x_114 = l_Lean_Elab_isAbortTacticException(x_112);
if (x_114 == 0)
{
lean_dec(x_70);
lean_dec(x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_42 = x_112;
x_43 = x_113;
goto block_66;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_112);
x_115 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_40, x_70, x_3, x_4, x_5, x_6, x_7, x_8, x_113);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_40);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_72 = x_116;
x_73 = x_117;
goto block_106;
}
}
block_66:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_st_ref_get(x_8, x_43);
lean_dec(x_8);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_st_ref_take(x_4, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_47, 1);
lean_dec(x_50);
lean_ctor_set(x_47, 1, x_28);
x_51 = lean_st_ref_set(x_4, x_47, x_48);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_42);
x_10 = x_51;
goto block_22;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_42);
lean_ctor_set(x_55, 1, x_54);
x_10 = x_55;
goto block_22;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_56 = lean_ctor_get(x_47, 0);
x_57 = lean_ctor_get(x_47, 2);
x_58 = lean_ctor_get(x_47, 3);
x_59 = lean_ctor_get(x_47, 4);
x_60 = lean_ctor_get(x_47, 5);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_47);
x_61 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_28);
lean_ctor_set(x_61, 2, x_57);
lean_ctor_set(x_61, 3, x_58);
lean_ctor_set(x_61, 4, x_59);
lean_ctor_set(x_61, 5, x_60);
x_62 = lean_st_ref_set(x_4, x_61, x_48);
lean_dec(x_4);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
 lean_ctor_set_tag(x_65, 1);
}
lean_ctor_set(x_65, 0, x_42);
lean_ctor_set(x_65, 1, x_63);
x_10 = x_65;
goto block_22;
}
}
block_106:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_74 = lean_st_ref_get(x_8, x_73);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_st_ref_get(x_70, x_75);
lean_dec(x_70);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_st_ref_get(x_8, x_77);
lean_dec(x_8);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_st_ref_take(x_4, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_81, 1);
lean_dec(x_84);
lean_ctor_set(x_81, 1, x_28);
x_85 = lean_st_ref_set(x_4, x_81, x_82);
lean_dec(x_4);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_72);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_85, 0, x_89);
x_10 = x_85;
goto block_22;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_72);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
x_10 = x_93;
goto block_22;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_94 = lean_ctor_get(x_81, 0);
x_95 = lean_ctor_get(x_81, 2);
x_96 = lean_ctor_get(x_81, 3);
x_97 = lean_ctor_get(x_81, 4);
x_98 = lean_ctor_get(x_81, 5);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_81);
x_99 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_99, 0, x_94);
lean_ctor_set(x_99, 1, x_28);
lean_ctor_set(x_99, 2, x_95);
lean_ctor_set(x_99, 3, x_96);
lean_ctor_set(x_99, 4, x_97);
lean_ctor_set(x_99, 5, x_98);
x_100 = lean_st_ref_set(x_4, x_99, x_82);
lean_dec(x_4);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_72);
lean_ctor_set(x_104, 1, x_103);
if (lean_is_scalar(x_102)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_102;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_101);
x_10 = x_105;
goto block_22;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_179; 
x_118 = lean_ctor_get(x_32, 0);
x_119 = lean_ctor_get(x_32, 2);
x_120 = lean_ctor_get(x_32, 3);
x_121 = lean_ctor_get(x_32, 4);
x_122 = lean_ctor_get(x_32, 5);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_32);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_124, 0, x_118);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set(x_124, 2, x_119);
lean_ctor_set(x_124, 3, x_120);
lean_ctor_set(x_124, 4, x_121);
lean_ctor_set(x_124, 5, x_122);
x_125 = lean_st_ref_set(x_4, x_124, x_33);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_box(0);
lean_inc(x_1);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_1);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_1);
lean_ctor_set(x_129, 1, x_123);
x_149 = lean_st_ref_get(x_8, x_126);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_st_mk_ref(x_129, x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_152);
lean_inc(x_128);
x_179 = lean_apply_9(x_2, x_128, x_152, x_3, x_4, x_5, x_6, x_7, x_8, x_153);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_181 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_128, x_152, x_3, x_4, x_5, x_6, x_7, x_8, x_180);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_128);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_154 = x_182;
x_155 = x_183;
goto block_178;
}
else
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_179, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_179, 1);
lean_inc(x_185);
lean_dec(x_179);
x_186 = l_Lean_Elab_isAbortTacticException(x_184);
if (x_186 == 0)
{
lean_dec(x_152);
lean_dec(x_128);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_130 = x_184;
x_131 = x_185;
goto block_148;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_184);
x_187 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_128, x_152, x_3, x_4, x_5, x_6, x_7, x_8, x_185);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_128);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_154 = x_188;
x_155 = x_189;
goto block_178;
}
}
block_148:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_132 = lean_st_ref_get(x_8, x_131);
lean_dec(x_8);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_st_ref_take(x_4, x_133);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_135, 3);
lean_inc(x_139);
x_140 = lean_ctor_get(x_135, 4);
lean_inc(x_140);
x_141 = lean_ctor_get(x_135, 5);
lean_inc(x_141);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 lean_ctor_release(x_135, 5);
 x_142 = x_135;
} else {
 lean_dec_ref(x_135);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 6, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_28);
lean_ctor_set(x_143, 2, x_138);
lean_ctor_set(x_143, 3, x_139);
lean_ctor_set(x_143, 4, x_140);
lean_ctor_set(x_143, 5, x_141);
x_144 = lean_st_ref_set(x_4, x_143, x_136);
lean_dec(x_4);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
 lean_ctor_set_tag(x_147, 1);
}
lean_ctor_set(x_147, 0, x_130);
lean_ctor_set(x_147, 1, x_145);
x_10 = x_147;
goto block_22;
}
block_178:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_156 = lean_st_ref_get(x_8, x_155);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
x_158 = lean_st_ref_get(x_152, x_157);
lean_dec(x_152);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
x_160 = lean_st_ref_get(x_8, x_159);
lean_dec(x_8);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = lean_st_ref_take(x_4, x_161);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_163, 3);
lean_inc(x_167);
x_168 = lean_ctor_get(x_163, 4);
lean_inc(x_168);
x_169 = lean_ctor_get(x_163, 5);
lean_inc(x_169);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 lean_ctor_release(x_163, 2);
 lean_ctor_release(x_163, 3);
 lean_ctor_release(x_163, 4);
 lean_ctor_release(x_163, 5);
 x_170 = x_163;
} else {
 lean_dec_ref(x_163);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(0, 6, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_165);
lean_ctor_set(x_171, 1, x_28);
lean_ctor_set(x_171, 2, x_166);
lean_ctor_set(x_171, 3, x_167);
lean_ctor_set(x_171, 4, x_168);
lean_ctor_set(x_171, 5, x_169);
x_172 = lean_st_ref_set(x_4, x_171, x_164);
lean_dec(x_4);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_174 = x_172;
} else {
 lean_dec_ref(x_172);
 x_174 = lean_box(0);
}
x_175 = lean_box(0);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_154);
lean_ctor_set(x_176, 1, x_175);
if (lean_is_scalar(x_174)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_174;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_173);
x_10 = x_177;
goto block_22;
}
}
block_22:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
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
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_run___lambda__1), 9, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_saveState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = l_Lean_Elab_Term_saveState___rarg(x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_7, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_1, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
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
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
lean_object* l_Lean_Elab_Tactic_saveState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_saveState___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_saveState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_saveState___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Elab_Tactic_saveState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_saveState(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = 0;
x_13 = l_Lean_Elab_Term_SavedState_restore(x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_st_ref_get(x_9, x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_set(x_3, x_15, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
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
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 4);
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
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__2;
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__4;
x_2 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticElabAttribute");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinTactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__2;
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__13;
x_2 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__7;
x_3 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__9;
x_4 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__11;
x_5 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_6 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__15;
x_7 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__10;
x_8 = l_Lean_Elab_mkElabAttribute___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute___lambda__1___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Elab_Tactic_tacticElabAttribute___lambda__1___closed__2;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
static uint32_t _init_l_Lean_Elab_Tactic_tacticElabAttribute___lambda__2___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___lambda__2___closed__2() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute___lambda__2___closed__1;
x_2 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute___lambda__2___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_Tactic_tacticElabAttribute___lambda__2___closed__2;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute___lambda__4___closed__1;
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Tactic_tacticElabAttribute___lambda__2___closed__2;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___lambda__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute___lambda__7___closed__1;
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticElabAttribute___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
x_3 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__1;
x_4 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
lean_ctor_set(x_4, 4, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticElabAttribute___lambda__2), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticElabAttribute___lambda__3___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticElabAttribute___lambda__4___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticElabAttribute___lambda__5___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__3;
x_3 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__4;
x_4 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__5;
x_5 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__6;
x_6 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__7;
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
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticElabAttribute___lambda__6___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticElabAttribute___lambda__7___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tacticElabAttribute___lambda__8___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__10;
x_2 = lean_box(0);
x_3 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__11;
x_4 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__6;
x_5 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__12;
x_6 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__13;
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
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__8;
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__14;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__15;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Elab_Tactic_tacticElabAttribute___lambda__1(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_tacticElabAttribute___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute___lambda__4(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_tacticElabAttribute___lambda__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_tacticElabAttribute___lambda__6(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute___lambda__7(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___lambda__8___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute___lambda__8(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_mkTacticInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_st_ref_get(x_11, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_9, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_1);
lean_ctor_set(x_24, 2, x_2);
lean_ctor_set(x_24, 3, x_18);
lean_ctor_set(x_24, 4, x_21);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_1);
lean_ctor_set(x_30, 2, x_2);
lean_ctor_set(x_30, 3, x_18);
lean_ctor_set(x_30, 4, x_26);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
}
lean_object* l_Lean_Elab_Tactic_mkTacticInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_mkTacticInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_mkTacticInfo(x_2, x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_7, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkInitialTacticInfo___elambda__1___boxed), 12, 3);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_16);
lean_closure_set(x_20, 2, x_19);
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
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkInitialTacticInfo___elambda__1___boxed), 12, 3);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_16);
lean_closure_set(x_23, 2, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_mkInitialTacticInfo___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_object* l_Lean_Elab_Tactic_mkInitialTacticInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
static lean_object* _init_l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__2;
x_3 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 5);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_5, x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_take(x_1, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 5);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 5);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_18, 1);
lean_dec(x_23);
x_24 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__3;
lean_ctor_set(x_18, 1, x_24);
x_25 = lean_st_ref_set(x_1, x_17, x_19);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_13);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get_uint8(x_18, sizeof(void*)*2);
x_31 = lean_ctor_get(x_18, 0);
lean_inc(x_31);
lean_dec(x_18);
x_32 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__3;
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_30);
lean_ctor_set(x_17, 5, x_33);
x_34 = lean_st_ref_set(x_1, x_17, x_19);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_13);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_17, 0);
x_39 = lean_ctor_get(x_17, 1);
x_40 = lean_ctor_get(x_17, 2);
x_41 = lean_ctor_get(x_17, 3);
x_42 = lean_ctor_get(x_17, 4);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_17);
x_43 = lean_ctor_get_uint8(x_18, sizeof(void*)*2);
x_44 = lean_ctor_get(x_18, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_45 = x_18;
} else {
 lean_dec_ref(x_18);
 x_45 = lean_box(0);
}
x_46 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__3;
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 1);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_43);
x_48 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_39);
lean_ctor_set(x_48, 2, x_40);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set(x_48, 4, x_42);
lean_ctor_set(x_48, 5, x_47);
x_49 = lean_st_ref_set(x_1, x_48, x_19);
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
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_13);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___boxed), 6, 0);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_withTacticInfoContext___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_10, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_6, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 5);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*2);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg(x_6, x_7, x_8, x_9, x_10, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_27 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_get(x_10, x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_st_ref_get(x_6, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 5);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_10);
lean_inc(x_6);
x_37 = lean_apply_9(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_36);
x_41 = lean_st_ref_get(x_10, x_39);
lean_dec(x_10);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_st_ref_take(x_6, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 5);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_44, 5);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_45, 1);
lean_dec(x_50);
x_51 = l_Std_PersistentArray_push___rarg(x_25, x_40);
lean_ctor_set(x_45, 1, x_51);
x_52 = lean_st_ref_set(x_6, x_44, x_46);
lean_dec(x_6);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_28);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_28);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get_uint8(x_45, sizeof(void*)*2);
x_58 = lean_ctor_get(x_45, 0);
lean_inc(x_58);
lean_dec(x_45);
x_59 = l_Std_PersistentArray_push___rarg(x_25, x_40);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_57);
lean_ctor_set(x_44, 5, x_60);
x_61 = lean_st_ref_set(x_6, x_44, x_46);
lean_dec(x_6);
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
lean_ctor_set(x_64, 0, x_28);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_65 = lean_ctor_get(x_44, 0);
x_66 = lean_ctor_get(x_44, 1);
x_67 = lean_ctor_get(x_44, 2);
x_68 = lean_ctor_get(x_44, 3);
x_69 = lean_ctor_get(x_44, 4);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_44);
x_70 = lean_ctor_get_uint8(x_45, sizeof(void*)*2);
x_71 = lean_ctor_get(x_45, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_72 = x_45;
} else {
 lean_dec_ref(x_45);
 x_72 = lean_box(0);
}
x_73 = l_Std_PersistentArray_push___rarg(x_25, x_40);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 1);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_70);
x_75 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_75, 0, x_65);
lean_ctor_set(x_75, 1, x_66);
lean_ctor_set(x_75, 2, x_67);
lean_ctor_set(x_75, 3, x_68);
lean_ctor_set(x_75, 4, x_69);
lean_ctor_set(x_75, 5, x_74);
x_76 = lean_st_ref_set(x_6, x_75, x_46);
lean_dec(x_6);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_28);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_6);
x_80 = !lean_is_exclusive(x_37);
if (x_80 == 0)
{
return x_37;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_37, 0);
x_82 = lean_ctor_get(x_37, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_37);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_27, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_27, 1);
lean_inc(x_85);
lean_dec(x_27);
x_86 = lean_st_ref_get(x_10, x_85);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_st_ref_get(x_6, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_89, 5);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
lean_inc(x_10);
lean_inc(x_6);
x_93 = lean_apply_9(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_90);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_92);
x_97 = lean_st_ref_get(x_10, x_95);
lean_dec(x_10);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_st_ref_take(x_6, x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 5);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = !lean_is_exclusive(x_100);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_100, 5);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_101);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = lean_ctor_get(x_101, 1);
lean_dec(x_106);
x_107 = l_Std_PersistentArray_push___rarg(x_25, x_96);
lean_ctor_set(x_101, 1, x_107);
x_108 = lean_st_ref_set(x_6, x_100, x_102);
lean_dec(x_6);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_108, 0);
lean_dec(x_110);
lean_ctor_set_tag(x_108, 1);
lean_ctor_set(x_108, 0, x_84);
return x_108;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_84);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
else
{
uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_113 = lean_ctor_get_uint8(x_101, sizeof(void*)*2);
x_114 = lean_ctor_get(x_101, 0);
lean_inc(x_114);
lean_dec(x_101);
x_115 = l_Std_PersistentArray_push___rarg(x_25, x_96);
x_116 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*2, x_113);
lean_ctor_set(x_100, 5, x_116);
x_117 = lean_st_ref_set(x_6, x_100, x_102);
lean_dec(x_6);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
 lean_ctor_set_tag(x_120, 1);
}
lean_ctor_set(x_120, 0, x_84);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_121 = lean_ctor_get(x_100, 0);
x_122 = lean_ctor_get(x_100, 1);
x_123 = lean_ctor_get(x_100, 2);
x_124 = lean_ctor_get(x_100, 3);
x_125 = lean_ctor_get(x_100, 4);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_100);
x_126 = lean_ctor_get_uint8(x_101, sizeof(void*)*2);
x_127 = lean_ctor_get(x_101, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_128 = x_101;
} else {
 lean_dec_ref(x_101);
 x_128 = lean_box(0);
}
x_129 = l_Std_PersistentArray_push___rarg(x_25, x_96);
if (lean_is_scalar(x_128)) {
 x_130 = lean_alloc_ctor(0, 2, 1);
} else {
 x_130 = x_128;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set_uint8(x_130, sizeof(void*)*2, x_126);
x_131 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_131, 0, x_121);
lean_ctor_set(x_131, 1, x_122);
lean_ctor_set(x_131, 2, x_123);
lean_ctor_set(x_131, 3, x_124);
lean_ctor_set(x_131, 4, x_125);
lean_ctor_set(x_131, 5, x_130);
x_132 = lean_st_ref_set(x_6, x_131, x_102);
lean_dec(x_6);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
 lean_ctor_set_tag(x_135, 1);
}
lean_ctor_set(x_135, 0, x_84);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
uint8_t x_136; 
lean_dec(x_92);
lean_dec(x_84);
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_6);
x_136 = !lean_is_exclusive(x_93);
if (x_136 == 0)
{
return x_93;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_93, 0);
x_138 = lean_ctor_get(x_93, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_93);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_withTacticInfoContext(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_apply_3(x_3, x_1, x_7, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 3);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_ctor_set(x_9, 3, x_14);
x_15 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_24 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
x_26 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25, x_10, x_11);
lean_dec(x_25);
return x_26;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected syntax ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
lean_inc(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = l_Lean_indentD(x_13);
x_15 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__1(x_2, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
x_51 = lean_ctor_get(x_20, 0);
lean_inc(x_51);
lean_dec(x_20);
x_52 = lean_ctor_get(x_4, 0);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_inc(x_2);
x_55 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_2, x_54, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_st_ref_get(x_11, x_57);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_st_ref_get(x_7, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 5);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_ctor_get_uint8(x_62, sizeof(void*)*2);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_56);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_dec(x_60);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_65 = lean_apply_10(x_22, x_2, x_54, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_64);
x_23 = x_65;
goto block_50;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
lean_dec(x_60);
x_67 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg(x_7, x_8, x_9, x_10, x_11, x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_54);
lean_inc(x_2);
x_70 = lean_apply_10(x_22, x_2, x_54, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_st_ref_get(x_11, x_72);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_st_ref_get(x_7, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 5);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_80 = lean_apply_9(x_56, x_54, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_77);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_79);
x_84 = lean_st_ref_get(x_11, x_82);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_st_ref_take(x_7, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_87, 5);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = !lean_is_exclusive(x_87);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_87, 5);
lean_dec(x_91);
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_88, 1);
lean_dec(x_93);
x_94 = l_Std_PersistentArray_push___rarg(x_68, x_83);
lean_ctor_set(x_88, 1, x_94);
x_95 = lean_st_ref_set(x_7, x_87, x_89);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_95, 0);
lean_dec(x_97);
lean_ctor_set(x_95, 0, x_71);
x_23 = x_95;
goto block_50;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_71);
lean_ctor_set(x_99, 1, x_98);
x_23 = x_99;
goto block_50;
}
}
else
{
uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_100 = lean_ctor_get_uint8(x_88, sizeof(void*)*2);
x_101 = lean_ctor_get(x_88, 0);
lean_inc(x_101);
lean_dec(x_88);
x_102 = l_Std_PersistentArray_push___rarg(x_68, x_83);
x_103 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*2, x_100);
lean_ctor_set(x_87, 5, x_103);
x_104 = lean_st_ref_set(x_7, x_87, x_89);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_71);
lean_ctor_set(x_107, 1, x_105);
x_23 = x_107;
goto block_50;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_108 = lean_ctor_get(x_87, 0);
x_109 = lean_ctor_get(x_87, 1);
x_110 = lean_ctor_get(x_87, 2);
x_111 = lean_ctor_get(x_87, 3);
x_112 = lean_ctor_get(x_87, 4);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_87);
x_113 = lean_ctor_get_uint8(x_88, sizeof(void*)*2);
x_114 = lean_ctor_get(x_88, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_115 = x_88;
} else {
 lean_dec_ref(x_88);
 x_115 = lean_box(0);
}
x_116 = l_Std_PersistentArray_push___rarg(x_68, x_83);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 2, 1);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set_uint8(x_117, sizeof(void*)*2, x_113);
x_118 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_118, 0, x_108);
lean_ctor_set(x_118, 1, x_109);
lean_ctor_set(x_118, 2, x_110);
lean_ctor_set(x_118, 3, x_111);
lean_ctor_set(x_118, 4, x_112);
lean_ctor_set(x_118, 5, x_117);
x_119 = lean_st_ref_set(x_7, x_118, x_89);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_71);
lean_ctor_set(x_122, 1, x_120);
x_23 = x_122;
goto block_50;
}
}
else
{
uint8_t x_123; 
lean_dec(x_79);
lean_dec(x_71);
lean_dec(x_68);
x_123 = !lean_is_exclusive(x_80);
if (x_123 == 0)
{
x_23 = x_80;
goto block_50;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_80, 0);
x_125 = lean_ctor_get(x_80, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_80);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_23 = x_126;
goto block_50;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_127 = lean_ctor_get(x_70, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_70, 1);
lean_inc(x_128);
lean_dec(x_70);
x_129 = lean_st_ref_get(x_11, x_128);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_st_ref_get(x_7, x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_132, 5);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_136 = lean_apply_9(x_56, x_54, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_133);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_135);
x_140 = lean_st_ref_get(x_11, x_138);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_st_ref_take(x_7, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_143, 5);
lean_inc(x_144);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = !lean_is_exclusive(x_143);
if (x_146 == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = lean_ctor_get(x_143, 5);
lean_dec(x_147);
x_148 = !lean_is_exclusive(x_144);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_149 = lean_ctor_get(x_144, 1);
lean_dec(x_149);
x_150 = l_Std_PersistentArray_push___rarg(x_68, x_139);
lean_ctor_set(x_144, 1, x_150);
x_151 = lean_st_ref_set(x_7, x_143, x_145);
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_151, 0);
lean_dec(x_153);
lean_ctor_set_tag(x_151, 1);
lean_ctor_set(x_151, 0, x_127);
x_23 = x_151;
goto block_50;
}
else
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_127);
lean_ctor_set(x_155, 1, x_154);
x_23 = x_155;
goto block_50;
}
}
else
{
uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_156 = lean_ctor_get_uint8(x_144, sizeof(void*)*2);
x_157 = lean_ctor_get(x_144, 0);
lean_inc(x_157);
lean_dec(x_144);
x_158 = l_Std_PersistentArray_push___rarg(x_68, x_139);
x_159 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set_uint8(x_159, sizeof(void*)*2, x_156);
lean_ctor_set(x_143, 5, x_159);
x_160 = lean_st_ref_set(x_7, x_143, x_145);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
 lean_ctor_set_tag(x_163, 1);
}
lean_ctor_set(x_163, 0, x_127);
lean_ctor_set(x_163, 1, x_161);
x_23 = x_163;
goto block_50;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_164 = lean_ctor_get(x_143, 0);
x_165 = lean_ctor_get(x_143, 1);
x_166 = lean_ctor_get(x_143, 2);
x_167 = lean_ctor_get(x_143, 3);
x_168 = lean_ctor_get(x_143, 4);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_143);
x_169 = lean_ctor_get_uint8(x_144, sizeof(void*)*2);
x_170 = lean_ctor_get(x_144, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_171 = x_144;
} else {
 lean_dec_ref(x_144);
 x_171 = lean_box(0);
}
x_172 = l_Std_PersistentArray_push___rarg(x_68, x_139);
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(0, 2, 1);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set_uint8(x_173, sizeof(void*)*2, x_169);
x_174 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_174, 0, x_164);
lean_ctor_set(x_174, 1, x_165);
lean_ctor_set(x_174, 2, x_166);
lean_ctor_set(x_174, 3, x_167);
lean_ctor_set(x_174, 4, x_168);
lean_ctor_set(x_174, 5, x_173);
x_175 = lean_st_ref_set(x_7, x_174, x_145);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_177 = x_175;
} else {
 lean_dec_ref(x_175);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
 lean_ctor_set_tag(x_178, 1);
}
lean_ctor_set(x_178, 0, x_127);
lean_ctor_set(x_178, 1, x_176);
x_23 = x_178;
goto block_50;
}
}
else
{
uint8_t x_179; 
lean_dec(x_135);
lean_dec(x_127);
lean_dec(x_68);
x_179 = !lean_is_exclusive(x_136);
if (x_179 == 0)
{
x_23 = x_136;
goto block_50;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_136, 0);
x_181 = lean_ctor_get(x_136, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_136);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_23 = x_182;
goto block_50;
}
}
}
}
block_50:
{
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_24);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
lean_inc(x_1);
x_30 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_3 = x_21;
x_12 = x_31;
goto _start;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_23, 1);
x_35 = lean_ctor_get(x_23, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_24, 0);
lean_inc(x_36);
x_37 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_38 = lean_nat_dec_eq(x_36, x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_free_object(x_23);
lean_dec(x_24);
lean_inc(x_1);
x_39 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_34);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_3 = x_21;
x_12 = x_40;
goto _start;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_dec(x_23);
x_43 = lean_ctor_get(x_24, 0);
lean_inc(x_43);
x_44 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_45 = lean_nat_dec_eq(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_24);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_24);
lean_inc(x_1);
x_47 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_42);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_3 = x_21;
x_12 = x_48;
goto _start;
}
}
}
}
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_expandTacticMacroFns_loop_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalTacticAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Tactic_evalTacticAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTacticAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = l_Lean_checkTraceOption(x_11, x_1);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] ");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_9, 3);
x_13 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_10, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 3);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_1);
x_24 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__2;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__4;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_14);
x_30 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_12);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Std_PersistentArray_push___rarg(x_23, x_33);
lean_ctor_set(x_18, 0, x_34);
x_35 = lean_st_ref_set(x_10, x_17, x_19);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_42 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
x_43 = lean_ctor_get(x_18, 0);
lean_inc(x_43);
lean_dec(x_18);
lean_inc(x_1);
x_44 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_44, 0, x_1);
x_45 = l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__2;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__4;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_14);
x_50 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_12);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_12);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Std_PersistentArray_push___rarg(x_43, x_53);
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_42);
lean_ctor_set(x_17, 3, x_55);
x_56 = lean_st_ref_set(x_10, x_17, x_19);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
x_59 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_61 = lean_ctor_get(x_17, 0);
x_62 = lean_ctor_get(x_17, 1);
x_63 = lean_ctor_get(x_17, 2);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_17);
x_64 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
x_65 = lean_ctor_get(x_18, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_66 = x_18;
} else {
 lean_dec_ref(x_18);
 x_66 = lean_box(0);
}
lean_inc(x_1);
x_67 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_67, 0, x_1);
x_68 = l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__2;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__4;
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_14);
x_73 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_74);
lean_inc(x_12);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_12);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Std_PersistentArray_push___rarg(x_65, x_76);
if (lean_is_scalar(x_66)) {
 x_78 = lean_alloc_ctor(0, 1, 1);
} else {
 x_78 = x_66;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_64);
x_79 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_79, 0, x_61);
lean_ctor_set(x_79, 1, x_62);
lean_ctor_set(x_79, 2, x_63);
lean_ctor_set(x_79, 3, x_78);
x_80 = lean_st_ref_set(x_10, x_79, x_19);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
x_83 = lean_box(0);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
}
lean_object* l_List_forM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_get(x_9, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_15);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_1 = x_14;
x_10 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
lean_inc(x_15);
x_24 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_16);
lean_dec(x_15);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_1 = x_14;
x_10 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_16);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3(x_15, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_1 = x_14;
x_10 = x_33;
goto _start;
}
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 3);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_ctor_set(x_9, 3, x_14);
x_15 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__6(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_24 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
x_26 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__6(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25, x_10, x_11);
lean_dec(x_25);
return x_26;
}
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__7___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__7___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__7___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__7___rarg), 1, 0);
return x_9;
}
}
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_17);
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set(x_6, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_24 = x_5;
} else {
 lean_dec_ref(x_5);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
if (lean_is_scalar(x_24)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_24;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
}
else
{
uint8_t x_28; 
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
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Environment_contains(x_1, x_2);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace_x3f(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_8, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 5);
lean_inc(x_16);
lean_inc(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__1___boxed), 4, 1);
lean_closure_set(x_17, 0, x_14);
lean_inc(x_15);
x_18 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_18, 0, x_15);
lean_inc(x_14);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__2___boxed), 4, 1);
lean_closure_set(x_19, 0, x_14);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__3___boxed), 6, 3);
lean_closure_set(x_20, 0, x_14);
lean_closure_set(x_20, 1, x_15);
lean_closure_set(x_20, 2, x_16);
lean_inc(x_14);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__4___boxed), 6, 3);
lean_closure_set(x_21, 0, x_14);
lean_closure_set(x_21, 1, x_15);
lean_closure_set(x_21, 2, x_16);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set(x_22, 4, x_21);
x_23 = x_22;
x_24 = lean_ctor_get(x_8, 3);
lean_inc(x_24);
x_25 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_13);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_8, 2);
lean_inc(x_29);
x_30 = lean_st_ref_get(x_9, x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_environment_main_module(x_14);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_26);
lean_ctor_set(x_35, 3, x_28);
lean_ctor_set(x_35, 4, x_29);
lean_ctor_set(x_35, 5, x_24);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_apply_2(x_1, x_35, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_st_ref_take(x_9, x_32);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_46 = lean_ctor_get(x_43, 1);
lean_dec(x_46);
lean_ctor_set(x_43, 1, x_41);
x_47 = lean_st_ref_set(x_9, x_43, x_44);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_dec(x_40);
x_50 = l_List_reverse___rarg(x_49);
x_51 = l_List_forM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__4(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
lean_dec(x_8);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set(x_51, 0, x_39);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_39);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_56 = lean_ctor_get(x_43, 0);
x_57 = lean_ctor_get(x_43, 2);
x_58 = lean_ctor_get(x_43, 3);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_43);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_41);
lean_ctor_set(x_59, 2, x_57);
lean_ctor_set(x_59, 3, x_58);
x_60 = lean_st_ref_set(x_9, x_59, x_44);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_ctor_get(x_40, 1);
lean_inc(x_62);
lean_dec(x_40);
x_63 = l_List_reverse___rarg(x_62);
x_64 = l_List_forM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__4(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_61);
lean_dec(x_8);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_39);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_38, 0);
lean_inc(x_68);
lean_dec(x_38);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__5(x_69, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
lean_dec(x_69);
return x_73;
}
else
{
lean_object* x_74; 
lean_dec(x_8);
x_74 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__7___rarg(x_32);
return x_74;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_expandTacticMacroFns_loop(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tactic '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has not been implemented");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_1);
x_12 = l_Lean_Syntax_getKind(x_1);
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwErrorAt___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__1(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_32; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
x_21 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_1);
x_25 = lean_apply_1(x_24, x_1);
x_36 = lean_ctor_get(x_19, 0);
lean_inc(x_36);
lean_dec(x_19);
x_37 = lean_ctor_get(x_3, 0);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_1);
x_40 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_1, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_st_ref_get(x_10, x_42);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_st_ref_get(x_6, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 5);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get_uint8(x_47, sizeof(void*)*2);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_41);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
lean_inc(x_9);
x_50 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1(x_25, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_53 = l_Lean_Elab_Tactic_evalTacticAux(x_51, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_52);
lean_dec(x_39);
if (lean_obj_tag(x_53) == 0)
{
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_26 = x_54;
x_27 = x_55;
goto block_31;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_39);
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_dec(x_50);
x_26 = x_56;
x_27 = x_57;
goto block_31;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_119; 
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
lean_dec(x_45);
x_59 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg(x_6, x_7, x_8, x_9, x_10, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_9);
x_119 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1(x_25, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_61);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_122 = l_Lean_Elab_Tactic_evalTacticAux(x_120, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_st_ref_get(x_10, x_124);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_st_ref_get(x_6, x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_128, 5);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_132 = lean_apply_9(x_41, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_129);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_131);
x_136 = lean_st_ref_get(x_10, x_134);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_st_ref_take(x_6, x_137);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_139, 5);
lean_inc(x_140);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = !lean_is_exclusive(x_139);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_139, 5);
lean_dec(x_143);
x_144 = !lean_is_exclusive(x_140);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_145 = lean_ctor_get(x_140, 1);
lean_dec(x_145);
x_146 = l_Std_PersistentArray_push___rarg(x_60, x_135);
lean_ctor_set(x_140, 1, x_146);
x_147 = lean_st_ref_set(x_6, x_139, x_141);
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_147, 0);
lean_dec(x_149);
lean_ctor_set(x_147, 0, x_123);
x_32 = x_147;
goto block_35;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_123);
lean_ctor_set(x_151, 1, x_150);
x_32 = x_151;
goto block_35;
}
}
else
{
uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_152 = lean_ctor_get_uint8(x_140, sizeof(void*)*2);
x_153 = lean_ctor_get(x_140, 0);
lean_inc(x_153);
lean_dec(x_140);
x_154 = l_Std_PersistentArray_push___rarg(x_60, x_135);
x_155 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
lean_ctor_set_uint8(x_155, sizeof(void*)*2, x_152);
lean_ctor_set(x_139, 5, x_155);
x_156 = lean_st_ref_set(x_6, x_139, x_141);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_123);
lean_ctor_set(x_159, 1, x_157);
x_32 = x_159;
goto block_35;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_160 = lean_ctor_get(x_139, 0);
x_161 = lean_ctor_get(x_139, 1);
x_162 = lean_ctor_get(x_139, 2);
x_163 = lean_ctor_get(x_139, 3);
x_164 = lean_ctor_get(x_139, 4);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_139);
x_165 = lean_ctor_get_uint8(x_140, sizeof(void*)*2);
x_166 = lean_ctor_get(x_140, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_167 = x_140;
} else {
 lean_dec_ref(x_140);
 x_167 = lean_box(0);
}
x_168 = l_Std_PersistentArray_push___rarg(x_60, x_135);
if (lean_is_scalar(x_167)) {
 x_169 = lean_alloc_ctor(0, 2, 1);
} else {
 x_169 = x_167;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set_uint8(x_169, sizeof(void*)*2, x_165);
x_170 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_170, 0, x_160);
lean_ctor_set(x_170, 1, x_161);
lean_ctor_set(x_170, 2, x_162);
lean_ctor_set(x_170, 3, x_163);
lean_ctor_set(x_170, 4, x_164);
lean_ctor_set(x_170, 5, x_169);
x_171 = lean_st_ref_set(x_6, x_170, x_141);
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
lean_ctor_set(x_174, 0, x_123);
lean_ctor_set(x_174, 1, x_172);
x_32 = x_174;
goto block_35;
}
}
else
{
uint8_t x_175; 
lean_dec(x_131);
lean_dec(x_123);
lean_dec(x_60);
x_175 = !lean_is_exclusive(x_132);
if (x_175 == 0)
{
x_32 = x_132;
goto block_35;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_132, 0);
x_177 = lean_ctor_get(x_132, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_132);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_32 = x_178;
goto block_35;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_122, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_122, 1);
lean_inc(x_180);
lean_dec(x_122);
x_62 = x_179;
x_63 = x_180;
goto block_118;
}
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_119, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_119, 1);
lean_inc(x_182);
lean_dec(x_119);
x_62 = x_181;
x_63 = x_182;
goto block_118;
}
block_118:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_st_ref_get(x_10, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_st_ref_get(x_6, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 5);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_71 = lean_apply_9(x_41, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_68);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_70);
x_75 = lean_st_ref_get(x_10, x_73);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_st_ref_take(x_6, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 5);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = !lean_is_exclusive(x_78);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_78, 5);
lean_dec(x_82);
x_83 = !lean_is_exclusive(x_79);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_79, 1);
lean_dec(x_84);
x_85 = l_Std_PersistentArray_push___rarg(x_60, x_74);
lean_ctor_set(x_79, 1, x_85);
x_86 = lean_st_ref_set(x_6, x_78, x_80);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
lean_ctor_set_tag(x_86, 1);
lean_ctor_set(x_86, 0, x_62);
x_32 = x_86;
goto block_35;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_62);
lean_ctor_set(x_90, 1, x_89);
x_32 = x_90;
goto block_35;
}
}
else
{
uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_91 = lean_ctor_get_uint8(x_79, sizeof(void*)*2);
x_92 = lean_ctor_get(x_79, 0);
lean_inc(x_92);
lean_dec(x_79);
x_93 = l_Std_PersistentArray_push___rarg(x_60, x_74);
x_94 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_91);
lean_ctor_set(x_78, 5, x_94);
x_95 = lean_st_ref_set(x_6, x_78, x_80);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
 lean_ctor_set_tag(x_98, 1);
}
lean_ctor_set(x_98, 0, x_62);
lean_ctor_set(x_98, 1, x_96);
x_32 = x_98;
goto block_35;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_99 = lean_ctor_get(x_78, 0);
x_100 = lean_ctor_get(x_78, 1);
x_101 = lean_ctor_get(x_78, 2);
x_102 = lean_ctor_get(x_78, 3);
x_103 = lean_ctor_get(x_78, 4);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_78);
x_104 = lean_ctor_get_uint8(x_79, sizeof(void*)*2);
x_105 = lean_ctor_get(x_79, 0);
lean_inc(x_105);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_106 = x_79;
} else {
 lean_dec_ref(x_79);
 x_106 = lean_box(0);
}
x_107 = l_Std_PersistentArray_push___rarg(x_60, x_74);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 2, 1);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set_uint8(x_108, sizeof(void*)*2, x_104);
x_109 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_109, 0, x_99);
lean_ctor_set(x_109, 1, x_100);
lean_ctor_set(x_109, 2, x_101);
lean_ctor_set(x_109, 3, x_102);
lean_ctor_set(x_109, 4, x_103);
lean_ctor_set(x_109, 5, x_108);
x_110 = lean_st_ref_set(x_6, x_109, x_80);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
 lean_ctor_set_tag(x_113, 1);
}
lean_ctor_set(x_113, 0, x_62);
lean_ctor_set(x_113, 1, x_111);
x_32 = x_113;
goto block_35;
}
}
else
{
uint8_t x_114; 
lean_dec(x_70);
lean_dec(x_62);
lean_dec(x_60);
x_114 = !lean_is_exclusive(x_71);
if (x_114 == 0)
{
x_32 = x_71;
goto block_35;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_71, 0);
x_116 = lean_ctor_get(x_71, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_71);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_32 = x_117;
goto block_35;
}
}
}
}
block_31:
{
uint8_t x_28; 
x_28 = l_List_isEmpty___rarg(x_20);
if (x_28 == 0)
{
lean_dec(x_26);
lean_dec(x_23);
x_2 = x_20;
x_11 = x_27;
goto _start;
}
else
{
lean_object* x_30; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_23)) {
 x_30 = lean_alloc_ctor(1, 2, 0);
} else {
 x_30 = x_23;
 lean_ctor_set_tag(x_30, 1);
}
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
block_35:
{
if (lean_obj_tag(x_32) == 0)
{
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_26 = x_33;
x_27 = x_34;
goto block_31;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalTacticAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalTacticAux___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_2 == x_3;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_15 = lean_array_uget(x_1, x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Elab_Tactic_evalTacticAux(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = x_2 + x_19;
x_2 = x_20;
x_4 = x_17;
x_13 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_13);
return x_26;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTacticAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
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
static lean_object* _init_l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("step");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__3;
x_2 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_evalTacticAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_1, x_13);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_10, 1);
lean_dec(x_16);
lean_ctor_set(x_10, 1, x_14);
x_17 = lean_st_ref_take(x_11, x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_nat_add(x_21, x_13);
lean_ctor_set(x_18, 1, x_22);
x_23 = lean_st_ref_set(x_11, x_18, x_19);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_6);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_6, 4);
lean_dec(x_28);
lean_ctor_set(x_6, 4, x_21);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = l_Lean_nullKind;
x_31 = lean_name_eq(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_free_object(x_23);
x_46 = lean_st_ref_get(x_11, x_25);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 3);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*1);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_32 = x_50;
goto block_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__5;
x_53 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2(x_52, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_51);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_32 = x_56;
goto block_45;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
lean_inc(x_2);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_2);
x_59 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3(x_52, x_61, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_57);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_32 = x_63;
goto block_45;
}
}
block_45:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = l_Lean_Elab_Tactic_saveState___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_get(x_11, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_2);
x_40 = l_Lean_Syntax_getKind(x_2);
x_41 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_42 = l_Lean_KeyedDeclsAttribute_getEntries___rarg(x_41, x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_dec(x_34);
x_43 = l_Lean_Elab_Tactic_expandTacticMacro(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_38);
return x_43;
}
else
{
lean_object* x_44; 
x_44 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop(x_34, x_2, x_42, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_38);
return x_44;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = l_Lean_Syntax_getArgs(x_2);
lean_dec(x_2);
x_65 = lean_array_get_size(x_64);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_lt(x_66, x_65);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_6);
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_68 = lean_box(0);
lean_ctor_set(x_23, 0, x_68);
return x_23;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_65, x_65);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_6);
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_70 = lean_box(0);
lean_ctor_set(x_23, 0, x_70);
return x_23;
}
else
{
size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; 
lean_free_object(x_23);
x_71 = 0;
x_72 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_73 = lean_box(0);
x_74 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalTacticAux___spec__1(x_64, x_71, x_72, x_73, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
lean_dec(x_64);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_free_object(x_23);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_2);
x_76 = l_Lean_indentD(x_75);
x_77 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__2;
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2(x_80, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; 
x_82 = lean_ctor_get(x_6, 0);
x_83 = lean_ctor_get(x_6, 1);
x_84 = lean_ctor_get(x_6, 2);
x_85 = lean_ctor_get(x_6, 3);
x_86 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
x_87 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 1);
x_88 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 2);
x_89 = lean_ctor_get(x_6, 5);
x_90 = lean_ctor_get(x_6, 6);
x_91 = lean_ctor_get(x_6, 7);
x_92 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 3);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_6);
x_93 = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(x_93, 0, x_82);
lean_ctor_set(x_93, 1, x_83);
lean_ctor_set(x_93, 2, x_84);
lean_ctor_set(x_93, 3, x_85);
lean_ctor_set(x_93, 4, x_21);
lean_ctor_set(x_93, 5, x_89);
lean_ctor_set(x_93, 6, x_90);
lean_ctor_set(x_93, 7, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*8, x_86);
lean_ctor_set_uint8(x_93, sizeof(void*)*8 + 1, x_87);
lean_ctor_set_uint8(x_93, sizeof(void*)*8 + 2, x_88);
lean_ctor_set_uint8(x_93, sizeof(void*)*8 + 3, x_92);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = lean_ctor_get(x_2, 0);
lean_inc(x_94);
x_95 = l_Lean_nullKind;
x_96 = lean_name_eq(x_94, x_95);
lean_dec(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
lean_free_object(x_23);
x_111 = lean_st_ref_get(x_11, x_25);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_112, 3);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_ctor_get_uint8(x_113, sizeof(void*)*1);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
lean_dec(x_111);
x_97 = x_115;
goto block_110;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
lean_dec(x_111);
x_117 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__5;
x_118 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2(x_117, x_4, x_5, x_93, x_7, x_8, x_9, x_10, x_11, x_116);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_97 = x_121;
goto block_110;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
lean_dec(x_118);
lean_inc(x_2);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_2);
x_124 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_125 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3(x_117, x_126, x_4, x_5, x_93, x_7, x_8, x_9, x_10, x_11, x_122);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_97 = x_128;
goto block_110;
}
}
block_110:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_98 = l_Lean_Elab_Tactic_saveState___rarg(x_5, x_93, x_7, x_8, x_9, x_10, x_11, x_97);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_st_ref_get(x_11, x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_ctor_get(x_102, 0);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_2);
x_105 = l_Lean_Syntax_getKind(x_2);
x_106 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_107 = l_Lean_KeyedDeclsAttribute_getEntries___rarg(x_106, x_104, x_105);
lean_dec(x_105);
lean_dec(x_104);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
lean_dec(x_99);
x_108 = l_Lean_Elab_Tactic_expandTacticMacro(x_2, x_4, x_5, x_93, x_7, x_8, x_9, x_10, x_11, x_103);
return x_108;
}
else
{
lean_object* x_109; 
x_109 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop(x_99, x_2, x_107, x_4, x_5, x_93, x_7, x_8, x_9, x_10, x_11, x_103);
return x_109;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_129 = l_Lean_Syntax_getArgs(x_2);
lean_dec(x_2);
x_130 = lean_array_get_size(x_129);
x_131 = lean_unsigned_to_nat(0u);
x_132 = lean_nat_dec_lt(x_131, x_130);
if (x_132 == 0)
{
lean_object* x_133; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_93);
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_133 = lean_box(0);
lean_ctor_set(x_23, 0, x_133);
return x_23;
}
else
{
uint8_t x_134; 
x_134 = lean_nat_dec_le(x_130, x_130);
if (x_134 == 0)
{
lean_object* x_135; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_93);
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_135 = lean_box(0);
lean_ctor_set(x_23, 0, x_135);
return x_23;
}
else
{
size_t x_136; size_t x_137; lean_object* x_138; lean_object* x_139; 
lean_free_object(x_23);
x_136 = 0;
x_137 = lean_usize_of_nat(x_130);
lean_dec(x_130);
x_138 = lean_box(0);
x_139 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalTacticAux___spec__1(x_129, x_136, x_137, x_138, x_4, x_5, x_93, x_7, x_8, x_9, x_10, x_11, x_25);
lean_dec(x_129);
return x_139;
}
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_free_object(x_23);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_2);
x_141 = l_Lean_indentD(x_140);
x_142 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__2;
x_143 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
x_144 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_145 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2(x_145, x_4, x_5, x_93, x_7, x_8, x_9, x_10, x_11, x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_93);
lean_dec(x_5);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; 
x_147 = lean_ctor_get(x_23, 1);
lean_inc(x_147);
lean_dec(x_23);
x_148 = lean_ctor_get(x_6, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_6, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_6, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_6, 3);
lean_inc(x_151);
x_152 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
x_153 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 1);
x_154 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 2);
x_155 = lean_ctor_get(x_6, 5);
lean_inc(x_155);
x_156 = lean_ctor_get(x_6, 6);
lean_inc(x_156);
x_157 = lean_ctor_get(x_6, 7);
lean_inc(x_157);
x_158 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 3);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 lean_ctor_release(x_6, 7);
 x_159 = x_6;
} else {
 lean_dec_ref(x_6);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(0, 8, 4);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_148);
lean_ctor_set(x_160, 1, x_149);
lean_ctor_set(x_160, 2, x_150);
lean_ctor_set(x_160, 3, x_151);
lean_ctor_set(x_160, 4, x_21);
lean_ctor_set(x_160, 5, x_155);
lean_ctor_set(x_160, 6, x_156);
lean_ctor_set(x_160, 7, x_157);
lean_ctor_set_uint8(x_160, sizeof(void*)*8, x_152);
lean_ctor_set_uint8(x_160, sizeof(void*)*8 + 1, x_153);
lean_ctor_set_uint8(x_160, sizeof(void*)*8 + 2, x_154);
lean_ctor_set_uint8(x_160, sizeof(void*)*8 + 3, x_158);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_2, 0);
lean_inc(x_161);
x_162 = l_Lean_nullKind;
x_163 = lean_name_eq(x_161, x_162);
lean_dec(x_161);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_178 = lean_st_ref_get(x_11, x_147);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_179, 3);
lean_inc(x_180);
lean_dec(x_179);
x_181 = lean_ctor_get_uint8(x_180, sizeof(void*)*1);
lean_dec(x_180);
if (x_181 == 0)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_178, 1);
lean_inc(x_182);
lean_dec(x_178);
x_164 = x_182;
goto block_177;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_183 = lean_ctor_get(x_178, 1);
lean_inc(x_183);
lean_dec(x_178);
x_184 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__5;
x_185 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2(x_184, x_4, x_5, x_160, x_7, x_8, x_9, x_10, x_11, x_183);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_unbox(x_186);
lean_dec(x_186);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
lean_dec(x_185);
x_164 = x_188;
goto block_177;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_189 = lean_ctor_get(x_185, 1);
lean_inc(x_189);
lean_dec(x_185);
lean_inc(x_2);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_2);
x_191 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_192 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
x_193 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
x_194 = l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3(x_184, x_193, x_4, x_5, x_160, x_7, x_8, x_9, x_10, x_11, x_189);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_164 = x_195;
goto block_177;
}
}
block_177:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_165 = l_Lean_Elab_Tactic_saveState___rarg(x_5, x_160, x_7, x_8, x_9, x_10, x_11, x_164);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_st_ref_get(x_11, x_167);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
lean_dec(x_169);
lean_inc(x_2);
x_172 = l_Lean_Syntax_getKind(x_2);
x_173 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_174 = l_Lean_KeyedDeclsAttribute_getEntries___rarg(x_173, x_171, x_172);
lean_dec(x_172);
lean_dec(x_171);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; 
lean_dec(x_166);
x_175 = l_Lean_Elab_Tactic_expandTacticMacro(x_2, x_4, x_5, x_160, x_7, x_8, x_9, x_10, x_11, x_170);
return x_175;
}
else
{
lean_object* x_176; 
x_176 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop(x_166, x_2, x_174, x_4, x_5, x_160, x_7, x_8, x_9, x_10, x_11, x_170);
return x_176;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_196 = l_Lean_Syntax_getArgs(x_2);
lean_dec(x_2);
x_197 = lean_array_get_size(x_196);
x_198 = lean_unsigned_to_nat(0u);
x_199 = lean_nat_dec_lt(x_198, x_197);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_160);
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_200 = lean_box(0);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_147);
return x_201;
}
else
{
uint8_t x_202; 
x_202 = lean_nat_dec_le(x_197, x_197);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_160);
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_203 = lean_box(0);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_147);
return x_204;
}
else
{
size_t x_205; size_t x_206; lean_object* x_207; lean_object* x_208; 
x_205 = 0;
x_206 = lean_usize_of_nat(x_197);
lean_dec(x_197);
x_207 = lean_box(0);
x_208 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalTacticAux___spec__1(x_196, x_205, x_206, x_207, x_4, x_5, x_160, x_7, x_8, x_9, x_10, x_11, x_147);
lean_dec(x_196);
return x_208;
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_2);
x_210 = l_Lean_indentD(x_209);
x_211 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__2;
x_212 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_210);
x_213 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_214 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_215 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2(x_214, x_4, x_5, x_160, x_7, x_8, x_9, x_10, x_11, x_147);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_160);
lean_dec(x_5);
return x_215;
}
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; uint8_t x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; 
x_216 = lean_ctor_get(x_18, 0);
x_217 = lean_ctor_get(x_18, 1);
x_218 = lean_ctor_get(x_18, 2);
x_219 = lean_ctor_get(x_18, 3);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_18);
x_220 = lean_nat_add(x_217, x_13);
x_221 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_221, 0, x_216);
lean_ctor_set(x_221, 1, x_220);
lean_ctor_set(x_221, 2, x_218);
lean_ctor_set(x_221, 3, x_219);
x_222 = lean_st_ref_set(x_11, x_221, x_19);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_224 = x_222;
} else {
 lean_dec_ref(x_222);
 x_224 = lean_box(0);
}
x_225 = lean_ctor_get(x_6, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_6, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_6, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_6, 3);
lean_inc(x_228);
x_229 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
x_230 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 1);
x_231 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 2);
x_232 = lean_ctor_get(x_6, 5);
lean_inc(x_232);
x_233 = lean_ctor_get(x_6, 6);
lean_inc(x_233);
x_234 = lean_ctor_get(x_6, 7);
lean_inc(x_234);
x_235 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 3);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 lean_ctor_release(x_6, 7);
 x_236 = x_6;
} else {
 lean_dec_ref(x_6);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(0, 8, 4);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_225);
lean_ctor_set(x_237, 1, x_226);
lean_ctor_set(x_237, 2, x_227);
lean_ctor_set(x_237, 3, x_228);
lean_ctor_set(x_237, 4, x_217);
lean_ctor_set(x_237, 5, x_232);
lean_ctor_set(x_237, 6, x_233);
lean_ctor_set(x_237, 7, x_234);
lean_ctor_set_uint8(x_237, sizeof(void*)*8, x_229);
lean_ctor_set_uint8(x_237, sizeof(void*)*8 + 1, x_230);
lean_ctor_set_uint8(x_237, sizeof(void*)*8 + 2, x_231);
lean_ctor_set_uint8(x_237, sizeof(void*)*8 + 3, x_235);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_238 = lean_ctor_get(x_2, 0);
lean_inc(x_238);
x_239 = l_Lean_nullKind;
x_240 = lean_name_eq(x_238, x_239);
lean_dec(x_238);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
lean_dec(x_224);
x_255 = lean_st_ref_get(x_11, x_223);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_256, 3);
lean_inc(x_257);
lean_dec(x_256);
x_258 = lean_ctor_get_uint8(x_257, sizeof(void*)*1);
lean_dec(x_257);
if (x_258 == 0)
{
lean_object* x_259; 
x_259 = lean_ctor_get(x_255, 1);
lean_inc(x_259);
lean_dec(x_255);
x_241 = x_259;
goto block_254;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_260 = lean_ctor_get(x_255, 1);
lean_inc(x_260);
lean_dec(x_255);
x_261 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__5;
x_262 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2(x_261, x_4, x_5, x_237, x_7, x_8, x_9, x_10, x_11, x_260);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_unbox(x_263);
lean_dec(x_263);
if (x_264 == 0)
{
lean_object* x_265; 
x_265 = lean_ctor_get(x_262, 1);
lean_inc(x_265);
lean_dec(x_262);
x_241 = x_265;
goto block_254;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_266 = lean_ctor_get(x_262, 1);
lean_inc(x_266);
lean_dec(x_262);
lean_inc(x_2);
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_2);
x_268 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_269 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_267);
x_270 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_268);
x_271 = l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3(x_261, x_270, x_4, x_5, x_237, x_7, x_8, x_9, x_10, x_11, x_266);
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
lean_dec(x_271);
x_241 = x_272;
goto block_254;
}
}
block_254:
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_242 = l_Lean_Elab_Tactic_saveState___rarg(x_5, x_237, x_7, x_8, x_9, x_10, x_11, x_241);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_st_ref_get(x_11, x_244);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
lean_dec(x_246);
lean_inc(x_2);
x_249 = l_Lean_Syntax_getKind(x_2);
x_250 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_251 = l_Lean_KeyedDeclsAttribute_getEntries___rarg(x_250, x_248, x_249);
lean_dec(x_249);
lean_dec(x_248);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; 
lean_dec(x_243);
x_252 = l_Lean_Elab_Tactic_expandTacticMacro(x_2, x_4, x_5, x_237, x_7, x_8, x_9, x_10, x_11, x_247);
return x_252;
}
else
{
lean_object* x_253; 
x_253 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop(x_243, x_2, x_251, x_4, x_5, x_237, x_7, x_8, x_9, x_10, x_11, x_247);
return x_253;
}
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_273 = l_Lean_Syntax_getArgs(x_2);
lean_dec(x_2);
x_274 = lean_array_get_size(x_273);
x_275 = lean_unsigned_to_nat(0u);
x_276 = lean_nat_dec_lt(x_275, x_274);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; 
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_237);
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_277 = lean_box(0);
if (lean_is_scalar(x_224)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_224;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_223);
return x_278;
}
else
{
uint8_t x_279; 
x_279 = lean_nat_dec_le(x_274, x_274);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; 
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_237);
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_280 = lean_box(0);
if (lean_is_scalar(x_224)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_224;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_223);
return x_281;
}
else
{
size_t x_282; size_t x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_224);
x_282 = 0;
x_283 = lean_usize_of_nat(x_274);
lean_dec(x_274);
x_284 = lean_box(0);
x_285 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalTacticAux___spec__1(x_273, x_282, x_283, x_284, x_4, x_5, x_237, x_7, x_8, x_9, x_10, x_11, x_223);
lean_dec(x_273);
return x_285;
}
}
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_224);
x_286 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_286, 0, x_2);
x_287 = l_Lean_indentD(x_286);
x_288 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__2;
x_289 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_287);
x_290 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_291 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
x_292 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2(x_291, x_4, x_5, x_237, x_7, x_8, x_9, x_10, x_11, x_223);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_237);
lean_dec(x_5);
return x_292;
}
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; uint8_t x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; lean_object* x_325; lean_object* x_326; 
x_293 = lean_ctor_get(x_10, 0);
x_294 = lean_ctor_get(x_10, 2);
x_295 = lean_ctor_get(x_10, 3);
x_296 = lean_ctor_get(x_10, 4);
x_297 = lean_ctor_get(x_10, 5);
x_298 = lean_ctor_get(x_10, 6);
x_299 = lean_ctor_get(x_10, 7);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_10);
x_300 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_300, 0, x_293);
lean_ctor_set(x_300, 1, x_14);
lean_ctor_set(x_300, 2, x_294);
lean_ctor_set(x_300, 3, x_295);
lean_ctor_set(x_300, 4, x_296);
lean_ctor_set(x_300, 5, x_297);
lean_ctor_set(x_300, 6, x_298);
lean_ctor_set(x_300, 7, x_299);
x_301 = lean_st_ref_take(x_11, x_12);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
x_304 = lean_ctor_get(x_302, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_302, 1);
lean_inc(x_305);
x_306 = lean_ctor_get(x_302, 2);
lean_inc(x_306);
x_307 = lean_ctor_get(x_302, 3);
lean_inc(x_307);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 lean_ctor_release(x_302, 2);
 lean_ctor_release(x_302, 3);
 x_308 = x_302;
} else {
 lean_dec_ref(x_302);
 x_308 = lean_box(0);
}
x_309 = lean_nat_add(x_305, x_13);
if (lean_is_scalar(x_308)) {
 x_310 = lean_alloc_ctor(0, 4, 0);
} else {
 x_310 = x_308;
}
lean_ctor_set(x_310, 0, x_304);
lean_ctor_set(x_310, 1, x_309);
lean_ctor_set(x_310, 2, x_306);
lean_ctor_set(x_310, 3, x_307);
x_311 = lean_st_ref_set(x_11, x_310, x_303);
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_313 = x_311;
} else {
 lean_dec_ref(x_311);
 x_313 = lean_box(0);
}
x_314 = lean_ctor_get(x_6, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_6, 1);
lean_inc(x_315);
x_316 = lean_ctor_get(x_6, 2);
lean_inc(x_316);
x_317 = lean_ctor_get(x_6, 3);
lean_inc(x_317);
x_318 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
x_319 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 1);
x_320 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 2);
x_321 = lean_ctor_get(x_6, 5);
lean_inc(x_321);
x_322 = lean_ctor_get(x_6, 6);
lean_inc(x_322);
x_323 = lean_ctor_get(x_6, 7);
lean_inc(x_323);
x_324 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 3);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 lean_ctor_release(x_6, 7);
 x_325 = x_6;
} else {
 lean_dec_ref(x_6);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(0, 8, 4);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_314);
lean_ctor_set(x_326, 1, x_315);
lean_ctor_set(x_326, 2, x_316);
lean_ctor_set(x_326, 3, x_317);
lean_ctor_set(x_326, 4, x_305);
lean_ctor_set(x_326, 5, x_321);
lean_ctor_set(x_326, 6, x_322);
lean_ctor_set(x_326, 7, x_323);
lean_ctor_set_uint8(x_326, sizeof(void*)*8, x_318);
lean_ctor_set_uint8(x_326, sizeof(void*)*8 + 1, x_319);
lean_ctor_set_uint8(x_326, sizeof(void*)*8 + 2, x_320);
lean_ctor_set_uint8(x_326, sizeof(void*)*8 + 3, x_324);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_327 = lean_ctor_get(x_2, 0);
lean_inc(x_327);
x_328 = l_Lean_nullKind;
x_329 = lean_name_eq(x_327, x_328);
lean_dec(x_327);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; 
lean_dec(x_313);
x_344 = lean_st_ref_get(x_11, x_312);
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_345, 3);
lean_inc(x_346);
lean_dec(x_345);
x_347 = lean_ctor_get_uint8(x_346, sizeof(void*)*1);
lean_dec(x_346);
if (x_347 == 0)
{
lean_object* x_348; 
x_348 = lean_ctor_get(x_344, 1);
lean_inc(x_348);
lean_dec(x_344);
x_330 = x_348;
goto block_343;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; 
x_349 = lean_ctor_get(x_344, 1);
lean_inc(x_349);
lean_dec(x_344);
x_350 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__5;
x_351 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2(x_350, x_4, x_5, x_326, x_7, x_8, x_9, x_300, x_11, x_349);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_unbox(x_352);
lean_dec(x_352);
if (x_353 == 0)
{
lean_object* x_354; 
x_354 = lean_ctor_get(x_351, 1);
lean_inc(x_354);
lean_dec(x_351);
x_330 = x_354;
goto block_343;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_355 = lean_ctor_get(x_351, 1);
lean_inc(x_355);
lean_dec(x_351);
lean_inc(x_2);
x_356 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_356, 0, x_2);
x_357 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_358 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_356);
x_359 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_357);
x_360 = l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3(x_350, x_359, x_4, x_5, x_326, x_7, x_8, x_9, x_300, x_11, x_355);
x_361 = lean_ctor_get(x_360, 1);
lean_inc(x_361);
lean_dec(x_360);
x_330 = x_361;
goto block_343;
}
}
block_343:
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_331 = l_Lean_Elab_Tactic_saveState___rarg(x_5, x_326, x_7, x_8, x_9, x_300, x_11, x_330);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = lean_st_ref_get(x_11, x_333);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
x_337 = lean_ctor_get(x_335, 0);
lean_inc(x_337);
lean_dec(x_335);
lean_inc(x_2);
x_338 = l_Lean_Syntax_getKind(x_2);
x_339 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_340 = l_Lean_KeyedDeclsAttribute_getEntries___rarg(x_339, x_337, x_338);
lean_dec(x_338);
lean_dec(x_337);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; 
lean_dec(x_332);
x_341 = l_Lean_Elab_Tactic_expandTacticMacro(x_2, x_4, x_5, x_326, x_7, x_8, x_9, x_300, x_11, x_336);
return x_341;
}
else
{
lean_object* x_342; 
x_342 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop(x_332, x_2, x_340, x_4, x_5, x_326, x_7, x_8, x_9, x_300, x_11, x_336);
return x_342;
}
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; 
x_362 = l_Lean_Syntax_getArgs(x_2);
lean_dec(x_2);
x_363 = lean_array_get_size(x_362);
x_364 = lean_unsigned_to_nat(0u);
x_365 = lean_nat_dec_lt(x_364, x_363);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; 
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_326);
lean_dec(x_300);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_366 = lean_box(0);
if (lean_is_scalar(x_313)) {
 x_367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_367 = x_313;
}
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_312);
return x_367;
}
else
{
uint8_t x_368; 
x_368 = lean_nat_dec_le(x_363, x_363);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; 
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_326);
lean_dec(x_300);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_369 = lean_box(0);
if (lean_is_scalar(x_313)) {
 x_370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_370 = x_313;
}
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_312);
return x_370;
}
else
{
size_t x_371; size_t x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_313);
x_371 = 0;
x_372 = lean_usize_of_nat(x_363);
lean_dec(x_363);
x_373 = lean_box(0);
x_374 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalTacticAux___spec__1(x_362, x_371, x_372, x_373, x_4, x_5, x_326, x_7, x_8, x_9, x_300, x_11, x_312);
lean_dec(x_362);
return x_374;
}
}
}
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_313);
x_375 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_375, 0, x_2);
x_376 = l_Lean_indentD(x_375);
x_377 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__2;
x_378 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_376);
x_379 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_380 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
x_381 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2(x_380, x_4, x_5, x_326, x_7, x_8, x_9, x_300, x_11, x_312);
lean_dec(x_11);
lean_dec(x_300);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_326);
lean_dec(x_5);
return x_381;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTacticAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalTacticAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalTacticAux___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalTacticAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_8, 2);
x_14 = lean_ctor_get(x_8, 3);
x_15 = l_Lean_replaceRef(x_1, x_14);
lean_dec(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_ctor_set(x_8, 3, x_15);
x_16 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1(x_12, x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_12);
lean_dec(x_1);
x_19 = l_Lean_Elab_Tactic_evalTacticAux___closed__2;
x_20 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTacticAux___spec__2(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
x_27 = lean_ctor_get(x_8, 2);
x_28 = lean_ctor_get(x_8, 3);
x_29 = lean_ctor_get(x_8, 4);
x_30 = lean_ctor_get(x_8, 5);
x_31 = lean_ctor_get(x_8, 6);
x_32 = lean_ctor_get(x_8, 7);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_33 = l_Lean_replaceRef(x_1, x_28);
lean_dec(x_28);
lean_inc(x_27);
lean_inc(x_26);
x_34 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_27);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_29);
lean_ctor_set(x_34, 5, x_30);
lean_ctor_set(x_34, 6, x_31);
lean_ctor_set(x_34, 7, x_32);
x_35 = lean_nat_dec_eq(x_26, x_27);
lean_dec(x_27);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(0);
x_37 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1(x_26, x_1, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_34, x_9, x_10);
lean_dec(x_26);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_26);
lean_dec(x_1);
x_38 = l_Lean_Elab_Tactic_evalTacticAux___closed__2;
x_39 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTacticAux___spec__2(x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_34, x_9, x_10);
lean_dec(x_9);
lean_dec(x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_expandTacticMacro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_1);
x_15 = l_Lean_Syntax_getKind(x_1);
x_16 = l_Lean_Elab_macroAttribute;
x_17 = l_Lean_KeyedDeclsAttribute_getEntries___rarg(x_16, x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_18 = l_Lean_Elab_Tactic_expandTacticMacroFns_loop(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_18;
}
}
lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_expandTacticMacroFns_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_List_forM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns_loop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_expandTacticMacroFns_loop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_expandTacticMacroFns_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalTacticAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalTacticAux___spec__1(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTacticAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTacticAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Elab_Tactic_evalTacticAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_evalTacticAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalTacticAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_expandTacticMacro___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_expandTacticMacro(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_expandTacticMacroFns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_expandTacticMacroFns(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_throwNoGoalsToBeSolved___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_throwNoGoalsToBeSolved___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Tactic_throwNoGoalsToBeSolved___spec__1___rarg___boxed), 10, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no goals to be solved");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__2;
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_throwNoGoalsToBeSolved___spec__1___rarg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_throwNoGoalsToBeSolved___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_throwNoGoalsToBeSolved___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_abortTacticExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg), 1, 0);
return x_9;
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
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg(x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_box(0);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = l_List_isEmpty___rarg(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_Lean_Elab_Term_reportUnsolvedGoals(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg(x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_31 = x_26;
} else {
 lean_dec_ref(x_26);
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
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
return x_34;
}
}
}
}
lean_object* l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Elab_Tactic_done___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_done(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Tactic_focus_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Tactic_focus_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_focus_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_focus___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_12, 1);
x_18 = lean_box(0);
lean_ctor_set(x_12, 1, x_18);
x_19 = l_Lean_Elab_Tactic_setGoals(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_List_append___rarg(x_25, x_17);
x_28 = l_Lean_Elab_Tactic_setGoals(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_22);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_12);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Elab_Tactic_setGoals(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_43 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_List_append___rarg(x_47, x_38);
x_50 = l_Lean_Elab_Tactic_setGoals(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_38);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = lean_ctor_get(x_43, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_56 = x_43;
} else {
 lean_dec_ref(x_43);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
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
lean_object* l_Lean_Elab_Tactic_focusAndDone___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Tactic_done(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_12);
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
lean_object* l_Lean_Elab_Tactic_focusAndDone___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_focusAndDone___rarg___lambda__1), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_focus___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_focusAndDone(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_focusAndDone___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_294; uint8_t x_295; 
x_294 = 2;
x_295 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_102_(x_3, x_294);
if (x_295 == 0)
{
lean_object* x_296; 
x_296 = lean_box(0);
x_13 = x_296;
goto block_293;
}
else
{
uint8_t x_297; 
lean_inc(x_2);
x_297 = l_Lean_MessageData_hasSyntheticSorry(x_2);
if (x_297 == 0)
{
lean_object* x_298; 
x_298 = lean_box(0);
x_13 = x_298;
goto block_293;
}
else
{
lean_object* x_299; lean_object* x_300; 
lean_dec(x_2);
x_299 = lean_box(0);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_12);
return x_300;
}
}
block_293:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
x_14 = lean_ctor_get(x_10, 3);
x_15 = l_Lean_replaceRef(x_1, x_14);
x_16 = 0;
x_17 = l_Lean_Syntax_getPos_x3f(x_15, x_16);
x_18 = l_Lean_Syntax_getTailPos_x3f(x_15, x_16);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
x_21 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_FileMap_toPosition(x_20, x_24);
lean_inc(x_25);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_ctor_get(x_10, 4);
x_28 = lean_ctor_get(x_10, 5);
lean_inc(x_28);
lean_inc(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
x_31 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
lean_inc(x_19);
x_32 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_25);
lean_ctor_set(x_32, 2, x_26);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set(x_32, 4, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*5, x_3);
x_33 = lean_st_ref_get(x_11, x_23);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_st_ref_take(x_7, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_36, 3);
x_40 = l_Std_PersistentArray_push___rarg(x_39, x_32);
lean_ctor_set(x_36, 3, x_40);
x_41 = lean_st_ref_set(x_7, x_36, x_37);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_48 = lean_ctor_get(x_36, 0);
x_49 = lean_ctor_get(x_36, 1);
x_50 = lean_ctor_get(x_36, 2);
x_51 = lean_ctor_get(x_36, 3);
x_52 = lean_ctor_get(x_36, 4);
x_53 = lean_ctor_get(x_36, 5);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_36);
x_54 = l_Std_PersistentArray_push___rarg(x_51, x_32);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_49);
lean_ctor_set(x_55, 2, x_50);
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 4, x_52);
lean_ctor_set(x_55, 5, x_53);
x_56 = lean_st_ref_set(x_7, x_55, x_37);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
x_59 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_18);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_62 = lean_ctor_get(x_18, 0);
x_63 = lean_ctor_get(x_6, 0);
x_64 = lean_ctor_get(x_6, 1);
x_65 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Lean_FileMap_toPosition(x_64, x_68);
x_70 = l_Lean_FileMap_toPosition(x_64, x_62);
lean_dec(x_62);
lean_ctor_set(x_18, 0, x_70);
x_71 = lean_ctor_get(x_10, 4);
x_72 = lean_ctor_get(x_10, 5);
lean_inc(x_72);
lean_inc(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_66);
x_75 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
lean_inc(x_63);
x_76 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_76, 0, x_63);
lean_ctor_set(x_76, 1, x_69);
lean_ctor_set(x_76, 2, x_18);
lean_ctor_set(x_76, 3, x_75);
lean_ctor_set(x_76, 4, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*5, x_3);
x_77 = lean_st_ref_get(x_11, x_67);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_st_ref_take(x_7, x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_80, 3);
x_84 = l_Std_PersistentArray_push___rarg(x_83, x_76);
lean_ctor_set(x_80, 3, x_84);
x_85 = lean_st_ref_set(x_7, x_80, x_81);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = lean_box(0);
lean_ctor_set(x_85, 0, x_88);
return x_85;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_dec(x_85);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_92 = lean_ctor_get(x_80, 0);
x_93 = lean_ctor_get(x_80, 1);
x_94 = lean_ctor_get(x_80, 2);
x_95 = lean_ctor_get(x_80, 3);
x_96 = lean_ctor_get(x_80, 4);
x_97 = lean_ctor_get(x_80, 5);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_80);
x_98 = l_Std_PersistentArray_push___rarg(x_95, x_76);
x_99 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_99, 0, x_92);
lean_ctor_set(x_99, 1, x_93);
lean_ctor_set(x_99, 2, x_94);
lean_ctor_set(x_99, 3, x_98);
lean_ctor_set(x_99, 4, x_96);
lean_ctor_set(x_99, 5, x_97);
x_100 = lean_st_ref_set(x_7, x_99, x_81);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = lean_box(0);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_105 = lean_ctor_get(x_18, 0);
lean_inc(x_105);
lean_dec(x_18);
x_106 = lean_ctor_get(x_6, 0);
x_107 = lean_ctor_get(x_6, 1);
x_108 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_unsigned_to_nat(0u);
x_112 = l_Lean_FileMap_toPosition(x_107, x_111);
x_113 = l_Lean_FileMap_toPosition(x_107, x_105);
lean_dec(x_105);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_ctor_get(x_10, 4);
x_116 = lean_ctor_get(x_10, 5);
lean_inc(x_116);
lean_inc(x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_109);
x_119 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
lean_inc(x_106);
x_120 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_120, 0, x_106);
lean_ctor_set(x_120, 1, x_112);
lean_ctor_set(x_120, 2, x_114);
lean_ctor_set(x_120, 3, x_119);
lean_ctor_set(x_120, 4, x_118);
lean_ctor_set_uint8(x_120, sizeof(void*)*5, x_3);
x_121 = lean_st_ref_get(x_11, x_110);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_st_ref_take(x_7, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_124, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_124, 3);
lean_inc(x_129);
x_130 = lean_ctor_get(x_124, 4);
lean_inc(x_130);
x_131 = lean_ctor_get(x_124, 5);
lean_inc(x_131);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 lean_ctor_release(x_124, 4);
 lean_ctor_release(x_124, 5);
 x_132 = x_124;
} else {
 lean_dec_ref(x_124);
 x_132 = lean_box(0);
}
x_133 = l_Std_PersistentArray_push___rarg(x_129, x_120);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(0, 6, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_126);
lean_ctor_set(x_134, 1, x_127);
lean_ctor_set(x_134, 2, x_128);
lean_ctor_set(x_134, 3, x_133);
lean_ctor_set(x_134, 4, x_130);
lean_ctor_set(x_134, 5, x_131);
x_135 = lean_st_ref_set(x_7, x_134, x_125);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_137 = x_135;
} else {
 lean_dec_ref(x_135);
 x_137 = lean_box(0);
}
x_138 = lean_box(0);
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_136);
return x_139;
}
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_17);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_141 = lean_ctor_get(x_17, 0);
x_142 = lean_ctor_get(x_6, 0);
x_143 = lean_ctor_get(x_6, 1);
x_144 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_FileMap_toPosition(x_143, x_141);
lean_dec(x_141);
lean_inc(x_147);
lean_ctor_set(x_17, 0, x_147);
x_148 = lean_ctor_get(x_10, 4);
x_149 = lean_ctor_get(x_10, 5);
lean_inc(x_149);
lean_inc(x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_145);
x_152 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
lean_inc(x_142);
x_153 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_153, 0, x_142);
lean_ctor_set(x_153, 1, x_147);
lean_ctor_set(x_153, 2, x_17);
lean_ctor_set(x_153, 3, x_152);
lean_ctor_set(x_153, 4, x_151);
lean_ctor_set_uint8(x_153, sizeof(void*)*5, x_3);
x_154 = lean_st_ref_get(x_11, x_146);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_st_ref_take(x_7, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = !lean_is_exclusive(x_157);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_160 = lean_ctor_get(x_157, 3);
x_161 = l_Std_PersistentArray_push___rarg(x_160, x_153);
lean_ctor_set(x_157, 3, x_161);
x_162 = lean_st_ref_set(x_7, x_157, x_158);
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_162, 0);
lean_dec(x_164);
x_165 = lean_box(0);
lean_ctor_set(x_162, 0, x_165);
return x_162;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_162, 1);
lean_inc(x_166);
lean_dec(x_162);
x_167 = lean_box(0);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_169 = lean_ctor_get(x_157, 0);
x_170 = lean_ctor_get(x_157, 1);
x_171 = lean_ctor_get(x_157, 2);
x_172 = lean_ctor_get(x_157, 3);
x_173 = lean_ctor_get(x_157, 4);
x_174 = lean_ctor_get(x_157, 5);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_157);
x_175 = l_Std_PersistentArray_push___rarg(x_172, x_153);
x_176 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_176, 0, x_169);
lean_ctor_set(x_176, 1, x_170);
lean_ctor_set(x_176, 2, x_171);
lean_ctor_set(x_176, 3, x_175);
lean_ctor_set(x_176, 4, x_173);
lean_ctor_set(x_176, 5, x_174);
x_177 = lean_st_ref_set(x_7, x_176, x_158);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_179 = x_177;
} else {
 lean_dec_ref(x_177);
 x_179 = lean_box(0);
}
x_180 = lean_box(0);
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_179;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_178);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_182 = lean_ctor_get(x_17, 0);
lean_inc(x_182);
lean_dec(x_17);
x_183 = lean_ctor_get(x_6, 0);
x_184 = lean_ctor_get(x_6, 1);
x_185 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = l_Lean_FileMap_toPosition(x_184, x_182);
lean_dec(x_182);
lean_inc(x_188);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_190 = lean_ctor_get(x_10, 4);
x_191 = lean_ctor_get(x_10, 5);
lean_inc(x_191);
lean_inc(x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_186);
x_194 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
lean_inc(x_183);
x_195 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_195, 0, x_183);
lean_ctor_set(x_195, 1, x_188);
lean_ctor_set(x_195, 2, x_189);
lean_ctor_set(x_195, 3, x_194);
lean_ctor_set(x_195, 4, x_193);
lean_ctor_set_uint8(x_195, sizeof(void*)*5, x_3);
x_196 = lean_st_ref_get(x_11, x_187);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
x_198 = lean_st_ref_take(x_7, x_197);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = lean_ctor_get(x_199, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_199, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_199, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_199, 3);
lean_inc(x_204);
x_205 = lean_ctor_get(x_199, 4);
lean_inc(x_205);
x_206 = lean_ctor_get(x_199, 5);
lean_inc(x_206);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 lean_ctor_release(x_199, 4);
 lean_ctor_release(x_199, 5);
 x_207 = x_199;
} else {
 lean_dec_ref(x_199);
 x_207 = lean_box(0);
}
x_208 = l_Std_PersistentArray_push___rarg(x_204, x_195);
if (lean_is_scalar(x_207)) {
 x_209 = lean_alloc_ctor(0, 6, 0);
} else {
 x_209 = x_207;
}
lean_ctor_set(x_209, 0, x_201);
lean_ctor_set(x_209, 1, x_202);
lean_ctor_set(x_209, 2, x_203);
lean_ctor_set(x_209, 3, x_208);
lean_ctor_set(x_209, 4, x_205);
lean_ctor_set(x_209, 5, x_206);
x_210 = lean_st_ref_set(x_7, x_209, x_200);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_212 = x_210;
} else {
 lean_dec_ref(x_210);
 x_212 = lean_box(0);
}
x_213 = lean_box(0);
if (lean_is_scalar(x_212)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_212;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_211);
return x_214;
}
}
else
{
lean_object* x_215; uint8_t x_216; 
x_215 = lean_ctor_get(x_17, 0);
lean_inc(x_215);
lean_dec(x_17);
x_216 = !lean_is_exclusive(x_18);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_217 = lean_ctor_get(x_18, 0);
x_218 = lean_ctor_get(x_6, 0);
x_219 = lean_ctor_get(x_6, 1);
x_220 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = l_Lean_FileMap_toPosition(x_219, x_215);
lean_dec(x_215);
x_224 = l_Lean_FileMap_toPosition(x_219, x_217);
lean_dec(x_217);
lean_ctor_set(x_18, 0, x_224);
x_225 = lean_ctor_get(x_10, 4);
x_226 = lean_ctor_get(x_10, 5);
lean_inc(x_226);
lean_inc(x_225);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_221);
x_229 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
lean_inc(x_218);
x_230 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_230, 0, x_218);
lean_ctor_set(x_230, 1, x_223);
lean_ctor_set(x_230, 2, x_18);
lean_ctor_set(x_230, 3, x_229);
lean_ctor_set(x_230, 4, x_228);
lean_ctor_set_uint8(x_230, sizeof(void*)*5, x_3);
x_231 = lean_st_ref_get(x_11, x_222);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec(x_231);
x_233 = lean_st_ref_take(x_7, x_232);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = !lean_is_exclusive(x_234);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_237 = lean_ctor_get(x_234, 3);
x_238 = l_Std_PersistentArray_push___rarg(x_237, x_230);
lean_ctor_set(x_234, 3, x_238);
x_239 = lean_st_ref_set(x_7, x_234, x_235);
x_240 = !lean_is_exclusive(x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_ctor_get(x_239, 0);
lean_dec(x_241);
x_242 = lean_box(0);
lean_ctor_set(x_239, 0, x_242);
return x_239;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_239, 1);
lean_inc(x_243);
lean_dec(x_239);
x_244 = lean_box(0);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_246 = lean_ctor_get(x_234, 0);
x_247 = lean_ctor_get(x_234, 1);
x_248 = lean_ctor_get(x_234, 2);
x_249 = lean_ctor_get(x_234, 3);
x_250 = lean_ctor_get(x_234, 4);
x_251 = lean_ctor_get(x_234, 5);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_234);
x_252 = l_Std_PersistentArray_push___rarg(x_249, x_230);
x_253 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_253, 0, x_246);
lean_ctor_set(x_253, 1, x_247);
lean_ctor_set(x_253, 2, x_248);
lean_ctor_set(x_253, 3, x_252);
lean_ctor_set(x_253, 4, x_250);
lean_ctor_set(x_253, 5, x_251);
x_254 = lean_st_ref_set(x_7, x_253, x_235);
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_256 = x_254;
} else {
 lean_dec_ref(x_254);
 x_256 = lean_box(0);
}
x_257 = lean_box(0);
if (lean_is_scalar(x_256)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_256;
}
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_255);
return x_258;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_259 = lean_ctor_get(x_18, 0);
lean_inc(x_259);
lean_dec(x_18);
x_260 = lean_ctor_get(x_6, 0);
x_261 = lean_ctor_get(x_6, 1);
x_262 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_8, x_9, x_10, x_11, x_12);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = l_Lean_FileMap_toPosition(x_261, x_215);
lean_dec(x_215);
x_266 = l_Lean_FileMap_toPosition(x_261, x_259);
lean_dec(x_259);
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_266);
x_268 = lean_ctor_get(x_10, 4);
x_269 = lean_ctor_get(x_10, 5);
lean_inc(x_269);
lean_inc(x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_263);
x_272 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
lean_inc(x_260);
x_273 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_273, 0, x_260);
lean_ctor_set(x_273, 1, x_265);
lean_ctor_set(x_273, 2, x_267);
lean_ctor_set(x_273, 3, x_272);
lean_ctor_set(x_273, 4, x_271);
lean_ctor_set_uint8(x_273, sizeof(void*)*5, x_3);
x_274 = lean_st_ref_get(x_11, x_264);
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
lean_dec(x_274);
x_276 = lean_st_ref_take(x_7, x_275);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_279 = lean_ctor_get(x_277, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_277, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_277, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_277, 3);
lean_inc(x_282);
x_283 = lean_ctor_get(x_277, 4);
lean_inc(x_283);
x_284 = lean_ctor_get(x_277, 5);
lean_inc(x_284);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 lean_ctor_release(x_277, 2);
 lean_ctor_release(x_277, 3);
 lean_ctor_release(x_277, 4);
 lean_ctor_release(x_277, 5);
 x_285 = x_277;
} else {
 lean_dec_ref(x_277);
 x_285 = lean_box(0);
}
x_286 = l_Std_PersistentArray_push___rarg(x_282, x_273);
if (lean_is_scalar(x_285)) {
 x_287 = lean_alloc_ctor(0, 6, 0);
} else {
 x_287 = x_285;
}
lean_ctor_set(x_287, 0, x_279);
lean_ctor_set(x_287, 1, x_280);
lean_ctor_set(x_287, 2, x_281);
lean_ctor_set(x_287, 3, x_286);
lean_ctor_set(x_287, 4, x_283);
lean_ctor_set(x_287, 5, x_284);
x_288 = lean_st_ref_set(x_7, x_287, x_278);
x_289 = lean_ctor_get(x_288, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_290 = x_288;
} else {
 lean_dec_ref(x_288);
 x_290 = lean_box(0);
}
x_291 = lean_box(0);
if (lean_is_scalar(x_290)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_290;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_289);
return x_292;
}
}
}
}
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 3);
x_13 = l_Lean_Elab_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("internal exception: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = 2;
x_14 = l_Lean_Elab_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(x_11, x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = l_Lean_Elab_isAbortExceptionId(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_st_ref_get(x_9, x_10);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_8, 3);
x_22 = l_Lean_InternalExceptionId_getName(x_16, x_20);
lean_dec(x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
lean_free_object(x_1);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__2;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = 2;
x_31 = l_Lean_Elab_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(x_29, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_io_error_to_string(x_33);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_inc(x_21);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_36);
lean_ctor_set(x_1, 0, x_21);
lean_ctor_set(x_22, 0, x_1);
return x_22;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_22);
x_39 = lean_io_error_to_string(x_37);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_inc(x_21);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_41);
lean_ctor_set(x_1, 0, x_21);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_free_object(x_1);
lean_dec(x_16);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_10);
return x_44;
}
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
lean_dec(x_1);
x_46 = l_Lean_Elab_isAbortExceptionId(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_st_ref_get(x_9, x_10);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_8, 3);
x_50 = l_Lean_InternalExceptionId_getName(x_45, x_48);
lean_dec(x_45);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_53, 0, x_51);
x_54 = l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__2;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = 2;
x_59 = l_Lean_Elab_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(x_57, x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_50, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_50, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_62 = x_50;
} else {
 lean_dec_ref(x_50);
 x_62 = lean_box(0);
}
x_63 = lean_io_error_to_string(x_60);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
lean_inc(x_49);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_49);
lean_ctor_set(x_66, 1, x_65);
if (lean_is_scalar(x_62)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_62;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_61);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_45);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_10);
return x_69;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_closeUsingOrAdmit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Elab_Tactic_focusAndDone___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_17);
lean_dec(x_16);
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
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l_Lean_Elab_admitGoal(x_16, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_Tactic_setGoals(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
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
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Elab_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
static lean_object* _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_saveState___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_SavedState_restore___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__1;
x_2 = l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__3;
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_tryCatch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Elab_Tactic_saveState___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_18 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_apply_10(x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
return x_20;
}
}
}
lean_object* l_Lean_Elab_Tactic_tryCatch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tryCatch___rarg), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_Elab_Tactic_saveState___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
x_19 = l_Lean_Elab_Tactic_SavedState_restore(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_apply_10(x_3, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lambda__1___boxed), 11, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lambda__2), 12, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__1;
x_2 = l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__3;
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_Elab_Tactic_orElse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_Elab_Tactic_saveState___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_Tactic_SavedState_restore(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
return x_19;
}
}
}
lean_object* l_Lean_Elab_Tactic_orElse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_orElse___rarg), 11, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_instOrElseTacticM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_orElse___rarg), 11, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_instOrElseTacticM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_instOrElseTacticM___closed__1;
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_saveTacticInfoForToken(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
x_12 = l_Lean_Syntax_getPos_x3f(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_12);
x_15 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_9, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_5, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 5);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg(x_5, x_6, x_7, x_8, x_9, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_9, x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_get(x_5, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 5);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_9);
lean_inc(x_5);
x_41 = lean_apply_9(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_40);
x_45 = lean_st_ref_get(x_9, x_43);
lean_dec(x_9);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_st_ref_take(x_5, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 5);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_48, 5);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_49, 1);
lean_dec(x_54);
x_55 = l_Std_PersistentArray_push___rarg(x_32, x_44);
lean_ctor_set(x_49, 1, x_55);
x_56 = lean_st_ref_set(x_5, x_48, x_50);
lean_dec(x_5);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
x_59 = lean_box(0);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get_uint8(x_49, sizeof(void*)*2);
x_64 = lean_ctor_get(x_49, 0);
lean_inc(x_64);
lean_dec(x_49);
x_65 = l_Std_PersistentArray_push___rarg(x_32, x_44);
x_66 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*2, x_63);
lean_ctor_set(x_48, 5, x_66);
x_67 = lean_st_ref_set(x_5, x_48, x_50);
lean_dec(x_5);
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
x_70 = lean_box(0);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_72 = lean_ctor_get(x_48, 0);
x_73 = lean_ctor_get(x_48, 1);
x_74 = lean_ctor_get(x_48, 2);
x_75 = lean_ctor_get(x_48, 3);
x_76 = lean_ctor_get(x_48, 4);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_48);
x_77 = lean_ctor_get_uint8(x_49, sizeof(void*)*2);
x_78 = lean_ctor_get(x_49, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_79 = x_49;
} else {
 lean_dec_ref(x_49);
 x_79 = lean_box(0);
}
x_80 = l_Std_PersistentArray_push___rarg(x_32, x_44);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 1);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*2, x_77);
x_82 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_73);
lean_ctor_set(x_82, 2, x_74);
lean_ctor_set(x_82, 3, x_75);
lean_ctor_set(x_82, 4, x_76);
lean_ctor_set(x_82, 5, x_81);
x_83 = lean_st_ref_set(x_5, x_82, x_50);
lean_dec(x_5);
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
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec(x_40);
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_5);
x_88 = !lean_is_exclusive(x_41);
if (x_88 == 0)
{
return x_41;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_41, 0);
x_90 = lean_ctor_get(x_41, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_41);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
}
lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_st_ref_get(x_11, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_7, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 5);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*2);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_apply_9(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg(x_7, x_8, x_9, x_10, x_11, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_7);
x_25 = lean_apply_9(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_11, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_get(x_7, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 5);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_dec(x_8);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_1);
lean_ctor_set(x_36, 2, x_2);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
x_39 = lean_st_ref_get(x_11, x_32);
lean_dec(x_11);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_st_ref_take(x_7, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 5);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_42, 5);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_43, 1);
lean_dec(x_48);
x_49 = l_Std_PersistentArray_push___rarg(x_23, x_38);
lean_ctor_set(x_43, 1, x_49);
x_50 = lean_st_ref_set(x_7, x_42, x_44);
lean_dec(x_7);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_26);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_26);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get_uint8(x_43, sizeof(void*)*2);
x_56 = lean_ctor_get(x_43, 0);
lean_inc(x_56);
lean_dec(x_43);
x_57 = l_Std_PersistentArray_push___rarg(x_23, x_38);
x_58 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_55);
lean_ctor_set(x_42, 5, x_58);
x_59 = lean_st_ref_set(x_7, x_42, x_44);
lean_dec(x_7);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_26);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_63 = lean_ctor_get(x_42, 0);
x_64 = lean_ctor_get(x_42, 1);
x_65 = lean_ctor_get(x_42, 2);
x_66 = lean_ctor_get(x_42, 3);
x_67 = lean_ctor_get(x_42, 4);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_42);
x_68 = lean_ctor_get_uint8(x_43, sizeof(void*)*2);
x_69 = lean_ctor_get(x_43, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_70 = x_43;
} else {
 lean_dec_ref(x_43);
 x_70 = lean_box(0);
}
x_71 = l_Std_PersistentArray_push___rarg(x_23, x_38);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 1);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_68);
x_73 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_73, 0, x_63);
lean_ctor_set(x_73, 1, x_64);
lean_ctor_set(x_73, 2, x_65);
lean_ctor_set(x_73, 3, x_66);
lean_ctor_set(x_73, 4, x_67);
lean_ctor_set(x_73, 5, x_72);
x_74 = lean_st_ref_set(x_7, x_73, x_44);
lean_dec(x_7);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_26);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_78 = lean_ctor_get(x_25, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_25, 1);
lean_inc(x_79);
lean_dec(x_25);
x_80 = lean_st_ref_get(x_11, x_79);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_st_ref_get(x_7, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_83, 5);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_ctor_get(x_8, 1);
lean_inc(x_87);
lean_dec(x_8);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_1);
lean_ctor_set(x_88, 2, x_2);
x_89 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_86);
x_91 = lean_st_ref_get(x_11, x_84);
lean_dec(x_11);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_93 = lean_st_ref_take(x_7, x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 5);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = !lean_is_exclusive(x_94);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_94, 5);
lean_dec(x_98);
x_99 = !lean_is_exclusive(x_95);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_95, 1);
lean_dec(x_100);
x_101 = l_Std_PersistentArray_push___rarg(x_23, x_90);
lean_ctor_set(x_95, 1, x_101);
x_102 = lean_st_ref_set(x_7, x_94, x_96);
lean_dec(x_7);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_102, 0);
lean_dec(x_104);
lean_ctor_set_tag(x_102, 1);
lean_ctor_set(x_102, 0, x_78);
return x_102;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_78);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
else
{
uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_107 = lean_ctor_get_uint8(x_95, sizeof(void*)*2);
x_108 = lean_ctor_get(x_95, 0);
lean_inc(x_108);
lean_dec(x_95);
x_109 = l_Std_PersistentArray_push___rarg(x_23, x_90);
x_110 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_107);
lean_ctor_set(x_94, 5, x_110);
x_111 = lean_st_ref_set(x_7, x_94, x_96);
lean_dec(x_7);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
 lean_ctor_set_tag(x_114, 1);
}
lean_ctor_set(x_114, 0, x_78);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_115 = lean_ctor_get(x_94, 0);
x_116 = lean_ctor_get(x_94, 1);
x_117 = lean_ctor_get(x_94, 2);
x_118 = lean_ctor_get(x_94, 3);
x_119 = lean_ctor_get(x_94, 4);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_94);
x_120 = lean_ctor_get_uint8(x_95, sizeof(void*)*2);
x_121 = lean_ctor_get(x_95, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_122 = x_95;
} else {
 lean_dec_ref(x_95);
 x_122 = lean_box(0);
}
x_123 = l_Std_PersistentArray_push___rarg(x_23, x_90);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 1);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set_uint8(x_124, sizeof(void*)*2, x_120);
x_125 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_125, 0, x_115);
lean_ctor_set(x_125, 1, x_116);
lean_ctor_set(x_125, 2, x_117);
lean_ctor_set(x_125, 3, x_118);
lean_ctor_set(x_125, 4, x_119);
lean_ctor_set(x_125, 5, x_124);
x_126 = lean_st_ref_set(x_7, x_125, x_96);
lean_dec(x_7);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_128 = x_126;
} else {
 lean_dec_ref(x_126);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
 lean_ctor_set_tag(x_129, 1);
}
lean_ctor_set(x_129, 0, x_78);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
}
}
}
lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1___rarg), 12, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_withMacroExpansion___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_6, 3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_6, 3, x_16);
x_17 = lean_apply_9(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
x_24 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 1);
x_25 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 2);
x_26 = lean_ctor_get(x_6, 5);
x_27 = lean_ctor_get(x_6, 6);
x_28 = lean_ctor_get(x_6, 7);
x_29 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_2);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_21);
x_32 = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_19);
lean_ctor_set(x_32, 2, x_20);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set(x_32, 4, x_22);
lean_ctor_set(x_32, 5, x_26);
lean_ctor_set(x_32, 6, x_27);
lean_ctor_set(x_32, 7, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*8, x_23);
lean_ctor_set_uint8(x_32, sizeof(void*)*8 + 1, x_24);
lean_ctor_set_uint8(x_32, sizeof(void*)*8 + 2, x_25);
lean_ctor_set_uint8(x_32, sizeof(void*)*8 + 3, x_29);
x_33 = lean_apply_9(x_3, x_4, x_5, x_32, x_7, x_8, x_9, x_10, x_11, x_12);
return x_33;
}
}
}
lean_object* l_Lean_Elab_Tactic_withMacroExpansion___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_2);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMacroExpansion___rarg___lambda__1), 12, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
x_14 = l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_withMacroExpansion___spec__1___rarg(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
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
lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_adaptExpander___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_st_ref_get(x_11, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_7, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 5);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*2);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_apply_9(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg(x_7, x_8, x_9, x_10, x_11, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_7);
x_25 = lean_apply_9(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_11, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_get(x_7, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 5);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_dec(x_8);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_1);
lean_ctor_set(x_36, 2, x_2);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
x_39 = lean_st_ref_get(x_11, x_32);
lean_dec(x_11);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_st_ref_take(x_7, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 5);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_42, 5);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_43, 1);
lean_dec(x_48);
x_49 = l_Std_PersistentArray_push___rarg(x_23, x_38);
lean_ctor_set(x_43, 1, x_49);
x_50 = lean_st_ref_set(x_7, x_42, x_44);
lean_dec(x_7);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_26);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_26);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get_uint8(x_43, sizeof(void*)*2);
x_56 = lean_ctor_get(x_43, 0);
lean_inc(x_56);
lean_dec(x_43);
x_57 = l_Std_PersistentArray_push___rarg(x_23, x_38);
x_58 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_55);
lean_ctor_set(x_42, 5, x_58);
x_59 = lean_st_ref_set(x_7, x_42, x_44);
lean_dec(x_7);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_26);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_63 = lean_ctor_get(x_42, 0);
x_64 = lean_ctor_get(x_42, 1);
x_65 = lean_ctor_get(x_42, 2);
x_66 = lean_ctor_get(x_42, 3);
x_67 = lean_ctor_get(x_42, 4);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_42);
x_68 = lean_ctor_get_uint8(x_43, sizeof(void*)*2);
x_69 = lean_ctor_get(x_43, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_70 = x_43;
} else {
 lean_dec_ref(x_43);
 x_70 = lean_box(0);
}
x_71 = l_Std_PersistentArray_push___rarg(x_23, x_38);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 1);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_68);
x_73 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_73, 0, x_63);
lean_ctor_set(x_73, 1, x_64);
lean_ctor_set(x_73, 2, x_65);
lean_ctor_set(x_73, 3, x_66);
lean_ctor_set(x_73, 4, x_67);
lean_ctor_set(x_73, 5, x_72);
x_74 = lean_st_ref_set(x_7, x_73, x_44);
lean_dec(x_7);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_26);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_78 = lean_ctor_get(x_25, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_25, 1);
lean_inc(x_79);
lean_dec(x_25);
x_80 = lean_st_ref_get(x_11, x_79);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_st_ref_get(x_7, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_83, 5);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_ctor_get(x_8, 1);
lean_inc(x_87);
lean_dec(x_8);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_1);
lean_ctor_set(x_88, 2, x_2);
x_89 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_86);
x_91 = lean_st_ref_get(x_11, x_84);
lean_dec(x_11);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_93 = lean_st_ref_take(x_7, x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 5);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = !lean_is_exclusive(x_94);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_94, 5);
lean_dec(x_98);
x_99 = !lean_is_exclusive(x_95);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_100 = lean_ctor_get(x_95, 1);
lean_dec(x_100);
x_101 = l_Std_PersistentArray_push___rarg(x_23, x_90);
lean_ctor_set(x_95, 1, x_101);
x_102 = lean_st_ref_set(x_7, x_94, x_96);
lean_dec(x_7);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_102, 0);
lean_dec(x_104);
lean_ctor_set_tag(x_102, 1);
lean_ctor_set(x_102, 0, x_78);
return x_102;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_78);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
else
{
uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_107 = lean_ctor_get_uint8(x_95, sizeof(void*)*2);
x_108 = lean_ctor_get(x_95, 0);
lean_inc(x_108);
lean_dec(x_95);
x_109 = l_Std_PersistentArray_push___rarg(x_23, x_90);
x_110 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_107);
lean_ctor_set(x_94, 5, x_110);
x_111 = lean_st_ref_set(x_7, x_94, x_96);
lean_dec(x_7);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
 lean_ctor_set_tag(x_114, 1);
}
lean_ctor_set(x_114, 0, x_78);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_115 = lean_ctor_get(x_94, 0);
x_116 = lean_ctor_get(x_94, 1);
x_117 = lean_ctor_get(x_94, 2);
x_118 = lean_ctor_get(x_94, 3);
x_119 = lean_ctor_get(x_94, 4);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_94);
x_120 = lean_ctor_get_uint8(x_95, sizeof(void*)*2);
x_121 = lean_ctor_get(x_95, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_122 = x_95;
} else {
 lean_dec_ref(x_95);
 x_122 = lean_box(0);
}
x_123 = l_Std_PersistentArray_push___rarg(x_23, x_90);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 1);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set_uint8(x_124, sizeof(void*)*2, x_120);
x_125 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_125, 0, x_115);
lean_ctor_set(x_125, 1, x_116);
lean_ctor_set(x_125, 2, x_117);
lean_ctor_set(x_125, 3, x_118);
lean_ctor_set(x_125, 4, x_119);
lean_ctor_set(x_125, 5, x_124);
x_126 = lean_st_ref_set(x_7, x_125, x_96);
lean_dec(x_7);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_128 = x_126;
} else {
 lean_dec_ref(x_126);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
 lean_ctor_set_tag(x_129, 1);
}
lean_ctor_set(x_129, 0, x_78);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_adaptExpander___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_5, 3, x_15);
x_16 = l_Lean_Elab_Tactic_evalTacticAux(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_ctor_get(x_5, 2);
x_20 = lean_ctor_get(x_5, 3);
x_21 = lean_ctor_get(x_5, 4);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*8);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 1);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 2);
x_25 = lean_ctor_get(x_5, 5);
x_26 = lean_ctor_get(x_5, 6);
x_27 = lean_ctor_get(x_5, 7);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
lean_inc(x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_2);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_20);
x_31 = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 2, x_19);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_31, 4, x_21);
lean_ctor_set(x_31, 5, x_25);
lean_ctor_set(x_31, 6, x_26);
lean_ctor_set(x_31, 7, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*8, x_22);
lean_ctor_set_uint8(x_31, sizeof(void*)*8 + 1, x_23);
lean_ctor_set_uint8(x_31, sizeof(void*)*8 + 2, x_24);
lean_ctor_set_uint8(x_31, sizeof(void*)*8 + 3, x_28);
x_32 = l_Lean_Elab_Tactic_evalTacticAux(x_2, x_3, x_4, x_31, x_6, x_7, x_8, x_9, x_10, x_11);
return x_32;
}
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_adaptExpander___lambda__1___boxed), 11, 2);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_adaptExpander___spec__1(x_2, x_13, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
lean_object* l_Lean_Elab_Tactic_adaptExpander___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_adaptExpander___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_appendGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_List_append___rarg(x_14, x_1);
x_17 = lean_st_ref_set(x_3, x_16, x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
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
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Tactic_getGoals___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_st_ref_get(x_9, x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_take(x_3, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_List_append___rarg(x_1, x_16);
x_22 = lean_st_ref_set(x_3, x_21, x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_replaceMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Elab_Tactic_getMainGoal_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Elab_Tactic_getMainGoal_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getMainGoal_loop_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getMainGoal_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = l_Lean_Meta_isExprMVarAssigned(x_13, x_6, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_13);
x_19 = l_Lean_Elab_Tactic_setGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_13);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_free_object(x_1);
lean_dec(x_13);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_1 = x_14;
x_10 = x_24;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
x_28 = l_Lean_Meta_isExprMVarAssigned(x_26, x_6, x_7, x_8, x_9, x_10);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
lean_inc(x_26);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_27);
x_33 = l_Lean_Elab_Tactic_setGoals(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
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
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
else
{
lean_object* x_37; 
lean_dec(x_26);
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec(x_28);
x_1 = x_27;
x_10 = x_37;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_getMainGoal_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Elab_Tactic_getGoals___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Tactic_getMainGoal_loop(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_13;
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
lean_object* l_Lean_Elab_Tactic_getMainDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_getMVarDecl(x_11, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
uint8_t x_14; 
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
lean_object* l_Lean_Elab_Tactic_getMainDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Elab_Tactic_getMainTag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
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
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
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
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_instantiateMVars(x_13, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_getMainTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainTarget(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___rarg(x_1, x_12, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainContext___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Tactic_withMainContext___spec__1___rarg(x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_withMainContext(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalTacticAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = l_Lean_Elab_Tactic_getGoals___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_Tactic_setGoals(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Elab_Tactic_evalTacticAux(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Elab_Tactic_pruneSolvedGoals(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Tactic_getGoals___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Tactic_setGoals(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_24);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_dec(x_19);
x_33 = l_Lean_Elab_Tactic_setGoals(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalTacticAt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalTacticAt(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tactic failed, resulting expression contains metavariables");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_14 = l_Lean_Meta_getMVars(x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_15, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = l_Lean_Expr_hasExprMVar(x_12);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = lean_box(0);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_18);
x_24 = l_Lean_indentExpr(x_12);
x_25 = l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_29;
}
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
x_31 = l_Lean_Expr_hasExprMVar(x_12);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = l_Lean_indentExpr(x_12);
x_35 = l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2(x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_18, 0);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_18);
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
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_14);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_11);
if (x_48 == 0)
{
return x_11;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_11, 0);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_11);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_ensureHasNoMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_ensureHasNoMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_closeMainGoal___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_assignExprMVar(x_13, x_1, x_7, x_8, x_9, x_10, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Tactic_replaceMainGoal(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_closeMainGoal(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_2 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_Elab_Tactic_closeMainGoal___lambda__1(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
else
{
lean_object* x_14; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_14 = l_Lean_Elab_Tactic_ensureHasNoMVars(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_closeMainGoal___lambda__1(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
}
}
lean_object* l_Lean_Elab_Tactic_closeMainGoal___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_closeMainGoal___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_Elab_Tactic_closeMainGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_Tactic_closeMainGoal(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaMAtMain___rarg___lambda__1___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
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
lean_object* l_Lean_Elab_Tactic_liftMetaMAtMain___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaMAtMain___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux_match__1___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_Elab_Tactic_replaceMainGoal(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_17);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
}
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
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
lean_object* l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaTacticAux___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = lean_apply_6(x_1, x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_replaceMainGoal(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
}
lean_object* l_Lean_Elab_Tactic_liftMetaTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_liftMetaTactic___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("done");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalDone");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__5() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_tryTactic_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Elab_Tactic_saveState___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_23 = l_Lean_Elab_Tactic_SavedState_restore(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
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
lean_object* l_Lean_Elab_Tactic_tryTactic_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tryTactic_x3f___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_tryTactic___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Elab_Tactic_saveState___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_24 = l_Lean_Elab_Tactic_SavedState_restore(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
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
lean_object* l_Lean_Elab_Tactic_tryTactic(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tryTactic___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_tagUntaggedGoals_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_16 = l_Lean_MetavarContext_isAnonymousMVar(x_1, x_14);
if (x_16 == 0)
{
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_2 = x_15;
x_3 = x_19;
goto _start;
}
}
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_11 = l_Lean_MetavarContext_isAnonymousMVar(x_9, x_6);
if (x_11 == 0)
{
lean_dec(x_6);
x_4 = x_7;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_free_object(x_5);
x_13 = l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___closed__1;
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_10);
lean_inc(x_2);
x_16 = lean_name_append_index_after(x_2, x_10);
x_17 = l_Lean_Name_append(x_1, x_16);
x_18 = l_Lean_MetavarContext_renameMVar(x_9, x_6, x_17);
x_19 = lean_box(0);
x_20 = lean_apply_3(x_13, x_18, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_4 = x_7;
x_5 = x_22;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_1);
x_24 = l_Lean_MetavarContext_renameMVar(x_9, x_6, x_1);
x_25 = lean_box(0);
x_26 = lean_apply_3(x_13, x_24, x_10, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_4 = x_7;
x_5 = x_28;
goto _start;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_5);
lean_inc(x_30);
x_32 = l_Lean_MetavarContext_isAnonymousMVar(x_30, x_6);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_6);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
x_4 = x_7;
x_5 = x_33;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___closed__1;
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_dec_eq(x_3, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_inc(x_31);
lean_inc(x_2);
x_38 = lean_name_append_index_after(x_2, x_31);
x_39 = l_Lean_Name_append(x_1, x_38);
x_40 = l_Lean_MetavarContext_renameMVar(x_30, x_6, x_39);
x_41 = lean_box(0);
x_42 = lean_apply_3(x_35, x_40, x_31, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
return x_43;
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_4 = x_7;
x_5 = x_44;
goto _start;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc(x_1);
x_46 = l_Lean_MetavarContext_renameMVar(x_30, x_6, x_1);
x_47 = lean_box(0);
x_48 = lean_apply_3(x_35, x_46, x_31, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
return x_49;
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_4 = x_7;
x_5 = x_50;
goto _start;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_tagUntaggedGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_13 = lean_st_ref_get(x_11, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_9, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(x_18, x_3, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_11, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_take(x_9, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2(x_1, x_2, x_21, x_3, x_31);
lean_dec(x_21);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
lean_ctor_set(x_26, 0, x_33);
x_34 = lean_st_ref_set(x_9, x_26, x_27);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_41 = lean_ctor_get(x_26, 0);
x_42 = lean_ctor_get(x_26, 1);
x_43 = lean_ctor_get(x_26, 2);
x_44 = lean_ctor_get(x_26, 3);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_26);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2(x_1, x_2, x_21, x_3, x_46);
lean_dec(x_21);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_42);
lean_ctor_set(x_49, 2, x_43);
lean_ctor_set(x_49, 3, x_44);
x_50 = lean_st_ref_set(x_9, x_49, x_27);
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
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2(x_1, x_2, x_3, x_4, x_5);
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
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalSeq1___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_nat_dec_le(x_15, x_4);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_3, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_3, x_19);
lean_dec(x_3);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_mod(x_4, x_21);
x_23 = lean_nat_dec_eq(x_22, x_17);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_instInhabitedSyntax;
x_25 = lean_array_get(x_24, x_1, x_4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_26 = l_Lean_Elab_Tactic_saveTacticInfoForToken(x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_2, 2);
x_29 = lean_nat_add(x_4, x_28);
lean_dec(x_4);
x_30 = lean_box(0);
x_3 = x_20;
x_4 = x_29;
x_5 = x_30;
x_14 = x_27;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = l_Lean_instInhabitedSyntax;
x_37 = lean_array_get(x_36, x_1, x_4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_38 = l_Lean_Elab_Tactic_evalTacticAux(x_37, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_2, 2);
x_41 = lean_nat_add(x_4, x_40);
lean_dec(x_4);
x_42 = lean_box(0);
x_3 = x_20;
x_4 = x_41;
x_5 = x_42;
x_14 = x_39;
goto _start;
}
else
{
uint8_t x_44; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
return x_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_38, 0);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_14);
return x_48;
}
}
else
{
lean_object* x_49; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_5);
lean_ctor_set(x_49, 1, x_14);
return x_49;
}
}
}
lean_object* l_Lean_Elab_Tactic_evalSeq1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(1u);
lean_inc(x_14);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_box(0);
x_18 = l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalSeq1___spec__1(x_13, x_16, x_14, x_11, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_16);
lean_dec(x_13);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
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
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalSeq1___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalSeq1___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("seq1");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalSeq1");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__5() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_evalParen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Elab_Tactic_evalTacticAux(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_evalParen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalParen(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("paren");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalParen");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__5() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalManyTacticOptSemi___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_2 == x_3;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_15 = lean_array_uget(x_1, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_15, x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Elab_Tactic_evalTacticAux(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Syntax_getArg(x_15, x_20);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Lean_Elab_Tactic_saveTacticInfoForToken(x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
x_26 = x_2 + x_25;
x_2 = x_26;
x_4 = x_23;
x_13 = x_24;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
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
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
return x_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_13);
return x_36;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalManyTacticOptSemi(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_Syntax_getArgs(x_1);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
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
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_12, x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalManyTacticOptSemi___spec__1(x_11, x_20, x_21, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
return x_23;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalManyTacticOptSemi___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalManyTacticOptSemi___spec__1(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalManyTacticOptSemi___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalManyTacticOptSemi(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_evalTacticSeq1Indented(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalManyTacticOptSemi(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
return x_13;
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticSeq1Indented");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalTacticSeq1Indented");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__5() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_evalTacticSeqBracketed___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_6, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 5);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalManyTacticOptSemi(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg(x_6, x_7, x_8, x_9, x_10, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_10, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_get(x_6, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 5);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_33 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_32);
x_37 = lean_st_ref_get(x_10, x_35);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_st_ref_take(x_6, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 5);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_40, 5);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_41, 1);
lean_dec(x_46);
x_47 = l_Std_PersistentArray_push___rarg(x_24, x_36);
lean_ctor_set(x_41, 1, x_47);
x_48 = lean_st_ref_set(x_6, x_40, x_42);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_unsigned_to_nat(1u);
x_51 = l_Lean_Syntax_getArg(x_1, x_50);
x_52 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalManyTacticOptSemi(x_51, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_49);
lean_dec(x_51);
return x_52;
}
else
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get_uint8(x_41, sizeof(void*)*2);
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
lean_dec(x_41);
x_55 = l_Std_PersistentArray_push___rarg(x_24, x_36);
x_56 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_53);
lean_ctor_set(x_40, 5, x_56);
x_57 = lean_st_ref_set(x_6, x_40, x_42);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_unsigned_to_nat(1u);
x_60 = l_Lean_Syntax_getArg(x_1, x_59);
x_61 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalManyTacticOptSemi(x_60, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
lean_dec(x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_62 = lean_ctor_get(x_40, 0);
x_63 = lean_ctor_get(x_40, 1);
x_64 = lean_ctor_get(x_40, 2);
x_65 = lean_ctor_get(x_40, 3);
x_66 = lean_ctor_get(x_40, 4);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_40);
x_67 = lean_ctor_get_uint8(x_41, sizeof(void*)*2);
x_68 = lean_ctor_get(x_41, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_69 = x_41;
} else {
 lean_dec_ref(x_41);
 x_69 = lean_box(0);
}
x_70 = l_Std_PersistentArray_push___rarg(x_24, x_36);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 1);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_67);
x_72 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_63);
lean_ctor_set(x_72, 2, x_64);
lean_ctor_set(x_72, 3, x_65);
lean_ctor_set(x_72, 4, x_66);
lean_ctor_set(x_72, 5, x_71);
x_73 = lean_st_ref_set(x_6, x_72, x_42);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_unsigned_to_nat(1u);
x_76 = l_Lean_Syntax_getArg(x_1, x_75);
x_77 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalManyTacticOptSemi(x_76, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_74);
lean_dec(x_76);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_32);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_33);
if (x_78 == 0)
{
return x_33;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_33, 0);
x_80 = lean_ctor_get(x_33, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_33);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalTacticSeqBracketed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTacticSeqBracketed___lambda__1___boxed), 11, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_14);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 3);
x_21 = l_Lean_replaceRef(x_17, x_20);
lean_dec(x_20);
lean_dec(x_17);
lean_ctor_set(x_8, 3, x_21);
x_22 = l_Lean_Elab_Tactic_closeUsingOrAdmit(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
x_25 = lean_ctor_get(x_8, 2);
x_26 = lean_ctor_get(x_8, 3);
x_27 = lean_ctor_get(x_8, 4);
x_28 = lean_ctor_get(x_8, 5);
x_29 = lean_ctor_get(x_8, 6);
x_30 = lean_ctor_get(x_8, 7);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_31 = l_Lean_replaceRef(x_17, x_26);
lean_dec(x_26);
lean_dec(x_17);
x_32 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set(x_32, 4, x_27);
lean_ctor_set(x_32, 5, x_28);
lean_ctor_set(x_32, 6, x_29);
lean_ctor_set(x_32, 7, x_30);
x_33 = l_Lean_Elab_Tactic_closeUsingOrAdmit(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_32, x_9, x_15);
return x_33;
}
}
}
lean_object* l_Lean_Elab_Tactic_evalTacticSeqBracketed___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalTacticSeqBracketed___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticSeqBracketed");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalTacticSeqBracketed");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTacticSeqBracketed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_evalFocus___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_6, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 5);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = l_Lean_Elab_Tactic_evalTacticAux(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg(x_6, x_7, x_8, x_9, x_10, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_10, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_get(x_6, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 5);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_33 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_32);
x_37 = lean_st_ref_get(x_10, x_35);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_st_ref_take(x_6, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 5);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_40, 5);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_41, 1);
lean_dec(x_46);
x_47 = l_Std_PersistentArray_push___rarg(x_24, x_36);
lean_ctor_set(x_41, 1, x_47);
x_48 = lean_st_ref_set(x_6, x_40, x_42);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_unsigned_to_nat(1u);
x_51 = l_Lean_Syntax_getArg(x_1, x_50);
x_52 = l_Lean_Elab_Tactic_evalTacticAux(x_51, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_49);
lean_dec(x_3);
return x_52;
}
else
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get_uint8(x_41, sizeof(void*)*2);
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
lean_dec(x_41);
x_55 = l_Std_PersistentArray_push___rarg(x_24, x_36);
x_56 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_53);
lean_ctor_set(x_40, 5, x_56);
x_57 = lean_st_ref_set(x_6, x_40, x_42);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_unsigned_to_nat(1u);
x_60 = l_Lean_Syntax_getArg(x_1, x_59);
x_61 = l_Lean_Elab_Tactic_evalTacticAux(x_60, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
lean_dec(x_3);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_62 = lean_ctor_get(x_40, 0);
x_63 = lean_ctor_get(x_40, 1);
x_64 = lean_ctor_get(x_40, 2);
x_65 = lean_ctor_get(x_40, 3);
x_66 = lean_ctor_get(x_40, 4);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_40);
x_67 = lean_ctor_get_uint8(x_41, sizeof(void*)*2);
x_68 = lean_ctor_get(x_41, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_69 = x_41;
} else {
 lean_dec_ref(x_41);
 x_69 = lean_box(0);
}
x_70 = l_Std_PersistentArray_push___rarg(x_24, x_36);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 1);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_67);
x_72 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_63);
lean_ctor_set(x_72, 2, x_64);
lean_ctor_set(x_72, 3, x_65);
lean_ctor_set(x_72, 4, x_66);
lean_ctor_set(x_72, 5, x_71);
x_73 = lean_st_ref_set(x_6, x_72, x_42);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_unsigned_to_nat(1u);
x_76 = l_Lean_Syntax_getArg(x_1, x_75);
x_77 = l_Lean_Elab_Tactic_evalTacticAux(x_76, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_74);
lean_dec(x_3);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_32);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_33);
if (x_78 == 0)
{
return x_33;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_33, 0);
x_80 = lean_ctor_get(x_33, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_33);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalFocus(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Elab_Tactic_mkInitialTacticInfo(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalFocus___lambda__1___boxed), 11, 2);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_14);
x_17 = l_Lean_Elab_Tactic_focus___rarg(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_17;
}
}
lean_object* l_Lean_Elab_Tactic_evalFocus___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalFocus___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("focus");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalFocus");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalFocus), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFocus(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getOptRotation(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_isNone(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
x_5 = l_Lean_Syntax_toNat(x_4);
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(1u);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getOptRotation___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getOptRotation(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalRotateLeft(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getOptRotation(x_12);
lean_dec(x_12);
x_14 = l_Lean_Elab_Tactic_getGoals___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_List_rotateLeft___rarg(x_15, x_13);
lean_dec(x_13);
x_18 = l_Lean_Elab_Tactic_setGoals(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_18;
}
}
lean_object* l_Lean_Elab_Tactic_evalRotateLeft___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalRotateLeft(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rotateLeft");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalRotateLeft");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRotateLeft___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_evalRotateRight(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getOptRotation(x_12);
lean_dec(x_12);
x_14 = l_Lean_Elab_Tactic_getGoals___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_List_rotateRight___rarg(x_15, x_13);
lean_dec(x_13);
x_18 = l_Lean_Elab_Tactic_setGoals(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_18;
}
}
lean_object* l_Lean_Elab_Tactic_evalRotateRight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalRotateRight(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rotateRight");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalRotateRight");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRotateRight___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRotateRight(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_3 < x_2;
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_4);
x_16 = lean_array_uget(x_1, x_3);
x_17 = lean_st_ref_take(x_12, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = l_Lean_ScopedEnvExtension_pushScope___rarg(x_16, x_21);
lean_dec(x_16);
lean_ctor_set(x_18, 0, x_22);
x_23 = lean_st_ref_set(x_12, x_18, x_19);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = 1;
x_26 = x_3 + x_25;
x_27 = lean_box(0);
x_3 = x_26;
x_4 = x_27;
x_13 = x_24;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
x_31 = lean_ctor_get(x_18, 2);
x_32 = lean_ctor_get(x_18, 3);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_33 = l_Lean_ScopedEnvExtension_pushScope___rarg(x_16, x_29);
lean_dec(x_16);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_31);
lean_ctor_set(x_34, 3, x_32);
x_35 = lean_st_ref_set(x_12, x_34, x_19);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = 1;
x_38 = x_3 + x_37;
x_39 = lean_box(0);
x_3 = x_38;
x_4 = x_39;
x_13 = x_36;
goto _start;
}
}
}
}
lean_object* l_Lean_pushScope___at_Lean_Elab_Tactic_evalOpen___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_scopedEnvExtensionsRef;
x_13 = lean_st_ref_get(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_14);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = lean_box(0);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__2(x_14, x_17, x_18, x_19, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_14);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalOpen___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 3);
x_13 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_7, x_8, x_9, x_10, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
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
lean_inc(x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
static lean_object* _init_l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown namespace '");
return x_1;
}
}
static lean_object* _init_l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_10, x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_2, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_10, x_20);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_get(x_2, x_23);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_1);
x_29 = l_Lean_ResolveName_resolveNamespace_x3f(x_15, x_21, x_28, x_1);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_15);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_24);
x_30 = 1;
x_31 = l_Lean_Name_toString(x_1, x_30);
x_32 = l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_throwError___at_Lean_Elab_Tactic_evalOpen___spec__6(x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_1);
x_39 = lean_ctor_get(x_29, 0);
lean_inc(x_39);
lean_dec(x_29);
lean_ctor_set(x_24, 0, x_39);
return x_24;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_1);
x_43 = l_Lean_ResolveName_resolveNamespace_x3f(x_15, x_21, x_42, x_1);
lean_dec(x_42);
lean_dec(x_21);
lean_dec(x_15);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = 1;
x_45 = l_Lean_Name_toString(x_1, x_44);
x_46 = l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5___closed__1;
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5___closed__2;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Lean_throwError___at_Lean_Elab_Tactic_evalOpen___spec__6(x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_41);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_53 = lean_ctor_get(x_43, 0);
lean_inc(x_53);
lean_dec(x_43);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_41);
return x_54;
}
}
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalOpen___spec__9(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_295; uint8_t x_296; 
x_295 = 2;
x_296 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_102_(x_3, x_295);
if (x_296 == 0)
{
lean_object* x_297; 
x_297 = lean_box(0);
x_14 = x_297;
goto block_294;
}
else
{
uint8_t x_298; 
lean_inc(x_2);
x_298 = l_Lean_MessageData_hasSyntheticSorry(x_2);
if (x_298 == 0)
{
lean_object* x_299; 
x_299 = lean_box(0);
x_14 = x_299;
goto block_294;
}
else
{
lean_object* x_300; lean_object* x_301; 
lean_dec(x_2);
x_300 = lean_box(0);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_13);
return x_301;
}
}
block_294:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
x_15 = lean_ctor_get(x_11, 3);
x_16 = l_Lean_replaceRef(x_1, x_15);
x_17 = 0;
x_18 = l_Lean_Syntax_getPos_x3f(x_16, x_17);
x_19 = l_Lean_Syntax_getTailPos_x3f(x_16, x_17);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
x_22 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_9, x_10, x_11, x_12, x_13);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_FileMap_toPosition(x_21, x_25);
lean_inc(x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_ctor_get(x_11, 4);
x_29 = lean_ctor_get(x_11, 5);
lean_inc(x_29);
lean_inc(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
x_32 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
lean_inc(x_20);
x_33 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_27);
lean_ctor_set(x_33, 3, x_32);
lean_ctor_set(x_33, 4, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*5, x_3);
x_34 = lean_st_ref_get(x_12, x_24);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_take(x_8, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_37, 3);
x_41 = l_Std_PersistentArray_push___rarg(x_40, x_33);
lean_ctor_set(x_37, 3, x_41);
x_42 = lean_st_ref_set(x_8, x_37, x_38);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_49 = lean_ctor_get(x_37, 0);
x_50 = lean_ctor_get(x_37, 1);
x_51 = lean_ctor_get(x_37, 2);
x_52 = lean_ctor_get(x_37, 3);
x_53 = lean_ctor_get(x_37, 4);
x_54 = lean_ctor_get(x_37, 5);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_37);
x_55 = l_Std_PersistentArray_push___rarg(x_52, x_33);
x_56 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_50);
lean_ctor_set(x_56, 2, x_51);
lean_ctor_set(x_56, 3, x_55);
lean_ctor_set(x_56, 4, x_53);
lean_ctor_set(x_56, 5, x_54);
x_57 = lean_st_ref_set(x_8, x_56, x_38);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_19);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_63 = lean_ctor_get(x_19, 0);
x_64 = lean_ctor_get(x_7, 0);
x_65 = lean_ctor_get(x_7, 1);
x_66 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_9, x_10, x_11, x_12, x_13);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unsigned_to_nat(0u);
x_70 = l_Lean_FileMap_toPosition(x_65, x_69);
x_71 = l_Lean_FileMap_toPosition(x_65, x_63);
lean_dec(x_63);
lean_ctor_set(x_19, 0, x_71);
x_72 = lean_ctor_get(x_11, 4);
x_73 = lean_ctor_get(x_11, 5);
lean_inc(x_73);
lean_inc(x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_67);
x_76 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
lean_inc(x_64);
x_77 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_70);
lean_ctor_set(x_77, 2, x_19);
lean_ctor_set(x_77, 3, x_76);
lean_ctor_set(x_77, 4, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*5, x_3);
x_78 = lean_st_ref_get(x_12, x_68);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_st_ref_take(x_8, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_81, 3);
x_85 = l_Std_PersistentArray_push___rarg(x_84, x_77);
lean_ctor_set(x_81, 3, x_85);
x_86 = lean_st_ref_set(x_8, x_81, x_82);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
x_89 = lean_box(0);
lean_ctor_set(x_86, 0, x_89);
return x_86;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec(x_86);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_93 = lean_ctor_get(x_81, 0);
x_94 = lean_ctor_get(x_81, 1);
x_95 = lean_ctor_get(x_81, 2);
x_96 = lean_ctor_get(x_81, 3);
x_97 = lean_ctor_get(x_81, 4);
x_98 = lean_ctor_get(x_81, 5);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_81);
x_99 = l_Std_PersistentArray_push___rarg(x_96, x_77);
x_100 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_100, 0, x_93);
lean_ctor_set(x_100, 1, x_94);
lean_ctor_set(x_100, 2, x_95);
lean_ctor_set(x_100, 3, x_99);
lean_ctor_set(x_100, 4, x_97);
lean_ctor_set(x_100, 5, x_98);
x_101 = lean_st_ref_set(x_8, x_100, x_82);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = lean_box(0);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_106 = lean_ctor_get(x_19, 0);
lean_inc(x_106);
lean_dec(x_19);
x_107 = lean_ctor_get(x_7, 0);
x_108 = lean_ctor_get(x_7, 1);
x_109 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_9, x_10, x_11, x_12, x_13);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_unsigned_to_nat(0u);
x_113 = l_Lean_FileMap_toPosition(x_108, x_112);
x_114 = l_Lean_FileMap_toPosition(x_108, x_106);
lean_dec(x_106);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_ctor_get(x_11, 4);
x_117 = lean_ctor_get(x_11, 5);
lean_inc(x_117);
lean_inc(x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_110);
x_120 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
lean_inc(x_107);
x_121 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_121, 0, x_107);
lean_ctor_set(x_121, 1, x_113);
lean_ctor_set(x_121, 2, x_115);
lean_ctor_set(x_121, 3, x_120);
lean_ctor_set(x_121, 4, x_119);
lean_ctor_set_uint8(x_121, sizeof(void*)*5, x_3);
x_122 = lean_st_ref_get(x_12, x_111);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_124 = lean_st_ref_take(x_8, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_125, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_125, 3);
lean_inc(x_130);
x_131 = lean_ctor_get(x_125, 4);
lean_inc(x_131);
x_132 = lean_ctor_get(x_125, 5);
lean_inc(x_132);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 lean_ctor_release(x_125, 3);
 lean_ctor_release(x_125, 4);
 lean_ctor_release(x_125, 5);
 x_133 = x_125;
} else {
 lean_dec_ref(x_125);
 x_133 = lean_box(0);
}
x_134 = l_Std_PersistentArray_push___rarg(x_130, x_121);
if (lean_is_scalar(x_133)) {
 x_135 = lean_alloc_ctor(0, 6, 0);
} else {
 x_135 = x_133;
}
lean_ctor_set(x_135, 0, x_127);
lean_ctor_set(x_135, 1, x_128);
lean_ctor_set(x_135, 2, x_129);
lean_ctor_set(x_135, 3, x_134);
lean_ctor_set(x_135, 4, x_131);
lean_ctor_set(x_135, 5, x_132);
x_136 = lean_st_ref_set(x_8, x_135, x_126);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
x_139 = lean_box(0);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
return x_140;
}
}
}
else
{
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_18);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_142 = lean_ctor_get(x_18, 0);
x_143 = lean_ctor_get(x_7, 0);
x_144 = lean_ctor_get(x_7, 1);
x_145 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_9, x_10, x_11, x_12, x_13);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = l_Lean_FileMap_toPosition(x_144, x_142);
lean_dec(x_142);
lean_inc(x_148);
lean_ctor_set(x_18, 0, x_148);
x_149 = lean_ctor_get(x_11, 4);
x_150 = lean_ctor_get(x_11, 5);
lean_inc(x_150);
lean_inc(x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_146);
x_153 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
lean_inc(x_143);
x_154 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_154, 0, x_143);
lean_ctor_set(x_154, 1, x_148);
lean_ctor_set(x_154, 2, x_18);
lean_ctor_set(x_154, 3, x_153);
lean_ctor_set(x_154, 4, x_152);
lean_ctor_set_uint8(x_154, sizeof(void*)*5, x_3);
x_155 = lean_st_ref_get(x_12, x_147);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_157 = lean_st_ref_take(x_8, x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = !lean_is_exclusive(x_158);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_161 = lean_ctor_get(x_158, 3);
x_162 = l_Std_PersistentArray_push___rarg(x_161, x_154);
lean_ctor_set(x_158, 3, x_162);
x_163 = lean_st_ref_set(x_8, x_158, x_159);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_163, 0);
lean_dec(x_165);
x_166 = lean_box(0);
lean_ctor_set(x_163, 0, x_166);
return x_163;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_163, 1);
lean_inc(x_167);
lean_dec(x_163);
x_168 = lean_box(0);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_170 = lean_ctor_get(x_158, 0);
x_171 = lean_ctor_get(x_158, 1);
x_172 = lean_ctor_get(x_158, 2);
x_173 = lean_ctor_get(x_158, 3);
x_174 = lean_ctor_get(x_158, 4);
x_175 = lean_ctor_get(x_158, 5);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_158);
x_176 = l_Std_PersistentArray_push___rarg(x_173, x_154);
x_177 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_177, 0, x_170);
lean_ctor_set(x_177, 1, x_171);
lean_ctor_set(x_177, 2, x_172);
lean_ctor_set(x_177, 3, x_176);
lean_ctor_set(x_177, 4, x_174);
lean_ctor_set(x_177, 5, x_175);
x_178 = lean_st_ref_set(x_8, x_177, x_159);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_180 = x_178;
} else {
 lean_dec_ref(x_178);
 x_180 = lean_box(0);
}
x_181 = lean_box(0);
if (lean_is_scalar(x_180)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_180;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_179);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_183 = lean_ctor_get(x_18, 0);
lean_inc(x_183);
lean_dec(x_18);
x_184 = lean_ctor_get(x_7, 0);
x_185 = lean_ctor_get(x_7, 1);
x_186 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_9, x_10, x_11, x_12, x_13);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = l_Lean_FileMap_toPosition(x_185, x_183);
lean_dec(x_183);
lean_inc(x_189);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_189);
x_191 = lean_ctor_get(x_11, 4);
x_192 = lean_ctor_get(x_11, 5);
lean_inc(x_192);
lean_inc(x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_187);
x_195 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
lean_inc(x_184);
x_196 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_196, 0, x_184);
lean_ctor_set(x_196, 1, x_189);
lean_ctor_set(x_196, 2, x_190);
lean_ctor_set(x_196, 3, x_195);
lean_ctor_set(x_196, 4, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*5, x_3);
x_197 = lean_st_ref_get(x_12, x_188);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
x_199 = lean_st_ref_take(x_8, x_198);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = lean_ctor_get(x_200, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_200, 2);
lean_inc(x_204);
x_205 = lean_ctor_get(x_200, 3);
lean_inc(x_205);
x_206 = lean_ctor_get(x_200, 4);
lean_inc(x_206);
x_207 = lean_ctor_get(x_200, 5);
lean_inc(x_207);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 lean_ctor_release(x_200, 3);
 lean_ctor_release(x_200, 4);
 lean_ctor_release(x_200, 5);
 x_208 = x_200;
} else {
 lean_dec_ref(x_200);
 x_208 = lean_box(0);
}
x_209 = l_Std_PersistentArray_push___rarg(x_205, x_196);
if (lean_is_scalar(x_208)) {
 x_210 = lean_alloc_ctor(0, 6, 0);
} else {
 x_210 = x_208;
}
lean_ctor_set(x_210, 0, x_202);
lean_ctor_set(x_210, 1, x_203);
lean_ctor_set(x_210, 2, x_204);
lean_ctor_set(x_210, 3, x_209);
lean_ctor_set(x_210, 4, x_206);
lean_ctor_set(x_210, 5, x_207);
x_211 = lean_st_ref_set(x_8, x_210, x_201);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_213 = x_211;
} else {
 lean_dec_ref(x_211);
 x_213 = lean_box(0);
}
x_214 = lean_box(0);
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_212);
return x_215;
}
}
else
{
lean_object* x_216; uint8_t x_217; 
x_216 = lean_ctor_get(x_18, 0);
lean_inc(x_216);
lean_dec(x_18);
x_217 = !lean_is_exclusive(x_19);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_218 = lean_ctor_get(x_19, 0);
x_219 = lean_ctor_get(x_7, 0);
x_220 = lean_ctor_get(x_7, 1);
x_221 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_9, x_10, x_11, x_12, x_13);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = l_Lean_FileMap_toPosition(x_220, x_216);
lean_dec(x_216);
x_225 = l_Lean_FileMap_toPosition(x_220, x_218);
lean_dec(x_218);
lean_ctor_set(x_19, 0, x_225);
x_226 = lean_ctor_get(x_11, 4);
x_227 = lean_ctor_get(x_11, 5);
lean_inc(x_227);
lean_inc(x_226);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_222);
x_230 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
lean_inc(x_219);
x_231 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_231, 0, x_219);
lean_ctor_set(x_231, 1, x_224);
lean_ctor_set(x_231, 2, x_19);
lean_ctor_set(x_231, 3, x_230);
lean_ctor_set(x_231, 4, x_229);
lean_ctor_set_uint8(x_231, sizeof(void*)*5, x_3);
x_232 = lean_st_ref_get(x_12, x_223);
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
lean_dec(x_232);
x_234 = lean_st_ref_take(x_8, x_233);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = !lean_is_exclusive(x_235);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_238 = lean_ctor_get(x_235, 3);
x_239 = l_Std_PersistentArray_push___rarg(x_238, x_231);
lean_ctor_set(x_235, 3, x_239);
x_240 = lean_st_ref_set(x_8, x_235, x_236);
x_241 = !lean_is_exclusive(x_240);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_240, 0);
lean_dec(x_242);
x_243 = lean_box(0);
lean_ctor_set(x_240, 0, x_243);
return x_240;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_240, 1);
lean_inc(x_244);
lean_dec(x_240);
x_245 = lean_box(0);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_247 = lean_ctor_get(x_235, 0);
x_248 = lean_ctor_get(x_235, 1);
x_249 = lean_ctor_get(x_235, 2);
x_250 = lean_ctor_get(x_235, 3);
x_251 = lean_ctor_get(x_235, 4);
x_252 = lean_ctor_get(x_235, 5);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_235);
x_253 = l_Std_PersistentArray_push___rarg(x_250, x_231);
x_254 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_254, 0, x_247);
lean_ctor_set(x_254, 1, x_248);
lean_ctor_set(x_254, 2, x_249);
lean_ctor_set(x_254, 3, x_253);
lean_ctor_set(x_254, 4, x_251);
lean_ctor_set(x_254, 5, x_252);
x_255 = lean_st_ref_set(x_8, x_254, x_236);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_257 = x_255;
} else {
 lean_dec_ref(x_255);
 x_257 = lean_box(0);
}
x_258 = lean_box(0);
if (lean_is_scalar(x_257)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_257;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_256);
return x_259;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_260 = lean_ctor_get(x_19, 0);
lean_inc(x_260);
lean_dec(x_19);
x_261 = lean_ctor_get(x_7, 0);
x_262 = lean_ctor_get(x_7, 1);
x_263 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_9, x_10, x_11, x_12, x_13);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
x_266 = l_Lean_FileMap_toPosition(x_262, x_216);
lean_dec(x_216);
x_267 = l_Lean_FileMap_toPosition(x_262, x_260);
lean_dec(x_260);
x_268 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_268, 0, x_267);
x_269 = lean_ctor_get(x_11, 4);
x_270 = lean_ctor_get(x_11, 5);
lean_inc(x_270);
lean_inc(x_269);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_264);
x_273 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__7;
lean_inc(x_261);
x_274 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_274, 0, x_261);
lean_ctor_set(x_274, 1, x_266);
lean_ctor_set(x_274, 2, x_268);
lean_ctor_set(x_274, 3, x_273);
lean_ctor_set(x_274, 4, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*5, x_3);
x_275 = lean_st_ref_get(x_12, x_265);
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
lean_dec(x_275);
x_277 = lean_st_ref_take(x_8, x_276);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_280 = lean_ctor_get(x_278, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_278, 1);
lean_inc(x_281);
x_282 = lean_ctor_get(x_278, 2);
lean_inc(x_282);
x_283 = lean_ctor_get(x_278, 3);
lean_inc(x_283);
x_284 = lean_ctor_get(x_278, 4);
lean_inc(x_284);
x_285 = lean_ctor_get(x_278, 5);
lean_inc(x_285);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 lean_ctor_release(x_278, 2);
 lean_ctor_release(x_278, 3);
 lean_ctor_release(x_278, 4);
 lean_ctor_release(x_278, 5);
 x_286 = x_278;
} else {
 lean_dec_ref(x_278);
 x_286 = lean_box(0);
}
x_287 = l_Std_PersistentArray_push___rarg(x_283, x_274);
if (lean_is_scalar(x_286)) {
 x_288 = lean_alloc_ctor(0, 6, 0);
} else {
 x_288 = x_286;
}
lean_ctor_set(x_288, 0, x_280);
lean_ctor_set(x_288, 1, x_281);
lean_ctor_set(x_288, 2, x_282);
lean_ctor_set(x_288, 3, x_287);
lean_ctor_set(x_288, 4, x_284);
lean_ctor_set(x_288, 5, x_285);
x_289 = lean_st_ref_set(x_8, x_288, x_279);
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_291 = x_289;
} else {
 lean_dec_ref(x_289);
 x_291 = lean_box(0);
}
x_292 = lean_box(0);
if (lean_is_scalar(x_291)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_291;
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_290);
return x_293;
}
}
}
}
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_evalOpen___spec__8(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 3);
x_14 = l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalOpen___spec__9(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown declaration '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__2;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__3;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = 2;
x_18 = l_Lean_Elab_log___at_Lean_Elab_Tactic_evalOpen___spec__8(x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
}
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_take(x_2, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_15, 0, x_19);
x_20 = lean_st_ref_set(x_2, x_15, x_16);
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
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_st_ref_set(x_2, x_30, x_16);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = x_4 < x_3;
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_5);
x_18 = lean_array_uget(x_2, x_4);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_getArg(x_18, x_19);
x_21 = l_Lean_Syntax_getId(x_20);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(2u);
x_23 = l_Lean_Syntax_getArg(x_18, x_22);
x_24 = l_Lean_Syntax_getId(x_23);
lean_dec(x_23);
x_25 = l_Lean_Name_append(x_1, x_21);
x_26 = lean_st_ref_get(x_14, x_15);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Environment_contains(x_29, x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; 
lean_dec(x_24);
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
x_33 = lean_ctor_get(x_13, 2);
x_34 = lean_ctor_get(x_13, 3);
x_35 = lean_ctor_get(x_13, 4);
x_36 = lean_ctor_get(x_13, 5);
x_37 = lean_ctor_get(x_13, 6);
x_38 = lean_ctor_get(x_13, 7);
x_39 = l_Lean_replaceRef(x_18, x_34);
lean_dec(x_18);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
x_40 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_33);
lean_ctor_set(x_40, 3, x_39);
lean_ctor_set(x_40, 4, x_35);
lean_ctor_set(x_40, 5, x_36);
lean_ctor_set(x_40, 6, x_37);
lean_ctor_set(x_40, 7, x_38);
x_41 = l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7(x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_40, x_14, x_28);
lean_dec(x_40);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = 1;
x_44 = x_4 + x_43;
x_45 = lean_box(0);
x_4 = x_44;
x_5 = x_45;
x_15 = x_42;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; 
lean_dec(x_18);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_24);
lean_ctor_set(x_47, 1, x_25);
x_48 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__10(x_47, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_28);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = 1;
x_51 = x_4 + x_50;
x_52 = lean_box(0);
x_4 = x_51;
x_5 = x_52;
x_15 = x_49;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenRenaming___at_Lean_Elab_Tactic_evalOpen___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_getId(x_13);
lean_dec(x_13);
x_15 = l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = l_Lean_Syntax_getSepArgs(x_19);
lean_dec(x_19);
x_21 = lean_array_get_size(x_20);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = lean_box(0);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__11(x_16, x_20, x_22, x_23, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_20);
lean_dec(x_16);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
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
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__13(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = x_4 < x_3;
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_array_uget(x_2, x_4);
x_19 = l_Lean_Syntax_getId(x_18);
lean_inc(x_19);
x_20 = l_Lean_Name_append(x_1, x_19);
x_21 = lean_st_ref_get(x_14, x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Environment_contains(x_24, x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; 
lean_dec(x_19);
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
x_28 = lean_ctor_get(x_13, 2);
x_29 = lean_ctor_get(x_13, 3);
x_30 = lean_ctor_get(x_13, 4);
x_31 = lean_ctor_get(x_13, 5);
x_32 = lean_ctor_get(x_13, 6);
x_33 = lean_ctor_get(x_13, 7);
x_34 = l_Lean_replaceRef(x_18, x_29);
lean_dec(x_18);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
x_35 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_27);
lean_ctor_set(x_35, 2, x_28);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_35, 4, x_30);
lean_ctor_set(x_35, 5, x_31);
lean_ctor_set(x_35, 6, x_32);
lean_ctor_set(x_35, 7, x_33);
x_36 = l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7(x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_35, x_14, x_23);
lean_dec(x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = 1;
x_39 = x_4 + x_38;
x_4 = x_39;
x_15 = x_37;
goto _start;
}
else
{
lean_object* x_41; size_t x_42; size_t x_43; 
lean_dec(x_20);
lean_dec(x_18);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_19);
lean_ctor_set(x_41, 1, x_5);
x_42 = 1;
x_43 = x_4 + x_42;
x_4 = x_43;
x_5 = x_41;
x_15 = x_23;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenHiding___at_Lean_Elab_Tactic_evalOpen___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_getId(x_13);
lean_dec(x_13);
x_15 = l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = l_Lean_Syntax_getArgs(x_20);
lean_dec(x_20);
x_22 = lean_array_get_size(x_21);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = 0;
x_25 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__13(x_16, x_21, x_23, x_24, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_26);
x_29 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__10(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
return x_29;
}
else
{
uint8_t x_30; 
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
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__15(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = x_4 < x_3;
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_5);
x_18 = lean_array_uget(x_2, x_4);
x_19 = l_Lean_Syntax_getId(x_18);
lean_inc(x_19);
x_20 = l_Lean_Name_append(x_1, x_19);
x_21 = lean_st_ref_get(x_14, x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Environment_contains(x_24, x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
lean_dec(x_19);
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
x_28 = lean_ctor_get(x_13, 2);
x_29 = lean_ctor_get(x_13, 3);
x_30 = lean_ctor_get(x_13, 4);
x_31 = lean_ctor_get(x_13, 5);
x_32 = lean_ctor_get(x_13, 6);
x_33 = lean_ctor_get(x_13, 7);
x_34 = l_Lean_replaceRef(x_18, x_29);
lean_dec(x_18);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
x_35 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_27);
lean_ctor_set(x_35, 2, x_28);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_35, 4, x_30);
lean_ctor_set(x_35, 5, x_31);
lean_ctor_set(x_35, 6, x_32);
lean_ctor_set(x_35, 7, x_33);
x_36 = l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7(x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_35, x_14, x_23);
lean_dec(x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = 1;
x_39 = x_4 + x_38;
x_40 = lean_box(0);
x_4 = x_39;
x_5 = x_40;
x_15 = x_37;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; 
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_19);
lean_ctor_set(x_42, 1, x_20);
x_43 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__10(x_42, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_23);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = 1;
x_46 = x_4 + x_45;
x_47 = lean_box(0);
x_4 = x_46;
x_5 = x_47;
x_15 = x_44;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenOnly___at_Lean_Elab_Tactic_evalOpen___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_getId(x_13);
lean_dec(x_13);
x_15 = l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
x_21 = lean_array_get_size(x_20);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = lean_box(0);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__15(x_16, x_20, x_22, x_23, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_20);
lean_dec(x_16);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
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
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__18(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = x_4 < x_3;
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_5);
x_18 = lean_array_uget(x_2, x_4);
x_19 = lean_st_ref_take(x_14, x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_1);
x_24 = l_Lean_ScopedEnvExtension_activateScoped___rarg(x_18, x_23, x_1);
lean_ctor_set(x_20, 0, x_24);
x_25 = lean_st_ref_set(x_14, x_20, x_21);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = 1;
x_28 = x_4 + x_27;
x_29 = lean_box(0);
x_4 = x_28;
x_5 = x_29;
x_15 = x_26;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
x_33 = lean_ctor_get(x_20, 2);
x_34 = lean_ctor_get(x_20, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
lean_inc(x_1);
x_35 = l_Lean_ScopedEnvExtension_activateScoped___rarg(x_18, x_31, x_1);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_34);
x_37 = lean_st_ref_set(x_14, x_36, x_21);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = 1;
x_40 = x_4 + x_39;
x_41 = lean_box(0);
x_4 = x_40;
x_5 = x_41;
x_15 = x_38;
goto _start;
}
}
}
}
lean_object* l_Lean_activateScoped___at_Lean_Elab_Tactic_evalOpen___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_scopedEnvExtensionsRef;
x_15 = lean_st_ref_get(x_14, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_get_size(x_16);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
x_21 = lean_box(0);
x_22 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__18(x_1, x_16, x_19, x_20, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_16);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__19(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = x_3 < x_2;
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_17 = lean_array_uget(x_1, x_3);
x_18 = l_Lean_Syntax_getId(x_17);
lean_dec(x_17);
x_19 = l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
lean_inc(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__10(x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_21);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_activateScoped___at_Lean_Elab_Tactic_evalOpen___spec__17(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = 1;
x_29 = x_3 + x_28;
x_30 = lean_box(0);
x_3 = x_29;
x_4 = x_30;
x_14 = x_27;
goto _start;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenSimple___at_Lean_Elab_Tactic_evalOpen___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = lean_array_get_size(x_14);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = lean_box(0);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__19(x_14, x_16, x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_14);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
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
}
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_2, x_13);
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
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___lambda__1___boxed), 11, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Command");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__13;
x_2 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("openSimple");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__3;
x_2 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("openOnly");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__3;
x_2 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("openHiding");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__3;
x_2 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; 
x_24 = lean_ctor_get(x_8, 5);
lean_inc(x_24);
x_25 = lean_ctor_get(x_8, 4);
lean_inc(x_25);
x_26 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__1;
lean_inc(x_1);
x_27 = l_Lean_Syntax_getKind(x_1);
x_28 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__5;
x_29 = lean_name_eq(x_27, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
if (x_29 == 0)
{
uint8_t x_140; 
x_140 = 0;
x_31 = x_140;
goto block_139;
}
else
{
uint8_t x_141; 
x_141 = 1;
x_31 = x_141;
goto block_139;
}
block_23:
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_14);
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
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
block_139:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_st_ref_get(x_9, x_10);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_st_mk_ref(x_30, x_33);
if (x_31 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__7;
x_38 = lean_name_eq(x_27, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__9;
x_40 = lean_name_eq(x_27, x_39);
lean_dec(x_27);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenRenaming___at_Lean_Elab_Tactic_evalOpen___spec__4(x_1, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_1);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_9);
lean_inc(x_35);
x_44 = lean_apply_11(x_26, x_42, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_st_ref_get(x_9, x_46);
lean_dec(x_9);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_st_ref_get(x_35, x_48);
lean_dec(x_35);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_49, 0, x_52);
x_11 = x_49;
goto block_23;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_45);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_11 = x_56;
goto block_23;
}
}
else
{
uint8_t x_57; 
lean_dec(x_35);
lean_dec(x_9);
x_57 = !lean_is_exclusive(x_44);
if (x_57 == 0)
{
x_11 = x_44;
goto block_23;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_44, 0);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_44);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_11 = x_60;
goto block_23;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_41);
if (x_61 == 0)
{
x_11 = x_41;
goto block_23;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_41, 0);
x_63 = lean_ctor_get(x_41, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_41);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_11 = x_64;
goto block_23;
}
}
}
else
{
lean_object* x_65; 
x_65 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenHiding___at_Lean_Elab_Tactic_evalOpen___spec__12(x_1, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_1);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_9);
lean_inc(x_35);
x_68 = lean_apply_11(x_26, x_66, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_st_ref_get(x_9, x_70);
lean_dec(x_9);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_st_ref_get(x_35, x_72);
lean_dec(x_35);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_73, 0, x_76);
x_11 = x_73;
goto block_23;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_73, 0);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_73);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_69);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_11 = x_80;
goto block_23;
}
}
else
{
uint8_t x_81; 
lean_dec(x_35);
lean_dec(x_9);
x_81 = !lean_is_exclusive(x_68);
if (x_81 == 0)
{
x_11 = x_68;
goto block_23;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_68, 0);
x_83 = lean_ctor_get(x_68, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_68);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_11 = x_84;
goto block_23;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_65);
if (x_85 == 0)
{
x_11 = x_65;
goto block_23;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_65, 0);
x_87 = lean_ctor_get(x_65, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_65);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_11 = x_88;
goto block_23;
}
}
}
}
else
{
lean_object* x_89; 
lean_dec(x_27);
x_89 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenOnly___at_Lean_Elab_Tactic_evalOpen___spec__14(x_1, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_1);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_9);
lean_inc(x_35);
x_92 = lean_apply_11(x_26, x_90, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_st_ref_get(x_9, x_94);
lean_dec(x_9);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_st_ref_get(x_35, x_96);
lean_dec(x_35);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_93);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_97, 0, x_100);
x_11 = x_97;
goto block_23;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_97, 0);
x_102 = lean_ctor_get(x_97, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_97);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_93);
lean_ctor_set(x_103, 1, x_101);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_11 = x_104;
goto block_23;
}
}
else
{
uint8_t x_105; 
lean_dec(x_35);
lean_dec(x_9);
x_105 = !lean_is_exclusive(x_92);
if (x_105 == 0)
{
x_11 = x_92;
goto block_23;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_92, 0);
x_107 = lean_ctor_get(x_92, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_92);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_11 = x_108;
goto block_23;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_109 = !lean_is_exclusive(x_89);
if (x_109 == 0)
{
x_11 = x_89;
goto block_23;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_89, 0);
x_111 = lean_ctor_get(x_89, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_89);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_11 = x_112;
goto block_23;
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_27);
x_113 = lean_ctor_get(x_34, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_34, 1);
lean_inc(x_114);
lean_dec(x_34);
x_115 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenSimple___at_Lean_Elab_Tactic_evalOpen___spec__16(x_1, x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_114);
lean_dec(x_1);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
lean_inc(x_9);
lean_inc(x_113);
x_118 = lean_apply_11(x_26, x_116, x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_st_ref_get(x_9, x_120);
lean_dec(x_9);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_st_ref_get(x_113, x_122);
lean_dec(x_113);
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_119);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set(x_123, 0, x_126);
x_11 = x_123;
goto block_23;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_123, 0);
x_128 = lean_ctor_get(x_123, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_123);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_119);
lean_ctor_set(x_129, 1, x_127);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_11 = x_130;
goto block_23;
}
}
else
{
uint8_t x_131; 
lean_dec(x_113);
lean_dec(x_9);
x_131 = !lean_is_exclusive(x_118);
if (x_131 == 0)
{
x_11 = x_118;
goto block_23;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_118, 0);
x_133 = lean_ctor_get(x_118, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_118);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_11 = x_134;
goto block_23;
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_113);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_135 = !lean_is_exclusive(x_115);
if (x_135 == 0)
{
x_11 = x_115;
goto block_23;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_115, 0);
x_137 = lean_ctor_get(x_115, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_115);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_11 = x_138;
goto block_23;
}
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__21(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_3 < x_2;
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_4);
x_16 = lean_array_uget(x_1, x_3);
x_17 = lean_st_ref_take(x_12, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = l_Lean_ScopedEnvExtension_popScope___rarg(x_16, x_21);
lean_dec(x_16);
lean_ctor_set(x_18, 0, x_22);
x_23 = lean_st_ref_set(x_12, x_18, x_19);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = 1;
x_26 = x_3 + x_25;
x_27 = lean_box(0);
x_3 = x_26;
x_4 = x_27;
x_13 = x_24;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
x_31 = lean_ctor_get(x_18, 2);
x_32 = lean_ctor_get(x_18, 3);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_33 = l_Lean_ScopedEnvExtension_popScope___rarg(x_16, x_29);
lean_dec(x_16);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_31);
lean_ctor_set(x_34, 3, x_32);
x_35 = lean_st_ref_set(x_12, x_34, x_19);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = 1;
x_38 = x_3 + x_37;
x_39 = lean_box(0);
x_3 = x_38;
x_4 = x_39;
x_13 = x_36;
goto _start;
}
}
}
}
lean_object* l_Lean_popScope___at_Lean_Elab_Tactic_evalOpen___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_scopedEnvExtensionsRef;
x_13 = lean_st_ref_get(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_14);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = lean_box(0);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__21(x_14, x_17, x_18, x_19, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_14);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
lean_object* l_Lean_Elab_Tactic_evalOpen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_pushScope___at_Lean_Elab_Tactic_evalOpen___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_8, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_8, 4);
lean_inc(x_24);
x_25 = lean_ctor_get(x_8, 6);
lean_inc(x_25);
x_26 = lean_ctor_get(x_8, 7);
lean_inc(x_26);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set(x_27, 5, x_16);
lean_ctor_set(x_27, 6, x_25);
lean_ctor_set(x_27, 7, x_26);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_28 = l_Lean_Elab_Tactic_evalTacticAux(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_27, x_9, x_17);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_popScope___at_Lean_Elab_Tactic_evalOpen___spec__20(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_38 = l_Lean_popScope___at_Lean_Elab_Tactic_evalOpen___spec__20(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_15, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_15, 1);
lean_inc(x_44);
lean_dec(x_15);
x_45 = l_Lean_popScope___at_Lean_Elab_Tactic_evalOpen___spec__20(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__2(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
lean_object* l_Lean_pushScope___at_Lean_Elab_Tactic_evalOpen___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_pushScope___at_Lean_Elab_Tactic_evalOpen___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalOpen___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at_Lean_Elab_Tactic_evalOpen___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalOpen___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Elab_logAt___at_Lean_Elab_Tactic_evalOpen___spec__9(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
return x_15;
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_evalOpen___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Elab_log___at_Lean_Elab_Tactic_evalOpen___spec__8(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
lean_object* l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__11(x_1, x_2, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenRenaming___at_Lean_Elab_Tactic_evalOpen___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenRenaming___at_Lean_Elab_Tactic_evalOpen___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__13(x_1, x_2, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenHiding___at_Lean_Elab_Tactic_evalOpen___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenHiding___at_Lean_Elab_Tactic_evalOpen___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__15(x_1, x_2, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenOnly___at_Lean_Elab_Tactic_evalOpen___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenOnly___at_Lean_Elab_Tactic_evalOpen___spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__18(x_1, x_2, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_18;
}
}
lean_object* l_Lean_activateScoped___at_Lean_Elab_Tactic_evalOpen___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_activateScoped___at_Lean_Elab_Tactic_evalOpen___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__19(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_17;
}
}
lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenSimple___at_Lean_Elab_Tactic_evalOpen___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenSimple___at_Lean_Elab_Tactic_evalOpen___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalOpen___spec__21(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
lean_object* l_Lean_popScope___at_Lean_Elab_Tactic_evalOpen___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_popScope___at_Lean_Elab_Tactic_evalOpen___spec__20(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Elab_Tactic_evalOpen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalOpen(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("open");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalOpen");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalOpen___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalOpen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_Tactic_elabSetOption___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 5);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_st_ref_get(x_9, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_take(x_5, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 5);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 5);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_28, 1);
x_34 = l_Std_PersistentArray_push___rarg(x_33, x_1);
lean_ctor_set(x_28, 1, x_34);
x_35 = lean_st_ref_set(x_5, x_27, x_29);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get_uint8(x_28, sizeof(void*)*2);
x_43 = lean_ctor_get(x_28, 0);
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_28);
x_45 = l_Std_PersistentArray_push___rarg(x_44, x_1);
x_46 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_42);
lean_ctor_set(x_27, 5, x_46);
x_47 = lean_st_ref_set(x_5, x_27, x_29);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_52 = lean_ctor_get(x_27, 0);
x_53 = lean_ctor_get(x_27, 1);
x_54 = lean_ctor_get(x_27, 2);
x_55 = lean_ctor_get(x_27, 3);
x_56 = lean_ctor_get(x_27, 4);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_27);
x_57 = lean_ctor_get_uint8(x_28, sizeof(void*)*2);
x_58 = lean_ctor_get(x_28, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_28, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_60 = x_28;
} else {
 lean_dec_ref(x_28);
 x_60 = lean_box(0);
}
x_61 = l_Std_PersistentArray_push___rarg(x_59, x_1);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 1);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*2, x_57);
x_63 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_63, 0, x_52);
lean_ctor_set(x_63, 1, x_53);
lean_ctor_set(x_63, 2, x_54);
lean_ctor_set(x_63, 3, x_55);
lean_ctor_set(x_63, 4, x_56);
lean_ctor_set(x_63, 5, x_62);
x_64 = lean_st_ref_set(x_5, x_63, x_29);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
}
}
}
lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Tactic_elabSetOption___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 5);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__3;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Tactic_elabSetOption___spec__4(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
return x_26;
}
}
}
lean_object* l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Tactic_elabSetOption___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Tactic_elabSetOption___spec__3(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabSetOption___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_KVMap_insertCore(x_13, x_1, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type mismatch at set_option");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 3);
lean_inc(x_12);
lean_inc(x_1);
x_13 = l_Lean_getOptionDecl(x_1, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_DataValue_sameCtor(x_16, x_2);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___closed__2;
x_19 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTacticAux___spec__2(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
lean_dec(x_9);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___lambda__1(x_1, x_2, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_io_error_to_string(x_27);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_13, 0, x_31);
return x_13;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_13);
x_34 = lean_io_error_to_string(x_32);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_12);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected set_option value ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("true");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("false");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Syntax_getId(x_1);
x_13 = lean_erase_macro_scopes(x_12);
x_14 = l_Lean_Syntax_isStrLit_x3f(x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_numLitKind;
x_16 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_15, x_2);
if (lean_obj_tag(x_16) == 0)
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__3;
x_19 = lean_string_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__4;
x_21 = lean_string_dec_eq(x_17, x_20);
lean_dec(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_13);
x_22 = lean_ctor_get(x_9, 3);
lean_inc(x_22);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Tactic_elabSetOption___spec__2(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_2);
x_27 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at_Lean_Elab_Tactic_elabSetOption___spec__5(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
lean_dec(x_9);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_2);
x_32 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__5;
x_33 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6(x_13, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_17);
lean_dec(x_2);
x_34 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__6;
x_35 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6(x_13, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_13);
x_36 = lean_ctor_get(x_9, 3);
lean_inc(x_36);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Tactic_elabSetOption___spec__2(x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_2);
x_41 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__2;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Elab_Term_reportUnsolvedGoals___closed__8;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_throwError___at_Lean_Elab_Tactic_elabSetOption___spec__5(x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
lean_dec(x_9);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
x_46 = lean_ctor_get(x_16, 0);
lean_inc(x_46);
lean_dec(x_16);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6(x_13, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_2);
x_49 = lean_ctor_get(x_14, 0);
lean_inc(x_49);
lean_dec(x_14);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6(x_13, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_51;
}
}
}
lean_object* l_Lean_Elab_Tactic_elabSetOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_inc(x_8);
x_15 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1(x_12, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(4u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_8, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_8, 0);
lean_dec(x_22);
x_23 = l_Lean_maxRecDepth;
x_24 = l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____spec__1(x_16, x_23);
lean_ctor_set(x_8, 2, x_24);
lean_ctor_set(x_8, 0, x_16);
x_25 = l_Lean_Elab_Tactic_evalTacticAux(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_8, 1);
x_27 = lean_ctor_get(x_8, 3);
x_28 = lean_ctor_get(x_8, 4);
x_29 = lean_ctor_get(x_8, 5);
x_30 = lean_ctor_get(x_8, 6);
x_31 = lean_ctor_get(x_8, 7);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_8);
x_32 = l_Lean_maxRecDepth;
x_33 = l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____spec__1(x_16, x_32);
x_34 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_34, 0, x_16);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_27);
lean_ctor_set(x_34, 4, x_28);
lean_ctor_set(x_34, 5, x_29);
lean_ctor_set(x_34, 6, x_30);
lean_ctor_set(x_34, 7, x_31);
x_35 = l_Lean_Elab_Tactic_evalTacticAux(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_34, x_9, x_17);
return x_35;
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
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_15);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_Tactic_elabSetOption___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Tactic_elabSetOption___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Tactic_elabSetOption___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Tactic_elabSetOption___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Tactic_elabSetOption___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Tactic_elabSetOption___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabSetOption___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_elabSetOption___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
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
lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_Elab_Tactic_elabSetOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabSetOption(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("set_option");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabSetOption");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabSetOption___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_elabSetOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_evalAllGoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_18 = l_Lean_Meta_isExprMVarAssigned(x_16, x_9, x_10, x_11, x_12, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_42; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_2);
lean_inc(x_16);
lean_ctor_set(x_3, 1, x_2);
x_22 = l_Lean_Elab_Tactic_setGoals(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
x_26 = l_Lean_Elab_Tactic_saveState___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_23);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_42 = l_Lean_Elab_Tactic_evalTacticAux(x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_28);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_27);
lean_dec(x_16);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_List_foldl___at_Array_appendList___spec__1___rarg(x_4, x_45);
x_3 = x_17;
x_4 = x_47;
x_13 = x_46;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
lean_dec(x_42);
x_29 = x_49;
x_30 = x_50;
goto block_41;
}
block_41:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Lean_Elab_Tactic_SavedState_restore(x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1(x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_array_push(x_4, x_16);
x_3 = x_17;
x_4 = x_35;
x_13 = x_34;
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
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
}
else
{
lean_object* x_51; 
lean_free_object(x_3);
lean_dec(x_16);
x_51 = lean_ctor_get(x_18, 1);
lean_inc(x_51);
lean_dec(x_18);
x_3 = x_17;
x_13 = x_51;
goto _start;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_3, 0);
x_54 = lean_ctor_get(x_3, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_3);
x_55 = l_Lean_Meta_isExprMVarAssigned(x_53, x_9, x_10, x_11, x_12, x_13);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_80; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
lean_inc(x_2);
lean_inc(x_53);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_2);
x_60 = l_Lean_Elab_Tactic_setGoals(x_59, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_58);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_unsigned_to_nat(1u);
x_63 = l_Lean_Syntax_getArg(x_1, x_62);
x_64 = l_Lean_Elab_Tactic_saveState___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_61);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_80 = l_Lean_Elab_Tactic_evalTacticAux(x_63, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_66);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_65);
lean_dec(x_53);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_List_foldl___at_Array_appendList___spec__1___rarg(x_4, x_83);
x_3 = x_54;
x_4 = x_85;
x_13 = x_84;
goto _start;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_80, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_80, 1);
lean_inc(x_88);
lean_dec(x_80);
x_67 = x_87;
x_68 = x_88;
goto block_79;
}
block_79:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = l_Lean_Elab_Tactic_SavedState_restore(x_65, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_68);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1(x_67, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_array_push(x_4, x_53);
x_3 = x_54;
x_4 = x_73;
x_13 = x_72;
goto _start;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_75 = lean_ctor_get(x_71, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_71, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_77 = x_71;
} else {
 lean_dec_ref(x_71);
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
else
{
lean_object* x_89; 
lean_dec(x_53);
x_89 = lean_ctor_get(x_55, 1);
lean_inc(x_89);
lean_dec(x_55);
x_3 = x_54;
x_13 = x_89;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalAllGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_Elab_Tactic_getGoals___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_Lean_Elab_Tactic_tacticElabAttribute___lambda__7___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_List_forIn_loop___at_Lean_Elab_Tactic_evalAllGoals___spec__1(x_1, x_14, x_12, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_to_list(lean_box(0), x_17);
x_20 = l_Lean_Elab_Tactic_setGoals(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_evalAllGoals___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_loop___at_Lean_Elab_Tactic_evalAllGoals___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Lean_Elab_Tactic_evalAllGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalAllGoals(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("allGoals");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalAllGoals");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalAllGoals___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalAllGoals(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_evalTacticSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Elab_Tactic_evalTacticAux(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_evalTacticSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalTacticSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticSeq");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalTacticSeq");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__5() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__7___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1___rarg), 1, 0);
return x_9;
}
}
lean_object* l_Lean_Elab_Tactic_evalChoiceAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_dec(x_2);
x_14 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1___rarg(x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_1, x_2);
x_16 = l_Lean_Elab_Tactic_saveState___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_19 = l_Lean_Elab_Tactic_evalTacticAux(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
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
x_22 = l_Lean_Elab_Tactic_SavedState_restore(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Elab_Tactic_evalChoiceAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalChoiceAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
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
x_13 = l_Lean_Elab_Tactic_evalChoiceAux(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_evalChoice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalChoice(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("choice");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalChoice");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__5() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("skip");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalSkip");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__5() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_evalUnknown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_Elab_Tactic_getGoals___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Tactic_elabSetOption___spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_15;
}
}
lean_object* l_Lean_Elab_Tactic_evalUnknown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalUnknown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalUnknown");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalUnknown___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalUnknown(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalFailIfSuccess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tactic succeeded");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalFailIfSuccess___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalFailIfSuccess___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = l_Lean_Elab_Tactic_saveState___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_23 = l_Lean_Elab_Tactic_evalTacticAux(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
lean_dec(x_21);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = 1;
x_11 = x_25;
x_12 = x_24;
goto block_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_Elab_Tactic_SavedState_restore(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = 0;
x_11 = x_29;
x_12 = x_28;
goto block_17;
}
block_17:
{
if (x_11 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Elab_Tactic_evalFailIfSuccess___closed__2;
x_16 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalFailIfSuccess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalFailIfSuccess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failIfSuccess");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalFailIfSuccess");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__5() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
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
x_15 = l_Lean_Elab_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(x_13, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("traceState");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalTraceState");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__5() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Meta_assumption(x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = l_Lean_Elab_Tactic_replaceMainGoal(x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
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
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_13);
if (x_27 == 0)
{
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
}
static lean_object* _init_l_Lean_Elab_Tactic_evalAssumption___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalAssumption___rarg___lambda__1___boxed), 9, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Tactic_evalAssumption___rarg___closed__1;
x_11 = l_Lean_Elab_Tactic_withMainContext___rarg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
lean_object* l_Lean_Elab_Tactic_evalAssumption___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_evalAssumption___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assumption");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalAssumption");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__5() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_evalContradiction___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_unsigned_to_nat(2u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Meta_contradiction(x_11, x_13, x_14, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Tactic_replaceMainGoal(x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
static lean_object* _init_l_Lean_Elab_Tactic_evalContradiction___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalContradiction___rarg___lambda__1___boxed), 9, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_evalContradiction___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Tactic_evalContradiction___rarg___closed__1;
x_11 = l_Lean_Elab_Tactic_withMainContext___rarg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_evalContradiction(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalContradiction___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalContradiction___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_evalContradiction___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Tactic_evalContradiction___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalContradiction(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("contradiction");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalContradiction");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalContradiction___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalContradiction(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntro_introStep_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Tactic_evalIntro_introStep_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntro_introStep_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntro_introStep___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l_Lean_Meta_intro(x_12, x_1, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_Tactic_replaceMainGoal(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
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
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_object* l_Lean_Elab_Tactic_evalIntro_introStep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntro_introStep___lambda__1___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntro_introStep___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalIntro_introStep___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Tactic_evalIntro___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = l_Lean_SourceInfo_fromRef(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Tactic_evalIntro___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Tactic_evalIntro___spec__1___rarg___boxed), 3, 0);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("intro");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("null");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(";");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ident");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__13;
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hole");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalIntro___closed__12;
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("h");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalIntro___closed__15;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_evalIntro___closed__15;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Tactic_evalIntro___closed__16;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("match");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalIntro___closed__4;
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute___lambda__7___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchDiscr");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalIntro___closed__12;
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__22;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalIntro___closed__6;
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__21;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("with");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchAlts");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalIntro___closed__12;
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__26;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchAlt");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalIntro___closed__12;
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__28;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("|");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("=>");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntheticHole");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalIntro___closed__12;
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__32;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("?");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tacticTry_");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__38;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("try");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("group");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__41;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("clear");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__43;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__35;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalIntro___closed__2;
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
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_nullKind;
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
x_18 = l_Lean_Syntax_isNodeOf(x_15, x_16, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_inc(x_15);
x_19 = l_Lean_Syntax_isNodeOf(x_15, x_16, x_14);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Syntax_getNumArgs(x_15);
x_21 = lean_nat_dec_le(x_14, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1___rarg(x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_23 = l_Lean_Syntax_getArg(x_15, x_17);
x_24 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
x_25 = lean_nat_sub(x_20, x_17);
lean_dec(x_20);
x_26 = l_Array_extract___rarg(x_24, x_14, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Syntax_getArgs(x_27);
lean_dec(x_27);
x_29 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Tactic_evalIntro___spec__1___rarg(x_8, x_9, x_10);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Elab_Tactic_evalIntro___closed__1;
lean_inc(x_30);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Elab_Tactic_evalIntro___closed__5;
x_39 = lean_array_push(x_38, x_23);
x_40 = l_Lean_Elab_Tactic_evalIntro___closed__4;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Elab_Tactic_evalIntro___closed__6;
x_43 = lean_array_push(x_42, x_37);
lean_inc(x_43);
x_44 = lean_array_push(x_43, x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_11);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Elab_Tactic_evalIntro___closed__7;
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_30);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Elab_Tactic_tacticElabAttribute___lambda__7___closed__1;
x_49 = l_Array_append___rarg(x_48, x_28);
lean_dec(x_28);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_array_push(x_43, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_11);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Elab_Tactic_evalIntro___closed__8;
x_54 = lean_array_push(x_53, x_45);
x_55 = lean_array_push(x_54, x_47);
x_56 = lean_array_push(x_55, x_52);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_40);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_array_push(x_38, x_57);
x_59 = l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__2;
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l_Lean_Elab_Tactic_evalTacticAux(x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
lean_dec(x_2);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = l_Lean_Syntax_getArg(x_15, x_17);
lean_dec(x_15);
x_63 = l_Lean_Elab_Tactic_evalIntro___closed__10;
lean_inc(x_62);
x_64 = l_Lean_Syntax_isOfKind(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = l_Lean_Elab_Tactic_evalIntro___closed__14;
lean_inc(x_62);
x_66 = l_Lean_Syntax_isOfKind(x_62, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_67 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Tactic_evalIntro___spec__1___rarg(x_8, x_9, x_10);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_69);
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
x_76 = l_Lean_Elab_Tactic_evalIntro___closed__1;
lean_inc(x_68);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Elab_Tactic_evalIntro___closed__18;
x_79 = l_Lean_addMacroScope(x_74, x_78, x_71);
x_80 = lean_box(0);
x_81 = l_Lean_Elab_Tactic_evalIntro___closed__17;
lean_inc(x_68);
x_82 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_82, 0, x_68);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_79);
lean_ctor_set(x_82, 3, x_80);
x_83 = l_Lean_Elab_Tactic_evalIntro___closed__5;
lean_inc(x_82);
x_84 = lean_array_push(x_83, x_82);
x_85 = l_Lean_Elab_Tactic_evalIntro___closed__4;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = l_Lean_Elab_Tactic_evalIntro___closed__6;
x_88 = lean_array_push(x_87, x_77);
lean_inc(x_86);
x_89 = lean_array_push(x_88, x_86);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_11);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_Elab_Tactic_evalIntro___closed__7;
lean_inc(x_68);
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_68);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_Elab_Tactic_evalIntro___closed__19;
lean_inc(x_68);
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_68);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_Elab_Tactic_evalIntro___closed__24;
x_96 = lean_array_push(x_95, x_82);
x_97 = l_Lean_Elab_Tactic_evalIntro___closed__23;
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_array_push(x_83, x_98);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_85);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_Elab_Tactic_evalIntro___closed__25;
lean_inc(x_68);
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_68);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Elab_Tactic_evalIntro___closed__30;
lean_inc(x_68);
x_104 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_104, 0, x_68);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_array_push(x_83, x_62);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_85);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_Elab_Tactic_evalIntro___closed__31;
lean_inc(x_68);
x_108 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_108, 0, x_68);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_Elab_Tactic_evalIntro___closed__34;
lean_inc(x_68);
x_110 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_110, 0, x_68);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_Elab_Tactic_evalIntro___closed__35;
lean_inc(x_68);
x_112 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_112, 0, x_68);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_array_push(x_83, x_112);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_65);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_array_push(x_87, x_110);
x_116 = lean_array_push(x_115, x_114);
x_117 = l_Lean_Elab_Tactic_evalIntro___closed__33;
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = l_Lean_Elab_Tactic_evalIntro___closed__36;
x_120 = lean_array_push(x_119, x_104);
x_121 = lean_array_push(x_120, x_106);
x_122 = lean_array_push(x_121, x_108);
x_123 = lean_array_push(x_122, x_118);
x_124 = l_Lean_Elab_Tactic_evalIntro___closed__29;
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = lean_array_push(x_83, x_125);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_85);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_array_push(x_83, x_127);
x_129 = l_Lean_Elab_Tactic_evalIntro___closed__27;
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = l_Lean_Elab_Tactic_evalIntro___closed__37;
x_132 = lean_array_push(x_131, x_94);
x_133 = l_Lean_Elab_Tactic_evalIntro___closed__21;
x_134 = lean_array_push(x_132, x_133);
x_135 = lean_array_push(x_134, x_100);
x_136 = lean_array_push(x_135, x_133);
x_137 = lean_array_push(x_136, x_102);
x_138 = lean_array_push(x_137, x_130);
x_139 = l_Lean_Elab_Tactic_evalIntro___closed__20;
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
x_141 = l_Lean_Elab_Tactic_evalIntro___closed__40;
lean_inc(x_68);
x_142 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_142, 0, x_68);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Lean_Elab_Tactic_evalIntro___closed__43;
x_144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_144, 0, x_68);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_array_push(x_87, x_144);
x_146 = lean_array_push(x_145, x_86);
x_147 = l_Lean_Elab_Tactic_evalIntro___closed__44;
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
x_149 = lean_array_push(x_87, x_148);
x_150 = lean_array_push(x_149, x_133);
x_151 = l_Lean_Elab_Tactic_evalIntro___closed__42;
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
x_153 = lean_array_push(x_83, x_152);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_85);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_array_push(x_83, x_154);
x_156 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__2;
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = lean_array_push(x_83, x_157);
x_159 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2;
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = lean_array_push(x_87, x_142);
x_162 = lean_array_push(x_161, x_160);
x_163 = l_Lean_Elab_Tactic_evalIntro___closed__39;
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
x_165 = l_Lean_Elab_Tactic_evalIntro___closed__45;
x_166 = lean_array_push(x_165, x_90);
lean_inc(x_92);
x_167 = lean_array_push(x_166, x_92);
x_168 = lean_array_push(x_167, x_140);
x_169 = lean_array_push(x_168, x_92);
x_170 = lean_array_push(x_169, x_164);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_85);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_array_push(x_83, x_171);
x_173 = l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__2;
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_172);
x_175 = l_Lean_Elab_Tactic_evalTacticAux(x_174, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
lean_dec(x_2);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_62);
x_176 = l_Lean_Elab_Tactic_evalIntro___closed__46;
x_177 = l_Lean_Elab_Tactic_evalIntro_introStep(x_176, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = l_Lean_Syntax_getId(x_62);
lean_dec(x_62);
x_179 = l_Lean_Elab_Tactic_evalIntro_introStep(x_178, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_179;
}
}
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_15);
x_180 = l_Lean_Elab_Tactic_evalIntro___closed__46;
x_181 = l_Lean_Elab_Tactic_evalIntro_introStep(x_180, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_181;
}
}
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Tactic_evalIntro___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Tactic_evalIntro___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Tactic_evalIntro___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Tactic_evalIntro___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalIntro");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__3() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_evalIntro___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntroMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandMatchAltsIntoMatchTactic___boxed), 4, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
lean_inc(x_8);
x_14 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_15);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_adaptExpander___lambda__1___boxed), 11, 2);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_15);
x_18 = l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_adaptExpander___spec__1(x_1, x_15, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("introMatch");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalIntroMatch");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__5() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getIntrosSize_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_10 = lean_box_uint64(x_9);
x_11 = lean_apply_4(x_2, x_6, x_7, x_8, x_10);
return x_11;
}
case 8:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_17 = lean_box_uint64(x_16);
x_18 = lean_apply_5(x_3, x_12, x_13, x_14, x_15, x_17);
return x_18;
}
case 10:
{
lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_22 = lean_box_uint64(x_21);
x_23 = lean_apply_3(x_4, x_19, x_20, x_22);
return x_23;
}
default: 
{
lean_object* x_24; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_apply_1(x_5, x_1);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getIntrosSize_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getIntrosSize_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getIntrosSize(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getIntrosSize(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
return x_5;
}
case 8:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 3);
x_7 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getIntrosSize(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
return x_9;
}
case 10:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 1);
x_1 = x_10;
goto _start;
}
default: 
{
lean_object* x_12; 
x_12 = lean_unsigned_to_nat(0u);
return x_12;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getIntrosSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getIntrosSize(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_isIdent(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_evalIntro___closed__46;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_getId(x_1);
return x_4;
}
}
}
lean_object* l_Lean_Elab_Tactic_getNameOfIdent_x27___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_getNameOfIdent_x27(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntros_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Tactic_evalIntros_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntros_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalIntros___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l_Lean_Elab_Tactic_getNameOfIdent_x27(x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_get_size(x_1);
x_15 = lean_usize_of_nat(x_14);
x_16 = 0;
x_17 = x_1;
x_18 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalIntros___spec__1(x_15, x_16, x_17);
x_19 = x_18;
x_20 = lean_array_to_list(lean_box(0), x_19);
x_21 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Meta_introNCore(x_12, x_14, x_20, x_21, x_21, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_Tactic_replaceMainGoal(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
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
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
return x_28;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_28, 0);
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_28);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_39 = !lean_is_exclusive(x_22);
if (x_39 == 0)
{
return x_22;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_22, 0);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_22);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_11);
if (x_43 == 0)
{
return x_11;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_Meta_getMVarType(x_11, x_5, x_6, x_7, x_8, x_12);
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
x_16 = l_Lean_Meta_instantiateMVars(x_14, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_getIntrosSize(x_17);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Lean_Meta_introNCore(x_11, x_19, x_20, x_21, x_21, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
x_27 = l_Lean_Elab_Tactic_replaceMainGoal(x_26, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
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
lean_dec(x_8);
lean_dec(x_7);
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
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_16);
if (x_42 == 0)
{
return x_16;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_16, 0);
x_44 = lean_ctor_get(x_16, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_16);
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
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_13);
if (x_46 == 0)
{
return x_13;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_13, 0);
x_48 = lean_ctor_get(x_13, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_13);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_50 = !lean_is_exclusive(x_10);
if (x_50 == 0)
{
return x_10;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_10, 0);
x_52 = lean_ctor_get(x_10, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_10);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntros___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("intros");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntros___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l_Lean_Elab_Tactic_evalIntros___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalIntros___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntros___lambda__2___boxed), 9, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntros(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalIntros___closed__2;
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
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_nullKind;
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
x_18 = l_Lean_Syntax_isNodeOf(x_15, x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntros___lambda__1___boxed), 10, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = l_Lean_Elab_Tactic_withMainContext___rarg(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
x_22 = l_Lean_Elab_Tactic_evalIntros___closed__3;
x_23 = l_Lean_Elab_Tactic_withMainContext___rarg(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_23;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalIntros___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_evalIntros___spec__1(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalIntros___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntros___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_evalIntros___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalIntros");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__3() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_evalIntros___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_getFVarId_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Tactic_getFVarId_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getFVarId_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_getFVarId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
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
static lean_object* _init_l_Lean_Elab_Tactic_getFVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown variable '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_getFVarId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_getFVarId___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 3);
x_13 = l_Lean_replaceRef(x_1, x_12);
lean_dec(x_12);
lean_ctor_set(x_8, 3, x_13);
lean_inc(x_6);
lean_inc(x_1);
x_14 = l_Lean_Elab_Term_isLocalIdent_x3f(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_18 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Elab_Tactic_getFVarId___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__3;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Elab_Tactic_getFVarId___spec__1(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_8);
lean_dec(x_6);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
x_27 = l_Lean_Expr_fvarId_x21(x_26);
lean_dec(x_26);
lean_ctor_set(x_14, 0, x_27);
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
x_30 = l_Lean_Expr_fvarId_x21(x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 1);
x_34 = lean_ctor_get(x_8, 2);
x_35 = lean_ctor_get(x_8, 3);
x_36 = lean_ctor_get(x_8, 4);
x_37 = lean_ctor_get(x_8, 5);
x_38 = lean_ctor_get(x_8, 6);
x_39 = lean_ctor_get(x_8, 7);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
x_40 = l_Lean_replaceRef(x_1, x_35);
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
lean_inc(x_6);
lean_inc(x_1);
x_42 = l_Lean_Elab_Term_isLocalIdent_x3f(x_1, x_4, x_5, x_6, x_7, x_41, x_9, x_10);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_46 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lean_Elab_Tactic_getFVarId___closed__2;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__3;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at_Lean_Elab_Tactic_getFVarId___spec__1(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_41, x_9, x_44);
lean_dec(x_41);
lean_dec(x_6);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_41);
lean_dec(x_6);
lean_dec(x_1);
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_53 = x_42;
} else {
 lean_dec_ref(x_42);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_43, 0);
lean_inc(x_54);
lean_dec(x_43);
x_55 = l_Lean_Expr_fvarId_x21(x_54);
lean_dec(x_54);
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_53;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_getFVarId___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_getFVarId___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_getFVarIds___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_2 < x_1;
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_8);
x_14 = x_3;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_uget(x_3, x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_3, x_2, x_17);
x_19 = x_16;
lean_inc(x_10);
lean_inc(x_8);
x_20 = l_Lean_Elab_Tactic_getFVarId(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = x_2 + x_23;
x_25 = x_21;
x_26 = lean_array_uset(x_18, x_2, x_25);
x_2 = x_24;
x_3 = x_26;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_8);
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
static lean_object* _init_l_Lean_Elab_Tactic_getFVarIds___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = x_1;
x_14 = lean_box_usize(x_12);
x_15 = l_Lean_Elab_Tactic_getFVarIds___boxed__const__1;
x_16 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_getFVarIds___spec__1___boxed), 12, 3);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_13);
x_17 = x_16;
x_18 = l_Lean_Elab_Tactic_withMainContext___rarg(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_getFVarIds___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_getFVarIds___spec__1(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRevert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("revert");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalRevert___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l_Lean_Elab_Tactic_evalRevert___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_evalRevert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalRevert___closed__2;
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
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
x_17 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_20 = l_Lean_Elab_Tactic_getFVarIds(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Meta_revert(x_18, x_21, x_23, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Elab_Tactic_replaceMainGoal(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
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
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_20, 0);
x_37 = lean_ctor_get(x_20, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_20);
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
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_17, 0);
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_17);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalRevert");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__3() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_evalRevert___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_apply_1(x_5, x_9);
return x_10;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_4, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_apply_2(x_3, x_13, x_14);
return x_15;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds_match__1___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Array_qpartition_loop___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_instInhabitedName;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_1);
lean_inc(x_3);
x_12 = lean_apply_2(x_1, x_11, x_3);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_6 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_swap(x_4, x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_4 = x_17;
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
}
uint8_t l_Array_qsort_sort___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = lean_local_ctx_find(x_1, x_2);
lean_inc(x_3);
x_5 = lean_local_ctx_find(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = l_Lean_Name_quickLt(x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_7 = 1;
return x_7;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Lean_LocalDecl_index(x_10);
lean_dec(x_10);
x_12 = l_Lean_LocalDecl_index(x_9);
lean_dec(x_9);
x_13 = lean_nat_dec_lt(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
return x_13;
}
}
}
}
lean_object* l_Array_qsort_sort___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_15; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Array_qsort_sort___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__1___lambda__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_15 = lean_nat_dec_lt(x_3, x_4);
if (x_15 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_16 = lean_nat_add(x_3, x_4);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_div(x_16, x_17);
lean_dec(x_16);
x_87 = l_Lean_instInhabitedName;
x_88 = lean_array_get(x_87, x_2, x_18);
x_89 = lean_array_get(x_87, x_2, x_3);
lean_inc(x_88);
lean_inc(x_1);
x_90 = lean_local_ctx_find(x_1, x_88);
lean_inc(x_89);
lean_inc(x_1);
x_91 = lean_local_ctx_find(x_1, x_89);
if (lean_obj_tag(x_90) == 0)
{
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = l_Lean_Name_quickLt(x_88, x_89);
lean_dec(x_89);
lean_dec(x_88);
if (x_92 == 0)
{
x_19 = x_2;
goto block_86;
}
else
{
lean_object* x_93; 
x_93 = lean_array_swap(x_2, x_3, x_18);
x_19 = x_93;
goto block_86;
}
}
else
{
lean_object* x_94; 
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_88);
x_94 = lean_array_swap(x_2, x_3, x_18);
x_19 = x_94;
goto block_86;
}
}
else
{
lean_dec(x_89);
lean_dec(x_88);
if (lean_obj_tag(x_91) == 0)
{
lean_dec(x_90);
x_19 = x_2;
goto block_86;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
lean_dec(x_90);
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
lean_dec(x_91);
x_97 = l_Lean_LocalDecl_index(x_96);
lean_dec(x_96);
x_98 = l_Lean_LocalDecl_index(x_95);
lean_dec(x_95);
x_99 = lean_nat_dec_lt(x_97, x_98);
lean_dec(x_98);
lean_dec(x_97);
if (x_99 == 0)
{
x_19 = x_2;
goto block_86;
}
else
{
lean_object* x_100; 
x_100 = lean_array_swap(x_2, x_3, x_18);
x_19 = x_100;
goto block_86;
}
}
}
block_86:
{
lean_object* x_20; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_46 = l_Lean_instInhabitedName;
x_47 = lean_array_get(x_46, x_19, x_4);
x_71 = lean_array_get(x_46, x_19, x_3);
lean_inc(x_47);
lean_inc(x_1);
x_72 = lean_local_ctx_find(x_1, x_47);
lean_inc(x_71);
lean_inc(x_1);
x_73 = lean_local_ctx_find(x_1, x_71);
if (lean_obj_tag(x_72) == 0)
{
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = l_Lean_Name_quickLt(x_47, x_71);
lean_dec(x_71);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_box(0);
x_48 = x_75;
goto block_70;
}
else
{
lean_object* x_76; 
lean_dec(x_47);
x_76 = lean_box(0);
x_20 = x_76;
goto block_45;
}
}
else
{
lean_object* x_77; 
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_47);
x_77 = lean_box(0);
x_20 = x_77;
goto block_45;
}
}
else
{
lean_dec(x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_78; 
lean_dec(x_72);
x_78 = lean_box(0);
x_48 = x_78;
goto block_70;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_72, 0);
lean_inc(x_79);
lean_dec(x_72);
x_80 = lean_ctor_get(x_73, 0);
lean_inc(x_80);
lean_dec(x_73);
x_81 = l_Lean_LocalDecl_index(x_80);
lean_dec(x_80);
x_82 = l_Lean_LocalDecl_index(x_79);
lean_dec(x_79);
x_83 = lean_nat_dec_lt(x_81, x_82);
lean_dec(x_82);
lean_dec(x_81);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_box(0);
x_48 = x_84;
goto block_70;
}
else
{
lean_object* x_85; 
lean_dec(x_47);
x_85 = lean_box(0);
x_20 = x_85;
goto block_45;
}
}
}
block_45:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
x_21 = lean_array_swap(x_19, x_3, x_4);
x_22 = l_Lean_instInhabitedName;
x_23 = lean_array_get(x_22, x_21, x_18);
x_24 = lean_array_get(x_22, x_21, x_4);
lean_inc(x_23);
lean_inc(x_1);
x_25 = lean_local_ctx_find(x_1, x_23);
lean_inc(x_24);
lean_inc(x_1);
x_26 = lean_local_ctx_find(x_1, x_24);
if (lean_obj_tag(x_25) == 0)
{
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Name_quickLt(x_23, x_24);
lean_dec(x_23);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_18);
lean_inc_n(x_3, 2);
x_28 = l_Array_qpartition_loop___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__2(x_5, x_4, x_24, x_21, x_3, x_3);
x_6 = x_28;
goto block_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_24);
x_29 = lean_array_swap(x_21, x_18, x_4);
lean_dec(x_18);
x_30 = lean_array_get(x_22, x_29, x_4);
lean_inc_n(x_3, 2);
x_31 = l_Array_qpartition_loop___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__2(x_5, x_4, x_30, x_29, x_3, x_3);
x_6 = x_31;
goto block_14;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
x_32 = lean_array_swap(x_21, x_18, x_4);
lean_dec(x_18);
x_33 = lean_array_get(x_22, x_32, x_4);
lean_inc_n(x_3, 2);
x_34 = l_Array_qpartition_loop___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__2(x_5, x_4, x_33, x_32, x_3, x_3);
x_6 = x_34;
goto block_14;
}
}
else
{
lean_dec(x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_35; 
lean_dec(x_25);
lean_dec(x_18);
lean_inc_n(x_3, 2);
x_35 = l_Array_qpartition_loop___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__2(x_5, x_4, x_24, x_21, x_3, x_3);
x_6 = x_35;
goto block_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
lean_dec(x_25);
x_37 = lean_ctor_get(x_26, 0);
lean_inc(x_37);
lean_dec(x_26);
x_38 = l_Lean_LocalDecl_index(x_37);
lean_dec(x_37);
x_39 = l_Lean_LocalDecl_index(x_36);
lean_dec(x_36);
x_40 = lean_nat_dec_lt(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_18);
lean_inc_n(x_3, 2);
x_41 = l_Array_qpartition_loop___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__2(x_5, x_4, x_24, x_21, x_3, x_3);
x_6 = x_41;
goto block_14;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_24);
x_42 = lean_array_swap(x_21, x_18, x_4);
lean_dec(x_18);
x_43 = lean_array_get(x_22, x_42, x_4);
lean_inc_n(x_3, 2);
x_44 = l_Array_qpartition_loop___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__2(x_5, x_4, x_43, x_42, x_3, x_3);
x_6 = x_44;
goto block_14;
}
}
}
}
block_70:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_48);
x_49 = lean_array_get(x_46, x_19, x_18);
lean_inc(x_49);
lean_inc(x_1);
x_50 = lean_local_ctx_find(x_1, x_49);
lean_inc(x_47);
lean_inc(x_1);
x_51 = lean_local_ctx_find(x_1, x_47);
if (lean_obj_tag(x_50) == 0)
{
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = l_Lean_Name_quickLt(x_49, x_47);
lean_dec(x_49);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_18);
lean_inc_n(x_3, 2);
x_53 = l_Array_qpartition_loop___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__2(x_5, x_4, x_47, x_19, x_3, x_3);
x_6 = x_53;
goto block_14;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_47);
x_54 = lean_array_swap(x_19, x_18, x_4);
lean_dec(x_18);
x_55 = lean_array_get(x_46, x_54, x_4);
lean_inc_n(x_3, 2);
x_56 = l_Array_qpartition_loop___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__2(x_5, x_4, x_55, x_54, x_3, x_3);
x_6 = x_56;
goto block_14;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_47);
x_57 = lean_array_swap(x_19, x_18, x_4);
lean_dec(x_18);
x_58 = lean_array_get(x_46, x_57, x_4);
lean_inc_n(x_3, 2);
x_59 = l_Array_qpartition_loop___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__2(x_5, x_4, x_58, x_57, x_3, x_3);
x_6 = x_59;
goto block_14;
}
}
else
{
lean_dec(x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_60; 
lean_dec(x_50);
lean_dec(x_18);
lean_inc_n(x_3, 2);
x_60 = l_Array_qpartition_loop___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__2(x_5, x_4, x_47, x_19, x_3, x_3);
x_6 = x_60;
goto block_14;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_50, 0);
lean_inc(x_61);
lean_dec(x_50);
x_62 = lean_ctor_get(x_51, 0);
lean_inc(x_62);
lean_dec(x_51);
x_63 = l_Lean_LocalDecl_index(x_62);
lean_dec(x_62);
x_64 = l_Lean_LocalDecl_index(x_61);
lean_dec(x_61);
x_65 = lean_nat_dec_lt(x_63, x_64);
lean_dec(x_64);
lean_dec(x_63);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_18);
lean_inc_n(x_3, 2);
x_66 = l_Array_qpartition_loop___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__2(x_5, x_4, x_47, x_19, x_3, x_3);
x_6 = x_66;
goto block_14;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_47);
x_67 = lean_array_swap(x_19, x_18, x_4);
lean_dec(x_18);
x_68 = lean_array_get(x_46, x_67, x_4);
lean_inc_n(x_3, 2);
x_69 = l_Array_qpartition_loop___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__2(x_5, x_4, x_68, x_67, x_3, x_3);
x_6 = x_69;
goto block_14;
}
}
}
}
}
}
block_14:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_4, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_10 = l_Array_qsort_sort___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__1(x_1, x_8, x_3, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_2 = x_10;
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_array_get_size(x_1);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_qsort_sort___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__1(x_11, x_1, x_15, x_14);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___lambda__1___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_withMainContext___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Array_qpartition_loop___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qpartition_loop___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_qsort_sort___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_qsort_sort___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__1___lambda__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Array_qsort_sort___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_qsort_sort___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalClear___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l_Lean_Meta_clear(x_12, x_1, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Elab_Tactic_replaceMainGoal(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalClear___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_3 < x_2;
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_16 = lean_array_uget(x_1, x_3);
x_17 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalClear___spec__1___lambda__1___boxed), 10, 1);
lean_closure_set(x_17, 0, x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Elab_Tactic_withMainContext___rarg(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 1;
x_21 = x_3 + x_20;
x_22 = lean_box(0);
x_3 = x_21;
x_4 = x_22;
x_13 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalClear(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalIntro___closed__44;
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
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_Elab_Tactic_getFVarIds(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_get_size(x_21);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = lean_box(0);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalClear___spec__1(x_21, x_24, x_25, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
lean_dec(x_21);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
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
x_36 = !lean_is_exclusive(x_20);
if (x_36 == 0)
{
return x_20;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_20, 0);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_20);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_17);
if (x_40 == 0)
{
return x_17;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = lean_ctor_get(x_17, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_17);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalClear___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalClear___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalClear___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_evalClear___spec__1(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_16;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalClear");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__3() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_evalIntro___closed__44;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_forEachVar___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_1);
x_12 = l_Lean_Elab_Tactic_getFVarId(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_7);
x_17 = l_Lean_Elab_Tactic_getFVarId(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_20 = lean_apply_7(x_2, x_15, x_18, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_Tactic_replaceMainGoal(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
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
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
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
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_forEachVar___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = x_4 < x_3;
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
x_17 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_forEachVar___spec__1___lambda__1___boxed), 11, 2);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Elab_Tactic_withMainContext___rarg(x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = 1;
x_22 = x_4 + x_21;
x_23 = lean_box(0);
x_4 = x_22;
x_5 = x_23;
x_14 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_forEachVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = lean_box(0);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_forEachVar___spec__1(x_2, x_1, x_13, x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_forEachVar___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_forEachVar___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_forEachVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_forEachVar___spec__1(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_17;
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
static lean_object* _init_l_Lean_Elab_Tactic_evalSubst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("subst");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSubst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l_Lean_Elab_Tactic_evalSubst___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSubst___closed__3() {
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
x_11 = l_Lean_Elab_Tactic_evalSubst___closed__2;
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
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
x_17 = l_Lean_Elab_Tactic_evalSubst___closed__3;
x_18 = l_Lean_Elab_Tactic_forEachVar(x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_16);
return x_18;
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalSubst");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__3() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_evalSubst___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_findM_x3f___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_16 = l_Lean_Meta_getMVarDecl(x_14, x_7, x_8, x_9, x_10, x_11);
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
x_21 = l_Lean_Name_isSuffixOf(x_1, x_20);
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
x_27 = l_Lean_Name_isSuffixOf(x_1, x_26);
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
lean_object* l_List_findM_x3f___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_16 = l_Lean_Meta_getMVarDecl(x_14, x_7, x_8, x_9, x_10, x_11);
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
x_21 = l_Lean_Name_isPrefixOf(x_1, x_20);
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
x_27 = l_Lean_Name_isPrefixOf(x_1, x_26);
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
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_1);
x_12 = l_List_findM_x3f___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f___spec__1(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_15 = l_List_findM_x3f___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f___spec__2(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
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
lean_object* l_List_findM_x3f___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_findM_x3f___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_List_findM_x3f___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_findM_x3f___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_Elab_Tactic_withCaseRef___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_replaceRef(x_1, x_4);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_3(x_6, lean_box(0), x_5, x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_Tactic_withCaseRef___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Lean_Elab_Tactic_evalIntro___closed__6;
x_7 = lean_array_push(x_6, x_3);
x_8 = lean_array_push(x_7, x_4);
x_9 = l_Lean_nullKind;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withCaseRef___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_5);
x_14 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Elab_Tactic_withCaseRef(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withCaseRef___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_withCaseRef___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_withCaseRef___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalCase_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Tactic_evalCase_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCase_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalCase_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Tactic_evalCase_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCase_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalCase_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Tactic_evalCase_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCase_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_erase___at_Lean_Elab_Tactic_evalCase___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_name_eq(x_5, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_List_erase___at_Lean_Elab_Tactic_evalCase___spec__1(x_6, x_2);
lean_ctor_set(x_1, 1, x_8);
return x_1;
}
else
{
lean_free_object(x_1);
lean_dec(x_5);
return x_6;
}
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_name_eq(x_9, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_List_erase___at_Lean_Elab_Tactic_evalCase___spec__1(x_10, x_2);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_dec(x_9);
return x_10;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalCase___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = l_Lean_Elab_Tactic_evalIntro___closed__6;
x_14 = lean_array_push(x_13, x_1);
x_15 = lean_array_push(x_14, x_2);
x_16 = l_Lean_nullKind;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 3);
x_20 = l_Lean_replaceRef(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
lean_ctor_set(x_10, 3, x_20);
x_21 = lean_apply_9(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
x_25 = lean_ctor_get(x_10, 3);
x_26 = lean_ctor_get(x_10, 4);
x_27 = lean_ctor_get(x_10, 5);
x_28 = lean_ctor_get(x_10, 6);
x_29 = lean_ctor_get(x_10, 7);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_30 = l_Lean_replaceRef(x_17, x_25);
lean_dec(x_25);
lean_dec(x_17);
x_31 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_31, 4, x_26);
lean_ctor_set(x_31, 5, x_27);
lean_ctor_set(x_31, 6, x_28);
lean_ctor_set(x_31, 7, x_29);
x_32 = lean_apply_9(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_31, x_11, x_12);
return x_32;
}
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_pop(x_2);
x_14 = l_Array_isEmpty___rarg(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3___lambda__1___boxed), 12, 0);
return x_1;
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_nat_dec_le(x_15, x_4);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_3, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_3, x_19);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
x_24 = lean_nat_sub(x_1, x_4);
x_25 = lean_nat_sub(x_24, x_19);
lean_dec(x_24);
lean_inc(x_22);
x_26 = lean_local_ctx_get(x_22, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_nat_add(x_4, x_27);
lean_dec(x_4);
x_3 = x_20;
x_4 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_31 = l_Lean_LocalDecl_userName(x_30);
x_32 = l_Lean_Name_hasMacroScopes(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_30);
x_33 = lean_ctor_get(x_2, 2);
x_34 = lean_nat_add(x_4, x_33);
lean_dec(x_4);
x_3 = x_20;
x_4 = x_34;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_free_object(x_5);
x_36 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_23);
x_37 = l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3___closed__1;
x_38 = l_Lean_Syntax_isIdent(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_30);
x_39 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_40 = lean_apply_12(x_37, x_22, x_23, x_39, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
lean_ctor_set(x_40, 0, x_44);
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_dec(x_40);
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
lean_dec(x_41);
x_50 = lean_ctor_get(x_2, 2);
x_51 = lean_nat_add(x_4, x_50);
lean_dec(x_4);
x_3 = x_20;
x_4 = x_51;
x_5 = x_49;
x_14 = x_48;
goto _start;
}
}
else
{
uint8_t x_53; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_40);
if (x_53 == 0)
{
return x_40;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_40, 0);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_40);
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
x_57 = l_Lean_Syntax_getId(x_36);
lean_dec(x_36);
x_58 = l_Lean_LocalDecl_fvarId(x_30);
lean_dec(x_30);
x_59 = l_Lean_LocalContext_setUserName(x_22, x_58, x_57);
x_60 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_61 = lean_apply_12(x_37, x_59, x_23, x_60, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
lean_dec(x_62);
lean_ctor_set(x_61, 0, x_65);
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_dec(x_61);
x_67 = lean_ctor_get(x_62, 0);
lean_inc(x_67);
lean_dec(x_62);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_61, 1);
lean_inc(x_69);
lean_dec(x_61);
x_70 = lean_ctor_get(x_62, 0);
lean_inc(x_70);
lean_dec(x_62);
x_71 = lean_ctor_get(x_2, 2);
x_72 = lean_nat_add(x_4, x_71);
lean_dec(x_4);
x_3 = x_20;
x_4 = x_72;
x_5 = x_70;
x_14 = x_69;
goto _start;
}
}
else
{
uint8_t x_74; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_74 = !lean_is_exclusive(x_61);
if (x_74 == 0)
{
return x_61;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_61, 0);
x_76 = lean_ctor_get(x_61, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_61);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_5, 0);
x_79 = lean_ctor_get(x_5, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_5);
x_80 = lean_nat_sub(x_1, x_4);
x_81 = lean_nat_sub(x_80, x_19);
lean_dec(x_80);
lean_inc(x_78);
x_82 = lean_local_ctx_get(x_78, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_78);
lean_ctor_set(x_83, 1, x_79);
x_84 = lean_ctor_get(x_2, 2);
x_85 = lean_nat_add(x_4, x_84);
lean_dec(x_4);
x_3 = x_20;
x_4 = x_85;
x_5 = x_83;
goto _start;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_82, 0);
lean_inc(x_87);
lean_dec(x_82);
x_88 = l_Lean_LocalDecl_userName(x_87);
x_89 = l_Lean_Name_hasMacroScopes(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_87);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_78);
lean_ctor_set(x_90, 1, x_79);
x_91 = lean_ctor_get(x_2, 2);
x_92 = lean_nat_add(x_4, x_91);
lean_dec(x_4);
x_3 = x_20;
x_4 = x_92;
x_5 = x_90;
goto _start;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_79);
x_95 = l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3___closed__1;
x_96 = l_Lean_Syntax_isIdent(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_94);
lean_dec(x_87);
x_97 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_98 = lean_apply_12(x_95, x_78, x_79, x_97, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
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
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
lean_dec(x_99);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
lean_dec(x_98);
x_105 = lean_ctor_get(x_99, 0);
lean_inc(x_105);
lean_dec(x_99);
x_106 = lean_ctor_get(x_2, 2);
x_107 = lean_nat_add(x_4, x_106);
lean_dec(x_4);
x_3 = x_20;
x_4 = x_107;
x_5 = x_105;
x_14 = x_104;
goto _start;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_109 = lean_ctor_get(x_98, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_98, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_111 = x_98;
} else {
 lean_dec_ref(x_98);
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
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = l_Lean_Syntax_getId(x_94);
lean_dec(x_94);
x_114 = l_Lean_LocalDecl_fvarId(x_87);
lean_dec(x_87);
x_115 = l_Lean_LocalContext_setUserName(x_78, x_114, x_113);
x_116 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_117 = lean_apply_12(x_95, x_115, x_79, x_116, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
lean_dec(x_118);
if (lean_is_scalar(x_120)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_120;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_119);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_117, 1);
lean_inc(x_123);
lean_dec(x_117);
x_124 = lean_ctor_get(x_118, 0);
lean_inc(x_124);
lean_dec(x_118);
x_125 = lean_ctor_get(x_2, 2);
x_126 = lean_nat_add(x_4, x_125);
lean_dec(x_4);
x_3 = x_20;
x_4 = x_126;
x_5 = x_124;
x_14 = x_123;
goto _start;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_128 = lean_ctor_get(x_117, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_117, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_130 = x_117;
} else {
 lean_dec_ref(x_117);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
}
}
}
else
{
lean_object* x_132; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_5);
lean_ctor_set(x_132, 1, x_14);
return x_132;
}
}
else
{
lean_object* x_133; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_5);
lean_ctor_set(x_133, 1, x_14);
return x_133;
}
}
}
lean_object* l_Lean_Elab_Tactic_evalCase___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_box(0);
lean_inc(x_5);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Tactic_setGoals(x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_5);
x_20 = l_Lean_Meta_getMVarTag(x_5, x_11, x_12, x_13, x_14, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
lean_inc(x_5);
x_24 = l_Lean_Meta_setMVarTag(x_5, x_23, x_11, x_12, x_13, x_14, x_22);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_1);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(x_26, 0, x_1);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withTacticInfoContext___rarg), 11, 2);
lean_closure_set(x_27, 0, x_2);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_closeUsingOrAdmit), 10, 1);
lean_closure_set(x_28, 0, x_27);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_29 = l_Lean_Elab_Tactic_withCaseRef___at_Lean_Elab_Tactic_evalCase___spec__2(x_3, x_1, x_28, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Meta_setMVarTag(x_5, x_21, x_11, x_12, x_13, x_14, x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_33 = l_Lean_Elab_Tactic_done(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Elab_Tactic_setGoals(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_34);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
x_42 = l_Lean_Meta_setMVarTag(x_5, x_21, x_11, x_12, x_13, x_14, x_41);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 0, x_40);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_20);
if (x_47 == 0)
{
return x_20;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_20, 0);
x_49 = lean_ctor_get(x_20, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_20);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalCase___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = 2;
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Meta_mkFreshExprMVarAt(x_2, x_15, x_16, x_18, x_17, x_19, x_10, x_11, x_12, x_13, x_14);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_21);
x_23 = l_Lean_Meta_assignExprMVar(x_4, x_21, x_10, x_11, x_12, x_13, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Expr_mvarId_x21(x_21);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_apply_11(x_3, x_25, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_24);
return x_27;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalCase___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("case");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalCase___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l_Lean_Elab_Tactic_evalCase___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalCase___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tag not found");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalCase___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalCase___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalCase___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many variable names provided at 'case'");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalCase___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalCase___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalCase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalCase___closed__2;
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
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = lean_unsigned_to_nat(4u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
x_22 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2;
lean_inc(x_21);
x_23 = l_Lean_Syntax_isOfKind(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalChoiceAux___spec__1___rarg(x_10);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_26 = l_Lean_Syntax_getId(x_15);
lean_dec(x_15);
x_27 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_28);
x_30 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_findTag_x3f(x_28, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_1);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Tactic_evalCase___closed__4;
x_34 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___spec__2(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
x_37 = l_List_erase___at_Lean_Elab_Tactic_evalCase___spec__1(x_28, x_36);
lean_inc(x_37);
lean_inc(x_19);
lean_inc(x_1);
lean_inc(x_21);
x_38 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalCase___lambda__1___boxed), 15, 4);
lean_closure_set(x_38, 0, x_21);
lean_closure_set(x_38, 1, x_1);
lean_closure_set(x_38, 2, x_19);
lean_closure_set(x_38, 3, x_37);
x_39 = l_Array_isEmpty___rarg(x_25);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_37);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_1);
lean_inc(x_36);
x_40 = l_Lean_Meta_getMVarDecl(x_36, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_inc(x_43);
x_44 = lean_local_ctx_num_indices(x_43);
x_45 = lean_unsigned_to_nat(0u);
lean_inc(x_44);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_14);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_25);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_44);
x_48 = l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3(x_44, x_46, x_44, x_45, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_46);
lean_dec(x_44);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l_Array_isEmpty___rarg(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = l_Lean_Elab_Tactic_evalCase___closed__6;
x_55 = 2;
x_56 = l_Lean_Elab_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(x_54, x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Elab_Tactic_evalCase___lambda__2(x_41, x_51, x_38, x_36, x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_58);
lean_dec(x_57);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_box(0);
x_61 = l_Lean_Elab_Tactic_evalCase___lambda__2(x_41, x_51, x_38, x_36, x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_48);
if (x_62 == 0)
{
return x_48;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_48, 0);
x_64 = lean_ctor_get(x_48, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_48);
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
lean_dec(x_36);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_40);
if (x_66 == 0)
{
return x_40;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_40, 0);
x_68 = lean_ctor_get(x_40, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_40);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_38);
lean_dec(x_25);
x_70 = lean_box(0);
x_71 = l_Lean_Elab_Tactic_evalCase___lambda__1(x_21, x_1, x_19, x_37, x_36, x_70, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_30);
if (x_72 == 0)
{
return x_30;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_30, 0);
x_74 = lean_ctor_get(x_30, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_30);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
}
lean_object* l_List_erase___at_Lean_Elab_Tactic_evalCase___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_erase___at_Lean_Elab_Tactic_evalCase___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
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
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Lean_Elab_Tactic_evalCase___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Tactic_evalCase___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
return x_16;
}
}
lean_object* l_Lean_Elab_Tactic_evalCase___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_evalCase___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_15;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalCase");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__3() {
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Elab_Tactic_evalCase___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_evalFirst_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_12, x_13);
lean_dec(x_12);
x_15 = lean_nat_dec_eq(x_2, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = l_Lean_instInhabitedSyntax;
x_17 = lean_array_get(x_16, x_1, x_2);
x_18 = l_Lean_Syntax_getArg(x_17, x_13);
lean_dec(x_17);
x_19 = lean_nat_add(x_2, x_13);
lean_dec(x_2);
x_20 = l_Lean_Elab_Tactic_saveState___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Elab_Tactic_evalTacticAux(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_Tactic_SavedState_restore(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_2 = x_19;
x_11 = x_26;
goto _start;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = l_Lean_instInhabitedSyntax;
x_29 = lean_array_get(x_28, x_1, x_2);
lean_dec(x_2);
x_30 = l_Lean_Syntax_getArg(x_29, x_13);
lean_dec(x_29);
x_31 = l_Lean_Elab_Tactic_evalTacticAux(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_31;
}
}
}
lean_object* l_Lean_Elab_Tactic_evalFirst_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalFirst_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalFirst___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__7___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalFirst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalFirst___spec__1___rarg), 1, 0);
return x_9;
}
}
lean_object* l_Lean_Elab_Tactic_evalFirst___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Elab_Tactic_evalFirst_loop(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_evalFirst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
x_14 = l_Array_isEmpty___rarg(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Elab_Tactic_evalFirst_loop(x_13, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_13);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalFirst___spec__1___rarg(x_10);
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalFirst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalFirst___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Elab_Tactic_evalFirst___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalFirst___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_evalFirst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalFirst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("first");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__14;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalFirst");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalFirst___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalFirst(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_5545____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__3;
x_2 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_5545_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_5545____closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_CollectMVars(lean_object*);
lean_object* initialize_Lean_Parser_Command(lean_object*);
lean_object* initialize_Lean_Meta_PPGoal(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assumption(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Contradiction(lean_object*);
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
res = initialize_Lean_Parser_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_PPGoal(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Contradiction(lean_io_mk_world());
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
l_Lean_Elab_goalsToMessageData___closed__2 = _init_l_Lean_Elab_goalsToMessageData___closed__2();
lean_mark_persistent(l_Lean_Elab_goalsToMessageData___closed__2);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__1 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__1);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__2 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__2);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__3 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__3);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__4 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__4);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__5 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__5);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__6 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__6);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__7 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__7);
l_Lean_Elab_Term_reportUnsolvedGoals___closed__8 = _init_l_Lean_Elab_Term_reportUnsolvedGoals___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_reportUnsolvedGoals___closed__8);
l_Lean_Elab_Tactic_instInhabitedState = _init_l_Lean_Elab_Tactic_instInhabitedState();
lean_mark_persistent(l_Lean_Elab_Tactic_instInhabitedState);
l_Lean_Elab_Tactic_instMonadTacticM___closed__1 = _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM___closed__1);
l_Lean_Elab_Tactic_instMonadTacticM___closed__2 = _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM___closed__2);
l_Lean_Elab_Tactic_instMonadTacticM___closed__3 = _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM___closed__3);
l_Lean_Elab_Tactic_instMonadTacticM___closed__4 = _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM___closed__4);
l_Lean_Elab_Tactic_instMonadTacticM___closed__5 = _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM___closed__5);
l_Lean_Elab_Tactic_instMonadTacticM___closed__6 = _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM___closed__6);
l_Lean_Elab_Tactic_instMonadTacticM___closed__7 = _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM___closed__7);
l_Lean_Elab_Tactic_instMonadTacticM___closed__8 = _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM___closed__8);
l_Lean_Elab_Tactic_instMonadTacticM___closed__9 = _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM___closed__9);
l_Lean_Elab_Tactic_instMonadTacticM___closed__10 = _init_l_Lean_Elab_Tactic_instMonadTacticM___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM___closed__10);
l_Lean_Elab_Tactic_instMonadTacticM = _init_l_Lean_Elab_Tactic_instMonadTacticM();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadTacticM);
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
l_Lean_Elab_Tactic_mkTacticAttribute___closed__8 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__8);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__9 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__9);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__10 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__10);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__11 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__11);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__12 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__12);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__13 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__13);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__14 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__14);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__15 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__15);
l_Lean_Elab_Tactic_tacticElabAttribute___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___lambda__1___closed__1);
l_Lean_Elab_Tactic_tacticElabAttribute___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___lambda__1___closed__2);
l_Lean_Elab_Tactic_tacticElabAttribute___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___lambda__2___closed__1();
l_Lean_Elab_Tactic_tacticElabAttribute___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___lambda__2___closed__2);
l_Lean_Elab_Tactic_tacticElabAttribute___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___lambda__4___closed__1);
l_Lean_Elab_Tactic_tacticElabAttribute___lambda__7___closed__1 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___lambda__7___closed__1);
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
l_Lean_Elab_Tactic_tacticElabAttribute___closed__6 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__6);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__7 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__7);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__8 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__8);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__9 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__9);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__10 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__10);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__11 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__11);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__12 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__12);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__13 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__13);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__14 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__14);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__15 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__15);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__16 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__16();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__16);
res = l_Lean_Elab_Tactic_mkTacticAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_tacticElabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute);
lean_dec_ref(res);
l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__1 = _init_l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__1);
l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__2 = _init_l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__2);
l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__3 = _init_l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg___closed__3);
l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___closed__1 = _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___closed__1);
l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___closed__2 = _init_l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_evalTacticUsing_loop___closed__2);
l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__1 = _init_l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__1);
l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__2 = _init_l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__2);
l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__3 = _init_l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__3);
l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__4 = _init_l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__4();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3___closed__4);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__7___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__7___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__7___rarg___closed__1);
l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__1 = _init_l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__1);
l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__2 = _init_l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__2);
l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__3 = _init_l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__3);
l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__4 = _init_l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_expandTacticMacroFns_loop___closed__4);
l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__1);
l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__2);
l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__3);
l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__4);
l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__5 = _init_l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__5);
l_Lean_Elab_Tactic_evalTacticAux___closed__1 = _init_l_Lean_Elab_Tactic_evalTacticAux___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTacticAux___closed__1);
l_Lean_Elab_Tactic_evalTacticAux___closed__2 = _init_l_Lean_Elab_Tactic_evalTacticAux___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTacticAux___closed__2);
l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__1 = _init_l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__1);
l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__2 = _init_l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_throwNoGoalsToBeSolved___rarg___closed__2);
l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwAbortTactic___at_Lean_Elab_Tactic_done___spec__1___rarg___closed__1);
l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__1 = _init_l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__1);
l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__2 = _init_l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_logException___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__1___closed__2);
l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__1 = _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__1);
l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__2 = _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__2);
l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__3 = _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM___closed__3);
l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM = _init_l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadBacktrackSavedStateTacticM);
l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__1 = _init_l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__1);
l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__2 = _init_l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__2);
l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__3 = _init_l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM___closed__3);
l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM = _init_l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM();
lean_mark_persistent(l_Lean_Elab_Tactic_instMonadExceptExceptionTacticM);
l_Lean_Elab_Tactic_instOrElseTacticM___closed__1 = _init_l_Lean_Elab_Tactic_instOrElseTacticM___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_instOrElseTacticM___closed__1);
l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1 = _init_l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_ensureHasNoMVars___closed__1);
l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2 = _init_l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_ensureHasNoMVars___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalDone(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___closed__1 = _init_l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Tactic_tagUntaggedGoals___spec__2___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSeq1___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalSeq1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalParen___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalParen(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq1Indented(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFocus___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalFocus(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalRotateLeft(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRotateRight___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalRotateRight(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5___closed__1 = _init_l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5___closed__1();
lean_mark_persistent(l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5___closed__1);
l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5___closed__2 = _init_l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5___closed__2();
lean_mark_persistent(l_Lean_resolveNamespace___at_Lean_Elab_Tactic_evalOpen___spec__5___closed__2);
l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__1 = _init_l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__1();
lean_mark_persistent(l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__1);
l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__2 = _init_l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__2();
lean_mark_persistent(l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__2);
l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__3 = _init_l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__3();
lean_mark_persistent(l_Lean_Elab_logUnknownDecl___at_Lean_Elab_Tactic_evalOpen___spec__7___closed__3);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__1 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__1();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__1);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__2 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__2();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__2);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__3 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__3();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__3);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__4 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__4();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__4);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__5 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__5();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__5);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__6 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__6();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__6);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__7 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__7();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__7);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__8 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__8();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__8);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__9 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__9();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Tactic_evalOpen___spec__3___closed__9);
l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalOpen___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalOpen(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___closed__1 = _init_l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___closed__1();
lean_mark_persistent(l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___closed__1);
l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___closed__2 = _init_l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___closed__2();
lean_mark_persistent(l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Tactic_elabSetOption___spec__6___closed__2);
l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__1 = _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__1);
l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__2 = _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__2);
l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__3 = _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__3();
lean_mark_persistent(l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__3);
l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__4 = _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__4();
lean_mark_persistent(l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__4);
l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__5 = _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__5();
lean_mark_persistent(l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__5);
l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__6 = _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__6();
lean_mark_persistent(l_Lean_Elab_elabSetOption___at_Lean_Elab_Tactic_elabSetOption___spec__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__1);
l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__2);
l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__3);
l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__4);
l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabSetOption___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_elabSetOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalAllGoals___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalAllGoals(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalChoice___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalChoice(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSkip___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalSkip(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalUnknown___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalUnknown(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalFailIfSuccess___closed__1 = _init_l_Lean_Elab_Tactic_evalFailIfSuccess___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalFailIfSuccess___closed__1);
l_Lean_Elab_Tactic_evalFailIfSuccess___closed__2 = _init_l_Lean_Elab_Tactic_evalFailIfSuccess___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalFailIfSuccess___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalFailIfSuccess(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalTraceState___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalTraceState(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalAssumption___rarg___closed__1 = _init_l_Lean_Elab_Tactic_evalAssumption___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalAssumption___rarg___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalAssumption___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalAssumption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalContradiction___rarg___closed__1 = _init_l_Lean_Elab_Tactic_evalContradiction___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalContradiction___rarg___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalContradiction___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalContradiction(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Lean_Elab_Tactic_evalIntro___closed__10 = _init_l_Lean_Elab_Tactic_evalIntro___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__10);
l_Lean_Elab_Tactic_evalIntro___closed__11 = _init_l_Lean_Elab_Tactic_evalIntro___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__11);
l_Lean_Elab_Tactic_evalIntro___closed__12 = _init_l_Lean_Elab_Tactic_evalIntro___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__12);
l_Lean_Elab_Tactic_evalIntro___closed__13 = _init_l_Lean_Elab_Tactic_evalIntro___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__13);
l_Lean_Elab_Tactic_evalIntro___closed__14 = _init_l_Lean_Elab_Tactic_evalIntro___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__14);
l_Lean_Elab_Tactic_evalIntro___closed__15 = _init_l_Lean_Elab_Tactic_evalIntro___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__15);
l_Lean_Elab_Tactic_evalIntro___closed__16 = _init_l_Lean_Elab_Tactic_evalIntro___closed__16();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__16);
l_Lean_Elab_Tactic_evalIntro___closed__17 = _init_l_Lean_Elab_Tactic_evalIntro___closed__17();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__17);
l_Lean_Elab_Tactic_evalIntro___closed__18 = _init_l_Lean_Elab_Tactic_evalIntro___closed__18();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__18);
l_Lean_Elab_Tactic_evalIntro___closed__19 = _init_l_Lean_Elab_Tactic_evalIntro___closed__19();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__19);
l_Lean_Elab_Tactic_evalIntro___closed__20 = _init_l_Lean_Elab_Tactic_evalIntro___closed__20();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__20);
l_Lean_Elab_Tactic_evalIntro___closed__21 = _init_l_Lean_Elab_Tactic_evalIntro___closed__21();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__21);
l_Lean_Elab_Tactic_evalIntro___closed__22 = _init_l_Lean_Elab_Tactic_evalIntro___closed__22();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__22);
l_Lean_Elab_Tactic_evalIntro___closed__23 = _init_l_Lean_Elab_Tactic_evalIntro___closed__23();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__23);
l_Lean_Elab_Tactic_evalIntro___closed__24 = _init_l_Lean_Elab_Tactic_evalIntro___closed__24();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__24);
l_Lean_Elab_Tactic_evalIntro___closed__25 = _init_l_Lean_Elab_Tactic_evalIntro___closed__25();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__25);
l_Lean_Elab_Tactic_evalIntro___closed__26 = _init_l_Lean_Elab_Tactic_evalIntro___closed__26();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__26);
l_Lean_Elab_Tactic_evalIntro___closed__27 = _init_l_Lean_Elab_Tactic_evalIntro___closed__27();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__27);
l_Lean_Elab_Tactic_evalIntro___closed__28 = _init_l_Lean_Elab_Tactic_evalIntro___closed__28();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__28);
l_Lean_Elab_Tactic_evalIntro___closed__29 = _init_l_Lean_Elab_Tactic_evalIntro___closed__29();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__29);
l_Lean_Elab_Tactic_evalIntro___closed__30 = _init_l_Lean_Elab_Tactic_evalIntro___closed__30();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__30);
l_Lean_Elab_Tactic_evalIntro___closed__31 = _init_l_Lean_Elab_Tactic_evalIntro___closed__31();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__31);
l_Lean_Elab_Tactic_evalIntro___closed__32 = _init_l_Lean_Elab_Tactic_evalIntro___closed__32();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__32);
l_Lean_Elab_Tactic_evalIntro___closed__33 = _init_l_Lean_Elab_Tactic_evalIntro___closed__33();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__33);
l_Lean_Elab_Tactic_evalIntro___closed__34 = _init_l_Lean_Elab_Tactic_evalIntro___closed__34();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__34);
l_Lean_Elab_Tactic_evalIntro___closed__35 = _init_l_Lean_Elab_Tactic_evalIntro___closed__35();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__35);
l_Lean_Elab_Tactic_evalIntro___closed__36 = _init_l_Lean_Elab_Tactic_evalIntro___closed__36();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__36);
l_Lean_Elab_Tactic_evalIntro___closed__37 = _init_l_Lean_Elab_Tactic_evalIntro___closed__37();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__37);
l_Lean_Elab_Tactic_evalIntro___closed__38 = _init_l_Lean_Elab_Tactic_evalIntro___closed__38();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__38);
l_Lean_Elab_Tactic_evalIntro___closed__39 = _init_l_Lean_Elab_Tactic_evalIntro___closed__39();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__39);
l_Lean_Elab_Tactic_evalIntro___closed__40 = _init_l_Lean_Elab_Tactic_evalIntro___closed__40();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__40);
l_Lean_Elab_Tactic_evalIntro___closed__41 = _init_l_Lean_Elab_Tactic_evalIntro___closed__41();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__41);
l_Lean_Elab_Tactic_evalIntro___closed__42 = _init_l_Lean_Elab_Tactic_evalIntro___closed__42();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__42);
l_Lean_Elab_Tactic_evalIntro___closed__43 = _init_l_Lean_Elab_Tactic_evalIntro___closed__43();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__43);
l_Lean_Elab_Tactic_evalIntro___closed__44 = _init_l_Lean_Elab_Tactic_evalIntro___closed__44();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__44);
l_Lean_Elab_Tactic_evalIntro___closed__45 = _init_l_Lean_Elab_Tactic_evalIntro___closed__45();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__45);
l_Lean_Elab_Tactic_evalIntro___closed__46 = _init_l_Lean_Elab_Tactic_evalIntro___closed__46();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__46);
l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalIntro___closed__3);
res = l___regBuiltin_Lean_Elab_Tactic_evalIntro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalIntroMatch(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalIntros___closed__1 = _init_l_Lean_Elab_Tactic_evalIntros___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntros___closed__1);
l_Lean_Elab_Tactic_evalIntros___closed__2 = _init_l_Lean_Elab_Tactic_evalIntros___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntros___closed__2);
l_Lean_Elab_Tactic_evalIntros___closed__3 = _init_l_Lean_Elab_Tactic_evalIntros___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntros___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalIntros___closed__3);
res = l___regBuiltin_Lean_Elab_Tactic_evalIntros(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_getFVarId___closed__1 = _init_l_Lean_Elab_Tactic_getFVarId___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_getFVarId___closed__1);
l_Lean_Elab_Tactic_getFVarId___closed__2 = _init_l_Lean_Elab_Tactic_getFVarId___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_getFVarId___closed__2);
l_Lean_Elab_Tactic_getFVarIds___boxed__const__1 = _init_l_Lean_Elab_Tactic_getFVarIds___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Tactic_getFVarIds___boxed__const__1);
l_Lean_Elab_Tactic_evalRevert___closed__1 = _init_l_Lean_Elab_Tactic_evalRevert___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRevert___closed__1);
l_Lean_Elab_Tactic_evalRevert___closed__2 = _init_l_Lean_Elab_Tactic_evalRevert___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRevert___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRevert___closed__3);
res = l___regBuiltin_Lean_Elab_Tactic_evalRevert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalClear___closed__3);
res = l___regBuiltin_Lean_Elab_Tactic_evalClear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalSubst___closed__1 = _init_l_Lean_Elab_Tactic_evalSubst___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSubst___closed__1);
l_Lean_Elab_Tactic_evalSubst___closed__2 = _init_l_Lean_Elab_Tactic_evalSubst___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSubst___closed__2);
l_Lean_Elab_Tactic_evalSubst___closed__3 = _init_l_Lean_Elab_Tactic_evalSubst___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSubst___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSubst___closed__3);
res = l___regBuiltin_Lean_Elab_Tactic_evalSubst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalCase___spec__3___closed__1);
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
l_Lean_Elab_Tactic_evalCase___closed__6 = _init_l_Lean_Elab_Tactic_evalCase___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalCase___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalCase___closed__3);
res = l___regBuiltin_Lean_Elab_Tactic_evalCase(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalFirst___closed__5);
res = l___regBuiltin_Lean_Elab_Tactic_evalFirst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_5545____closed__1 = _init_l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_5545____closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_5545____closed__1);
res = l_Lean_Elab_Tactic_initFn____x40_Lean_Elab_Tactic_Basic___hyg_5545_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
