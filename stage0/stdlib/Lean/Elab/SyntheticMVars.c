// Lean compiler output
// Module: Lean.Elab.SyntheticMVars
// Imports: Init Lean.Util.ForEachExpr Lean.Elab.Term Lean.Elab.Tactic.Basic
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
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__1;
lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___closed__3;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__2;
extern lean_object* l_Lean_Syntax_strLitToAtom___closed__3;
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_logException___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshLevelMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar_match__1(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Elab_Term_runTactic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault___closed__1;
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg___closed__1;
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__2(uint8_t);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAndSynthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_formatDataValue___closed__1;
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault_match__3___rarg(lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__1;
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_logException___rarg___lambda__1___closed__3;
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_traceAtCmdPos___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_synthesizeUsingDefault___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__7;
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDefaultInstances___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance_match__1(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault_match__3(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__2___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__2;
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__2;
lean_object* l_Lean_Meta_instantiateMVarsImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqGuarded___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__6___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__3;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar_match__1(lean_object*);
lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__5;
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__1(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__8;
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__3;
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___closed__1;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars_match__1(lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg___lambda__1___boxed(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__6;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__6;
lean_object* l_Lean_Elab_Tactic_getUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__2(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___closed__2;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault_match__1(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__2;
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftTacticElabM(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
lean_object* l_Lean_InternalExceptionId_getName(lean_object*, lean_object*);
lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__4;
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault_match__2(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__8;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_runTactic___closed__1;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__2;
extern lean_object* l_Lean_formatDataValue___closed__2;
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
extern lean_object* l_Lean_Expr_instInhabitedExpr;
extern uint8_t l_Lean_instInhabitedBinderInfo;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__9;
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__6(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__4;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___rarg(lean_object*, lean_object*);
extern lean_object* l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
extern lean_object* l_Lean_Elab_postponeExceptionId;
lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__7;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_839____closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withSynthesize(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Term_traceAtCmdPos___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__3;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__2___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__5(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault_match__4___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__8;
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_Term_runTactic___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortExceptionId;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withSynthesize___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg___closed__1;
extern lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___closed__1;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_3____closed__1;
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__10;
lean_object* l_Lean_MetavarContext_instantiateMVarDeclMVars(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg___lambda__1(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_runTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__4(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_getDefaultInstances___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_SynthInstance_resume___closed__4;
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_synthesizeUsingDefault___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_defaultInstanceExtension;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Meta_addDefaultInstanceEntry___spec__3(lean_object*, lean_object*);
extern lean_object* l_Array_findSomeM_x3f___rarg___closed__1;
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault_match__4(lean_object*);
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withSynthesize___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__3(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_3, 1);
x_25 = lean_st_ref_get(x_9, x_10);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_take(x_5, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_28, 1);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_28, 1, x_32);
x_33 = lean_st_ref_set(x_5, x_28, x_29);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_1);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_32);
x_36 = lean_st_ref_get(x_9, x_34);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_st_mk_ref(x_35, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_39);
x_41 = lean_apply_9(x_2, x_1, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_st_ref_get(x_9, x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_st_ref_get(x_39, x_45);
lean_dec(x_39);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_st_ref_get(x_9, x_47);
lean_dec(x_9);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_st_ref_take(x_5, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_51, 1);
lean_dec(x_54);
lean_inc(x_24);
lean_ctor_set(x_51, 1, x_24);
x_55 = lean_st_ref_set(x_5, x_51, x_52);
lean_dec(x_5);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_42);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_55, 0, x_59);
x_11 = x_55;
goto block_23;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_42);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
x_11 = x_63;
goto block_23;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_64 = lean_ctor_get(x_51, 0);
x_65 = lean_ctor_get(x_51, 2);
x_66 = lean_ctor_get(x_51, 3);
x_67 = lean_ctor_get(x_51, 4);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_51);
lean_inc(x_24);
x_68 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_24);
lean_ctor_set(x_68, 2, x_65);
lean_ctor_set(x_68, 3, x_66);
lean_ctor_set(x_68, 4, x_67);
x_69 = lean_st_ref_set(x_5, x_68, x_52);
lean_dec(x_5);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_42);
lean_ctor_set(x_73, 1, x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_70);
x_11 = x_74;
goto block_23;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_dec(x_39);
x_75 = lean_ctor_get(x_41, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_41, 1);
lean_inc(x_76);
lean_dec(x_41);
x_77 = lean_st_ref_get(x_9, x_76);
lean_dec(x_9);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_st_ref_take(x_5, x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_80, 1);
lean_dec(x_83);
lean_inc(x_24);
lean_ctor_set(x_80, 1, x_24);
x_84 = lean_st_ref_set(x_5, x_80, x_81);
lean_dec(x_5);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
lean_ctor_set_tag(x_84, 1);
lean_ctor_set(x_84, 0, x_75);
x_11 = x_84;
goto block_23;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_75);
lean_ctor_set(x_88, 1, x_87);
x_11 = x_88;
goto block_23;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_89 = lean_ctor_get(x_80, 0);
x_90 = lean_ctor_get(x_80, 2);
x_91 = lean_ctor_get(x_80, 3);
x_92 = lean_ctor_get(x_80, 4);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_80);
lean_inc(x_24);
x_93 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_24);
lean_ctor_set(x_93, 2, x_90);
lean_ctor_set(x_93, 3, x_91);
lean_ctor_set(x_93, 4, x_92);
x_94 = lean_st_ref_set(x_5, x_93, x_81);
lean_dec(x_5);
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
lean_ctor_set(x_97, 0, x_75);
lean_ctor_set(x_97, 1, x_95);
x_11 = x_97;
goto block_23;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_98 = lean_ctor_get(x_28, 0);
x_99 = lean_ctor_get(x_28, 2);
x_100 = lean_ctor_get(x_28, 3);
x_101 = lean_ctor_get(x_28, 4);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_28);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_103, 2, x_99);
lean_ctor_set(x_103, 3, x_100);
lean_ctor_set(x_103, 4, x_101);
x_104 = lean_st_ref_set(x_5, x_103, x_29);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
lean_inc(x_1);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_1);
lean_ctor_set(x_106, 1, x_102);
x_107 = lean_st_ref_get(x_9, x_105);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_st_mk_ref(x_106, x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_110);
x_112 = lean_apply_9(x_2, x_1, x_110, x_4, x_5, x_6, x_7, x_8, x_9, x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_st_ref_get(x_9, x_114);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_117 = lean_st_ref_get(x_110, x_116);
lean_dec(x_110);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_119 = lean_st_ref_get(x_9, x_118);
lean_dec(x_9);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_st_ref_take(x_5, x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_122, 3);
lean_inc(x_126);
x_127 = lean_ctor_get(x_122, 4);
lean_inc(x_127);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 lean_ctor_release(x_122, 3);
 lean_ctor_release(x_122, 4);
 x_128 = x_122;
} else {
 lean_dec_ref(x_122);
 x_128 = lean_box(0);
}
lean_inc(x_24);
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 5, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_124);
lean_ctor_set(x_129, 1, x_24);
lean_ctor_set(x_129, 2, x_125);
lean_ctor_set(x_129, 3, x_126);
lean_ctor_set(x_129, 4, x_127);
x_130 = lean_st_ref_set(x_5, x_129, x_123);
lean_dec(x_5);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_113);
lean_ctor_set(x_134, 1, x_133);
if (lean_is_scalar(x_132)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_132;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_131);
x_11 = x_135;
goto block_23;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_110);
x_136 = lean_ctor_get(x_112, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_112, 1);
lean_inc(x_137);
lean_dec(x_112);
x_138 = lean_st_ref_get(x_9, x_137);
lean_dec(x_9);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_st_ref_take(x_5, x_139);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_141, 2);
lean_inc(x_144);
x_145 = lean_ctor_get(x_141, 3);
lean_inc(x_145);
x_146 = lean_ctor_get(x_141, 4);
lean_inc(x_146);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 lean_ctor_release(x_141, 2);
 lean_ctor_release(x_141, 3);
 lean_ctor_release(x_141, 4);
 x_147 = x_141;
} else {
 lean_dec_ref(x_141);
 x_147 = lean_box(0);
}
lean_inc(x_24);
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 5, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_24);
lean_ctor_set(x_148, 2, x_144);
lean_ctor_set(x_148, 3, x_145);
lean_ctor_set(x_148, 4, x_146);
x_149 = lean_st_ref_set(x_5, x_148, x_142);
lean_dec(x_5);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
 lean_ctor_set_tag(x_152, 1);
}
lean_ctor_set(x_152, 0, x_136);
lean_ctor_set(x_152, 1, x_150);
x_11 = x_152;
goto block_23;
}
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
}
}
static lean_object* _init_l_Lean_Elab_Term_liftTacticElabM___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_liftTacticElabM___rarg___lambda__1___boxed), 7, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_liftTacticElabM___rarg___lambda__2___boxed), 10, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Lean_Elab_Term_liftTacticElabM___rarg___closed__1;
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg), 9, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__5___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_liftTacticElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_liftTacticElabM___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_liftTacticElabM___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_liftTacticElabM___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_liftTacticElabM___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_runTactic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getUnsolvedGoals(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_runTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_runTactic___lambda__1___boxed), 10, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_runTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_2, x_10);
x_12 = lean_st_ref_get(x_8, x_9);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_take(x_6, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_1);
x_19 = l_Lean_MetavarContext_instantiateMVarDeclMVars(x_18, x_1);
lean_ctor_set(x_15, 0, x_19);
x_20 = lean_st_ref_set(x_6, x_15, x_16);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic), 10, 1);
lean_closure_set(x_22, 0, x_11);
x_23 = l_Lean_Elab_Term_runTactic___closed__1;
x_24 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = l_Lean_Elab_Term_liftTacticElabM___rarg(x_1, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = l_List_isEmpty___rarg(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_free_object(x_25);
x_30 = l_Lean_Elab_Term_reportUnsolvedGoals(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = lean_box(0);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = l_List_isEmpty___rarg(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Lean_Elab_Term_reportUnsolvedGoals(x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_32);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
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
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_25, 0);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_25);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_42 = lean_ctor_get(x_15, 0);
x_43 = lean_ctor_get(x_15, 1);
x_44 = lean_ctor_get(x_15, 2);
x_45 = lean_ctor_get(x_15, 3);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_15);
lean_inc(x_1);
x_46 = l_Lean_MetavarContext_instantiateMVarDeclMVars(x_42, x_1);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_45);
x_48 = lean_st_ref_set(x_6, x_47, x_16);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic), 10, 1);
lean_closure_set(x_50, 0, x_11);
x_51 = l_Lean_Elab_Term_runTactic___closed__1;
x_52 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaTacticAux___spec__1___rarg), 11, 2);
lean_closure_set(x_52, 0, x_50);
lean_closure_set(x_52, 1, x_51);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_53 = l_Lean_Elab_Term_liftTacticElabM___rarg(x_1, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = l_List_isEmpty___rarg(x_54);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_56);
x_58 = l_Lean_Elab_Term_reportUnsolvedGoals(x_54, x_3, x_4, x_5, x_6, x_7, x_8, x_55);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_54);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_59 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_56;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = lean_ctor_get(x_53, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_53, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_63 = x_53;
} else {
 lean_dec_ref(x_53);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
}
lean_object* l_Lean_Elab_Term_runTactic___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_runTactic___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Elab_Term_runTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_runTactic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*6 + 1, x_13);
x_14 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_4, 2);
x_18 = lean_ctor_get(x_4, 3);
x_19 = lean_ctor_get(x_4, 4);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 2);
x_22 = lean_ctor_get(x_4, 5);
lean_inc(x_22);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_23 = 0;
x_24 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_17);
lean_ctor_set(x_24, 3, x_18);
lean_ctor_set(x_24, 4, x_19);
lean_ctor_set(x_24, 5, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*6, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*6 + 1, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*6 + 2, x_21);
x_25 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_23, x_24, x_5, x_6, x_7, x_8, x_9, x_10);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_4);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; 
lean_ctor_set_uint8(x_4, sizeof(void*)*6 + 1, x_3);
x_27 = 0;
x_28 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
x_31 = lean_ctor_get(x_4, 2);
x_32 = lean_ctor_get(x_4, 3);
x_33 = lean_ctor_get(x_4, 4);
x_34 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_35 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 2);
x_36 = lean_ctor_get(x_4, 5);
lean_inc(x_36);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_4);
x_37 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_33);
lean_ctor_set(x_37, 5, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*6, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*6 + 1, x_3);
lean_ctor_set_uint8(x_37, sizeof(void*)*6 + 2, x_35);
x_38 = 0;
x_39 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_38, x_37, x_5, x_6, x_7, x_8, x_9, x_10);
return x_39;
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_apply_3(x_3, x_1, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_apply_3(x_2, x_1, x_7, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logException___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = 2;
x_12 = l_Lean_Elab_logAt___at_Lean_Elab_Term_traceAtCmdPos___spec__3(x_9, x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_dec(x_15);
x_16 = l_Lean_Elab_abortExceptionId;
x_17 = lean_nat_dec_eq(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_st_ref_get(x_7, x_8);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_6, 3);
x_21 = l_Lean_InternalExceptionId_getName(x_14, x_19);
lean_dec(x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_free_object(x_1);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = l_Lean_Elab_logException___rarg___lambda__1___closed__3;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = 2;
x_28 = l_Lean_Elab_log___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_26, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_io_error_to_string(x_30);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_inc(x_20);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_33);
lean_ctor_set(x_1, 0, x_20);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_21, 0);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_21);
x_36 = lean_io_error_to_string(x_34);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_inc(x_20);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_38);
lean_ctor_set(x_1, 0, x_20);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_free_object(x_1);
lean_dec(x_14);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_8);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
x_43 = l_Lean_Elab_abortExceptionId;
x_44 = lean_nat_dec_eq(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_st_ref_get(x_7, x_8);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_6, 3);
x_48 = l_Lean_InternalExceptionId_getName(x_42, x_46);
lean_dec(x_42);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_51, 0, x_49);
x_52 = l_Lean_Elab_logException___rarg___lambda__1___closed__3;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = 2;
x_55 = l_Lean_Elab_log___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_53, x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_50);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_58 = x_48;
} else {
 lean_dec_ref(x_48);
 x_58 = lean_box(0);
}
x_59 = lean_io_error_to_string(x_56);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_inc(x_47);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_47);
lean_ctor_set(x_62, 1, x_61);
if (lean_is_scalar(x_58)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_58;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_57);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_42);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_8);
return x_65;
}
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_56 = lean_ctor_get(x_7, 0);
x_57 = lean_ctor_get(x_7, 1);
x_58 = lean_ctor_get(x_7, 4);
x_59 = lean_ctor_get_uint8(x_7, sizeof(void*)*6);
x_60 = lean_ctor_get_uint8(x_7, sizeof(void*)*6 + 1);
x_61 = lean_ctor_get_uint8(x_7, sizeof(void*)*6 + 2);
x_62 = lean_ctor_get(x_7, 5);
lean_inc(x_62);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
x_63 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_57);
lean_ctor_set(x_63, 2, x_2);
lean_ctor_set(x_63, 3, x_3);
lean_ctor_set(x_63, 4, x_58);
lean_ctor_set(x_63, 5, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*6, x_59);
lean_ctor_set_uint8(x_63, sizeof(void*)*6 + 1, x_60);
lean_ctor_set_uint8(x_63, sizeof(void*)*6 + 2, x_61);
x_64 = l_Lean_Elab_Term_getMVarDecl(x_4, x_63, x_8, x_9, x_10, x_11, x_12, x_13);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 2);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_68 = l_Lean_Meta_instantiateMVarsImp(x_67, x_9, x_10, x_11, x_12, x_66);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_69);
if (x_1 == 0)
{
uint8_t x_72; lean_object* x_73; 
x_72 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_63);
lean_inc(x_71);
lean_inc(x_5);
x_73 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm(x_5, x_71, x_72, x_63, x_8, x_9, x_10, x_11, x_12, x_70);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_box(0);
x_77 = lean_ctor_get(x_11, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_11, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_11, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_11, 3);
lean_inc(x_80);
x_81 = lean_ctor_get(x_11, 4);
lean_inc(x_81);
x_82 = lean_ctor_get(x_11, 5);
lean_inc(x_82);
x_83 = l_Lean_replaceRef(x_5, x_80);
lean_dec(x_80);
lean_dec(x_5);
x_84 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_78);
lean_ctor_set(x_84, 2, x_79);
lean_ctor_set(x_84, 3, x_83);
lean_ctor_set(x_84, 4, x_81);
lean_ctor_set(x_84, 5, x_82);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_63);
x_85 = l_Lean_Elab_Term_ensureHasType(x_71, x_74, x_76, x_63, x_8, x_9, x_10, x_84, x_12, x_75);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_6);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Meta_assignExprMVar___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(x_4, x_86, x_63, x_8, x_9, x_10, x_11, x_12, x_87);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_63);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_88, 0);
lean_dec(x_90);
x_91 = lean_box(x_72);
lean_ctor_set(x_88, 0, x_91);
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
x_93 = lean_box(x_72);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_63);
lean_dec(x_4);
x_95 = lean_ctor_get(x_85, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_85, 1);
lean_inc(x_96);
lean_dec(x_85);
x_14 = x_95;
x_15 = x_96;
goto block_55;
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_71);
lean_dec(x_63);
lean_dec(x_5);
lean_dec(x_4);
x_97 = lean_ctor_get(x_73, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_73, 1);
lean_inc(x_98);
lean_dec(x_73);
x_14 = x_97;
x_15 = x_98;
goto block_55;
}
}
else
{
uint8_t x_99; lean_object* x_100; 
x_99 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_63);
lean_inc(x_71);
lean_inc(x_5);
x_100 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumeElabTerm(x_5, x_71, x_99, x_63, x_8, x_9, x_10, x_11, x_12, x_70);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_box(0);
x_104 = lean_ctor_get(x_11, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_11, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_11, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_11, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_11, 4);
lean_inc(x_108);
x_109 = lean_ctor_get(x_11, 5);
lean_inc(x_109);
x_110 = l_Lean_replaceRef(x_5, x_107);
lean_dec(x_107);
lean_dec(x_5);
x_111 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_111, 0, x_104);
lean_ctor_set(x_111, 1, x_105);
lean_ctor_set(x_111, 2, x_106);
lean_ctor_set(x_111, 3, x_110);
lean_ctor_set(x_111, 4, x_108);
lean_ctor_set(x_111, 5, x_109);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_63);
x_112 = l_Lean_Elab_Term_ensureHasType(x_71, x_101, x_103, x_63, x_8, x_9, x_10, x_111, x_12, x_102);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_6);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Meta_assignExprMVar___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(x_4, x_113, x_63, x_8, x_9, x_10, x_11, x_12, x_114);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_63);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_115, 0);
lean_dec(x_117);
x_118 = 1;
x_119 = lean_box(x_118);
lean_ctor_set(x_115, 0, x_119);
return x_115;
}
else
{
lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
lean_dec(x_115);
x_121 = 1;
x_122 = lean_box(x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_63);
lean_dec(x_4);
x_124 = lean_ctor_get(x_112, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_112, 1);
lean_inc(x_125);
lean_dec(x_112);
x_14 = x_124;
x_15 = x_125;
goto block_55;
}
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_71);
lean_dec(x_63);
lean_dec(x_5);
lean_dec(x_4);
x_126 = lean_ctor_get(x_100, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_100, 1);
lean_inc(x_127);
lean_dec(x_100);
x_14 = x_126;
x_15 = x_127;
goto block_55;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_63);
lean_dec(x_5);
lean_dec(x_4);
x_128 = lean_ctor_get(x_68, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_68, 1);
lean_inc(x_129);
lean_dec(x_68);
x_14 = x_128;
x_15 = x_129;
goto block_55;
}
block_55:
{
if (lean_obj_tag(x_14) == 0)
{
if (x_1 == 0)
{
lean_object* x_16; 
lean_dec(x_6);
x_16 = l_Lean_Elab_logException___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1(x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_29 = lean_st_ref_get(x_12, x_15);
lean_dec(x_12);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_set(x_8, x_6, x_30);
lean_dec(x_8);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = 0;
x_35 = lean_box(x_34);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_40 = lean_ctor_get(x_14, 0);
lean_inc(x_40);
x_41 = l_Lean_Elab_postponeExceptionId;
x_42 = lean_nat_dec_eq(x_40, x_41);
lean_dec(x_40);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_14);
lean_ctor_set(x_43, 1, x_15);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_14);
x_44 = lean_st_ref_get(x_12, x_15);
lean_dec(x_12);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_st_ref_set(x_8, x_6, x_45);
lean_dec(x_8);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = 0;
x_50 = lean_box(x_49);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = 0;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_box(x_5);
lean_inc(x_3);
lean_inc(x_4);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__1___boxed), 13, 5);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_3);
x_15 = l_Lean_Elab_Term_liftTacticElabM___rarg___closed__1;
x_16 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg), 9, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 3);
x_19 = l_Lean_replaceRef(x_3, x_18);
lean_dec(x_18);
lean_dec(x_3);
lean_ctor_set(x_10, 3, x_19);
x_20 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__5___rarg(x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
x_23 = lean_ctor_get(x_10, 2);
x_24 = lean_ctor_get(x_10, 3);
x_25 = lean_ctor_get(x_10, 4);
x_26 = lean_ctor_get(x_10, 5);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_27 = l_Lean_replaceRef(x_3, x_24);
lean_dec(x_24);
lean_dec(x_3);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 2, x_23);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_25);
lean_ctor_set(x_28, 5, x_26);
x_29 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__5___rarg(x_4, x_16, x_6, x_7, x_8, x_9, x_28, x_11, x_12);
return x_29;
}
}
}
lean_object* l_Lean_Elab_logException___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_logException___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___lambda__1(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
return x_15;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.SyntheticMVars");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.SyntheticMVars.0.Lean.Elab.Term.synthesizePendingInstMVar");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__1;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__2;
x_3 = lean_unsigned_to_nat(78u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_logException___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = 1;
x_16 = lean_box(x_15);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_dec(x_9);
x_26 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_27 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__3;
x_28 = lean_panic_fn(x_26, x_27);
x_29 = lean_apply_7(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_25);
return x_29;
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1), 8, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__5___rarg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.SyntheticMVars.0.Lean.Elab.Term.synthesizePendingCoeInstMVar");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__1;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar___lambda__1___closed__1;
x_3 = lean_unsigned_to_nat(89u);
x_4 = lean_unsigned_to_nat(33u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_dec(x_12);
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
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_2, x_3, x_4, x_5, x_6, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_8);
lean_dec(x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_22 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar___lambda__1___closed__2;
x_23 = lean_panic_fn(x_21, x_22);
x_24 = lean_apply_7(x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar___lambda__1___boxed), 13, 6);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_6);
x_15 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__5___rarg(x_1, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_14;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_5(x_3, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_apply_2(x_5, x_14, x_15);
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_apply_2(x_4, x_17, x_18);
return x_19;
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_8, 3);
x_15 = l_Lean_replaceRef(x_11, x_14);
lean_dec(x_14);
lean_ctor_set(x_8, 3, x_15);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_12, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_12, 4);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar(x_23, x_18, x_19, x_20, x_21, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_24;
}
case 2:
{
lean_dec(x_11);
if (x_3 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_8);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_10);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_12, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_dec(x_12);
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_4, 2);
lean_dec(x_31);
lean_ctor_set(x_4, 2, x_28);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
lean_dec(x_1);
x_33 = l_Lean_Elab_Term_runTactic(x_32, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_29);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = 1;
x_37 = lean_box(x_36);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = 1;
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_33);
if (x_42 == 0)
{
return x_33;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_33, 0);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_33);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_ctor_get(x_4, 0);
x_47 = lean_ctor_get(x_4, 1);
x_48 = lean_ctor_get(x_4, 3);
x_49 = lean_ctor_get(x_4, 4);
x_50 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_51 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_52 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 2);
x_53 = lean_ctor_get(x_4, 5);
lean_inc(x_53);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_4);
x_54 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_54, 0, x_46);
lean_ctor_set(x_54, 1, x_47);
lean_ctor_set(x_54, 2, x_28);
lean_ctor_set(x_54, 3, x_48);
lean_ctor_set(x_54, 4, x_49);
lean_ctor_set(x_54, 5, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*6, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*6 + 1, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*6 + 2, x_52);
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
lean_dec(x_1);
x_56 = l_Lean_Elab_Term_runTactic(x_55, x_29, x_54, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_29);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
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
x_59 = 1;
x_60 = lean_box(x_59);
if (lean_is_scalar(x_58)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_58;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_56, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_64 = x_56;
} else {
 lean_dec_ref(x_56);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
}
default: 
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_12, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_12, 1);
lean_inc(x_67);
lean_dec(x_12);
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
lean_dec(x_1);
x_69 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed(x_66, x_67, x_11, x_68, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_8, 0);
x_71 = lean_ctor_get(x_8, 1);
x_72 = lean_ctor_get(x_8, 2);
x_73 = lean_ctor_get(x_8, 3);
x_74 = lean_ctor_get(x_8, 4);
x_75 = lean_ctor_get(x_8, 5);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_8);
x_76 = l_Lean_replaceRef(x_11, x_73);
lean_dec(x_73);
x_77 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set(x_77, 1, x_71);
lean_ctor_set(x_77, 2, x_72);
lean_ctor_set(x_77, 3, x_76);
lean_ctor_set(x_77, 4, x_74);
lean_ctor_set(x_77, 5, x_75);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_11);
x_78 = lean_ctor_get(x_1, 0);
lean_inc(x_78);
lean_dec(x_1);
x_79 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar(x_78, x_4, x_5, x_6, x_7, x_77, x_9, x_10);
return x_79;
}
case 1:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_11);
x_80 = lean_ctor_get(x_12, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_12, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_12, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_12, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_12, 4);
lean_inc(x_84);
lean_dec(x_12);
x_85 = lean_ctor_get(x_1, 0);
lean_inc(x_85);
lean_dec(x_1);
x_86 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar(x_85, x_80, x_81, x_82, x_83, x_84, x_4, x_5, x_6, x_7, x_77, x_9, x_10);
return x_86;
}
case 2:
{
lean_dec(x_11);
if (x_3 == 0)
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_77);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_87 = 0;
x_88 = lean_box(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_10);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_90 = lean_ctor_get(x_12, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_12, 1);
lean_inc(x_91);
lean_dec(x_12);
x_92 = lean_ctor_get(x_4, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_4, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_4, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_4, 4);
lean_inc(x_95);
x_96 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_97 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_98 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 2);
x_99 = lean_ctor_get(x_4, 5);
lean_inc(x_99);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_100 = x_4;
} else {
 lean_dec_ref(x_4);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(0, 6, 3);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_92);
lean_ctor_set(x_101, 1, x_93);
lean_ctor_set(x_101, 2, x_90);
lean_ctor_set(x_101, 3, x_94);
lean_ctor_set(x_101, 4, x_95);
lean_ctor_set(x_101, 5, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*6, x_96);
lean_ctor_set_uint8(x_101, sizeof(void*)*6 + 1, x_97);
lean_ctor_set_uint8(x_101, sizeof(void*)*6 + 2, x_98);
x_102 = lean_ctor_get(x_1, 0);
lean_inc(x_102);
lean_dec(x_1);
x_103 = l_Lean_Elab_Term_runTactic(x_102, x_91, x_101, x_5, x_6, x_7, x_77, x_9, x_10);
lean_dec(x_91);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = 1;
x_107 = lean_box(x_106);
if (lean_is_scalar(x_105)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_105;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_104);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_103, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_103, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_111 = x_103;
} else {
 lean_dec_ref(x_103);
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
default: 
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_12, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_12, 1);
lean_inc(x_114);
lean_dec(x_12);
x_115 = lean_ctor_get(x_1, 0);
lean_inc(x_115);
lean_dec(x_1);
x_116 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed(x_113, x_114, x_11, x_115, x_2, x_4, x_5, x_6, x_7, x_77, x_9, x_10);
return x_116;
}
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not ready yet");
return x_1;
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("succeeded");
return x_1;
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resuming ");
return x_1;
}
}
static lean_object* _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_16 = x_4;
} else {
 lean_dec_ref(x_4);
 x_16 = lean_box(0);
}
x_23 = l_Lean_Elab_initFn____x40_Lean_Elab_Exception___hyg_3____closed__1;
lean_inc(x_3);
x_24 = lean_name_mk_string(x_3, x_23);
x_60 = lean_ctor_get(x_14, 0);
lean_inc(x_60);
lean_inc(x_60);
x_61 = l_Lean_mkMVar(x_60);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__8;
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_closure((void*)(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__1___boxed), 8, 1);
lean_closure_set(x_67, 0, x_66);
x_68 = lean_st_ref_get(x_11, x_12);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 3);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_ctor_get_uint8(x_70, sizeof(void*)*1);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_67);
lean_dec(x_60);
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
lean_dec(x_68);
x_25 = x_72;
goto block_59;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_dec(x_68);
lean_inc(x_24);
x_74 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_67);
lean_dec(x_60);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_25 = x_77;
goto block_59;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_79 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__5___rarg(x_60, x_67, x_6, x_7, x_8, x_9, x_10, x_11, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_24);
x_82 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_24, x_80, x_6, x_7, x_8, x_9, x_10, x_11, x_81);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_25 = x_83;
goto block_59;
}
else
{
uint8_t x_84; 
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_79);
if (x_84 == 0)
{
return x_79;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_79, 0);
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_79);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
block_22:
{
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
x_4 = x_15;
x_12 = x_18;
goto _start;
}
else
{
lean_object* x_20; 
if (lean_is_scalar(x_16)) {
 x_20 = lean_alloc_ctor(1, 2, 0);
} else {
 x_20 = x_16;
}
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_5);
x_4 = x_15;
x_5 = x_20;
x_12 = x_18;
goto _start;
}
}
block_59:
{
lean_object* x_26; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_14);
x_26 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVar(x_14, x_1, x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_44 = lean_st_ref_get(x_11, x_28);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 3);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get_uint8(x_46, sizeof(void*)*1);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = 0;
x_29 = x_49;
x_30 = x_48;
goto block_43;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
lean_inc(x_24);
x_51 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_unbox(x_52);
lean_dec(x_52);
x_29 = x_54;
x_30 = x_53;
goto block_43;
}
block_43:
{
if (x_29 == 0)
{
uint8_t x_31; 
lean_dec(x_24);
x_31 = lean_unbox(x_27);
lean_dec(x_27);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = 1;
x_17 = x_32;
x_18 = x_30;
goto block_22;
}
else
{
uint8_t x_33; 
x_33 = 0;
x_17 = x_33;
x_18 = x_30;
goto block_22;
}
}
else
{
uint8_t x_34; 
x_34 = lean_unbox(x_27);
lean_dec(x_27);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__3;
x_36 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_24, x_35, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = 1;
x_17 = x_38;
x_18 = x_37;
goto block_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__6;
x_40 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_24, x_39, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = 0;
x_17 = x_42;
x_18 = x_41;
goto block_22;
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_26);
if (x_55 == 0)
{
return x_26;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_26, 0);
x_57 = lean_ctor_get(x_26, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_26);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
}
lean_object* l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__2(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lean_formatDataValue___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_formatDataValue___closed__2;
return x_3;
}
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resuming");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_839____closed__1;
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resuming synthetic metavariables, mayPostpone: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", postponeOnError: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_formatDataValue___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_formatDataValue___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_124 = lean_ctor_get(x_7, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_7, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_7, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_7, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_7, 4);
lean_inc(x_128);
x_129 = lean_ctor_get(x_7, 5);
lean_inc(x_129);
x_130 = lean_box(0);
x_131 = l_Lean_replaceRef(x_130, x_127);
lean_dec(x_127);
lean_inc(x_124);
x_132 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_132, 0, x_124);
lean_ctor_set(x_132, 1, x_125);
lean_ctor_set(x_132, 2, x_126);
lean_ctor_set(x_132, 3, x_131);
lean_ctor_set(x_132, 4, x_128);
lean_ctor_set(x_132, 5, x_129);
x_133 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__2;
x_134 = l_Lean_checkTraceOption(x_124, x_133);
lean_dec(x_124);
if (x_134 == 0)
{
lean_dec(x_132);
x_10 = x_9;
goto block_123;
}
else
{
uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_135 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_136 = l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__2(x_135);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_138 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__5;
x_139 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
x_140 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__8;
x_141 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
if (x_1 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__9;
x_143 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_133, x_143, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
lean_dec(x_132);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_10 = x_145;
goto block_123;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__10;
x_147 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_147, 0, x_141);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_133, x_147, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
lean_dec(x_132);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
x_10 = x_149;
goto block_123;
}
}
block_123:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_11 = lean_st_ref_get(x_8, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_List_lengthAux___rarg(x_16, x_17);
x_19 = lean_st_ref_get(x_8, x_15);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_take(x_4, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_22, 1);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_22, 1, x_26);
x_27 = lean_st_ref_set(x_4, x_22, x_23);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_List_reverse___rarg(x_16);
x_30 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_839____closed__1;
lean_inc(x_8);
lean_inc(x_4);
x_31 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1(x_1, x_2, x_30, x_29, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_8, x_33);
lean_dec(x_8);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_take(x_4, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_32);
x_41 = l_List_append___rarg(x_40, x_32);
lean_ctor_set(x_37, 1, x_41);
x_42 = lean_st_ref_set(x_4, x_37, x_38);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = l_List_lengthAux___rarg(x_32, x_17);
lean_dec(x_32);
x_46 = lean_nat_dec_eq(x_18, x_45);
lean_dec(x_45);
lean_dec(x_18);
if (x_46 == 0)
{
uint8_t x_47; lean_object* x_48; 
x_47 = 1;
x_48 = lean_box(x_47);
lean_ctor_set(x_42, 0, x_48);
return x_42;
}
else
{
uint8_t x_49; lean_object* x_50; 
x_49 = 0;
x_50 = lean_box(x_49);
lean_ctor_set(x_42, 0, x_50);
return x_42;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_dec(x_42);
x_52 = l_List_lengthAux___rarg(x_32, x_17);
lean_dec(x_32);
x_53 = lean_nat_dec_eq(x_18, x_52);
lean_dec(x_52);
lean_dec(x_18);
if (x_53 == 0)
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_54 = 1;
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_51);
return x_56;
}
else
{
uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_57 = 0;
x_58 = lean_box(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_51);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_60 = lean_ctor_get(x_37, 0);
x_61 = lean_ctor_get(x_37, 1);
x_62 = lean_ctor_get(x_37, 2);
x_63 = lean_ctor_get(x_37, 3);
x_64 = lean_ctor_get(x_37, 4);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_37);
lean_inc(x_32);
x_65 = l_List_append___rarg(x_61, x_32);
x_66 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_62);
lean_ctor_set(x_66, 3, x_63);
lean_ctor_set(x_66, 4, x_64);
x_67 = lean_st_ref_set(x_4, x_66, x_38);
lean_dec(x_4);
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
x_70 = l_List_lengthAux___rarg(x_32, x_17);
lean_dec(x_32);
x_71 = lean_nat_dec_eq(x_18, x_70);
lean_dec(x_70);
lean_dec(x_18);
if (x_71 == 0)
{
uint8_t x_72; lean_object* x_73; lean_object* x_74; 
x_72 = 1;
x_73 = lean_box(x_72);
if (lean_is_scalar(x_69)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_69;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_68);
return x_74;
}
else
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_75 = 0;
x_76 = lean_box(x_75);
if (lean_is_scalar(x_69)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_69;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_68);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_4);
x_78 = !lean_is_exclusive(x_31);
if (x_78 == 0)
{
return x_31;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_31, 0);
x_80 = lean_ctor_get(x_31, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_31);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_82 = lean_ctor_get(x_22, 0);
x_83 = lean_ctor_get(x_22, 2);
x_84 = lean_ctor_get(x_22, 3);
x_85 = lean_ctor_get(x_22, 4);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_22);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_83);
lean_ctor_set(x_87, 3, x_84);
lean_ctor_set(x_87, 4, x_85);
x_88 = lean_st_ref_set(x_4, x_87, x_23);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l_List_reverse___rarg(x_16);
x_91 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_839____closed__1;
lean_inc(x_8);
lean_inc(x_4);
x_92 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1(x_1, x_2, x_91, x_90, x_86, x_3, x_4, x_5, x_6, x_7, x_8, x_89);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_st_ref_get(x_8, x_94);
lean_dec(x_8);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_st_ref_take(x_4, x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_98, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_98, 3);
lean_inc(x_103);
x_104 = lean_ctor_get(x_98, 4);
lean_inc(x_104);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 lean_ctor_release(x_98, 2);
 lean_ctor_release(x_98, 3);
 lean_ctor_release(x_98, 4);
 x_105 = x_98;
} else {
 lean_dec_ref(x_98);
 x_105 = lean_box(0);
}
lean_inc(x_93);
x_106 = l_List_append___rarg(x_101, x_93);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 5, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_100);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_107, 2, x_102);
lean_ctor_set(x_107, 3, x_103);
lean_ctor_set(x_107, 4, x_104);
x_108 = lean_st_ref_set(x_4, x_107, x_99);
lean_dec(x_4);
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
x_111 = l_List_lengthAux___rarg(x_93, x_17);
lean_dec(x_93);
x_112 = lean_nat_dec_eq(x_18, x_111);
lean_dec(x_111);
lean_dec(x_18);
if (x_112 == 0)
{
uint8_t x_113; lean_object* x_114; lean_object* x_115; 
x_113 = 1;
x_114 = lean_box(x_113);
if (lean_is_scalar(x_110)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_110;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_109);
return x_115;
}
else
{
uint8_t x_116; lean_object* x_117; lean_object* x_118; 
x_116 = 0;
x_117 = lean_box(x_116);
if (lean_is_scalar(x_110)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_110;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_109);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_4);
x_119 = lean_ctor_get(x_92, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_92, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_121 = x_92;
} else {
 lean_dec_ref(x_92);
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
}
}
lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
lean_object* l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__2(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isExprDefEqGuarded___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isExprDefEqImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = 0;
x_12 = lean_box(x_11);
lean_ctor_set_tag(x_8, 0);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_nat_dec_le(x_12, x_5);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_4, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_4, x_16);
lean_dec(x_4);
x_18 = l_Lean_instInhabitedBinderInfo;
x_19 = lean_box(x_18);
x_20 = lean_array_get(x_19, x_2, x_5);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
x_22 = 3;
x_23 = l_Lean_BinderInfo_beq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_4 = x_17;
x_5 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_9, 3);
x_28 = l_Lean_Expr_instInhabitedExpr;
x_29 = lean_array_get(x_28, x_1, x_5);
x_30 = l_Lean_Expr_mvarId_x21(x_29);
lean_dec(x_29);
x_31 = lean_box(0);
lean_inc(x_27);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_6);
x_34 = lean_ctor_get(x_3, 2);
x_35 = lean_nat_add(x_5, x_34);
lean_dec(x_5);
x_4 = x_17;
x_5 = x_35;
x_6 = x_33;
goto _start;
}
}
else
{
lean_object* x_37; 
lean_dec(x_5);
lean_dec(x_4);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_6);
lean_ctor_set(x_37, 1, x_11);
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec(x_5);
lean_dec(x_4);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_11);
return x_38;
}
}
}
static lean_object* _init_l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_839____closed__1;
x_2 = l_Lean_Meta_SynthInstance_resume___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trying default instance for ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = l_Lean_ConstantInfo_lparams(x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_List_lengthAux___rarg(x_9, x_10);
lean_dec(x_9);
x_12 = l_Lean_Elab_Term_mkFreshLevelMVars(x_11, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_mkConst(x_1, x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_15);
x_16 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_15, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = 1;
x_21 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_17, x_20, x_19, x_21, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_56; lean_object* x_57; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Lean_mkAppN(x_15, x_26);
x_72 = lean_st_ref_get(x_7, x_25);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 3);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_ctor_get_uint8(x_74, sizeof(void*)*1);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
x_77 = 0;
x_56 = x_77;
x_57 = x_76;
goto block_71;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_dec(x_72);
x_79 = l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__1;
x_80 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_79, x_4, x_5, x_6, x_7, x_78);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_unbox(x_81);
lean_dec(x_81);
x_56 = x_83;
x_57 = x_82;
goto block_71;
}
block_55:
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_mkMVar(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_31 = l_Lean_Meta_isExprDefEqGuarded___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__1(x_30, x_28, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
lean_ctor_set(x_31, 0, x_19);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_19);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_dec(x_31);
x_39 = lean_box(0);
x_40 = lean_array_get_size(x_27);
x_41 = lean_unsigned_to_nat(1u);
lean_inc(x_40);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_10);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_41);
x_43 = l_Std_Range_forIn_loop___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__2(x_26, x_27, x_42, x_40, x_10, x_39, x_4, x_5, x_6, x_7, x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_42);
lean_dec(x_27);
lean_dec(x_26);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
block_71:
{
if (x_56 == 0)
{
x_29 = x_57;
goto block_55;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_inc(x_2);
x_58 = l_Lean_mkMVar(x_2);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__3;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__8;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_inc(x_28);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_28);
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__1;
x_69 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_68, x_67, x_4, x_5, x_6, x_7, x_57);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_29 = x_70;
goto block_55;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_22);
if (x_84 == 0)
{
return x_22;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_22, 0);
x_86 = lean_ctor_get(x_22, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_22);
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
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_16);
if (x_88 == 0)
{
return x_16;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_16, 0);
x_90 = lean_ctor_get(x_16, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_16);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_30; 
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1___boxed), 6, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___boxed), 8, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_1);
x_10 = lean_st_ref_get(x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_6, x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_4, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg(x_8, x_9, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_13, x_3, x_4, x_5, x_6, x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_19, x_3, x_4, x_5, x_6, x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
uint8_t x_42; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_30);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_30, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
return x_30;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_31, 0);
lean_inc(x_45);
lean_dec(x_31);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_30, 0, x_46);
return x_30;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
lean_dec(x_30);
x_48 = lean_ctor_get(x_31, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_49 = x_31;
} else {
 lean_dec_ref(x_31);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_30, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_30, 1);
lean_inc(x_53);
lean_dec(x_30);
x_20 = x_52;
x_21 = x_53;
goto block_29;
}
block_29:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_13, x_3, x_4, x_5, x_6, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_19, x_3, x_4, x_5, x_6, x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_20);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__3___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__5___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances_match__6___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getDefaultInstances___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Meta_defaultInstanceExtension;
x_12 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_11, x_10);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Std_RBNode_find___at_Lean_Meta_addDefaultInstanceEntry___spec__3(x_13, x_1);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_box(0);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_defaultInstanceExtension;
x_21 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_20, x_19);
lean_dec(x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Std_RBNode_find___at_Lean_Meta_addDefaultInstanceEntry___spec__3(x_22, x_1);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_18);
return x_27;
}
}
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_14 = l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3(x_1, x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_2);
{
lean_object* _tmp_2 = x_12;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_8 = x_16;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_9 = _tmp_8;
}
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_ctor_get(x_15, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_31 = x_15;
} else {
 lean_dec_ref(x_15);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_30);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
return x_14;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_14, 0);
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_14);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Meta_isClass_x3f___at___private_Lean_Meta_Basic_0__Lean_Meta_withNewFVar___spec__1(x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_Meta_getDefaultInstances___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances___spec__1(x_18, x_3, x_4, x_5, x_6, x_17);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_box(0);
x_29 = l_Array_findSomeM_x3f___rarg___closed__1;
x_30 = l_List_forIn_loop___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances___spec__2(x_1, x_29, x_20, x_29, x_3, x_4, x_5, x_6, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_30, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_39);
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_9);
if (x_47 == 0)
{
return x_9;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_9, 0);
x_49 = lean_ctor_get(x_9, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_9);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
lean_object* l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances___lambda__1), 7, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
lean_object* l_Lean_Meta_getDefaultInstances___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getDefaultInstances___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_synthesizeUsingDefault_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_synthesizeUsingDefault_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault_match__3___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_synthesizeUsingDefault_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault_match__4___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_synthesizeUsingDefault_match__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_synthesizeUsingDefault___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
x_23 = lean_ctor_get(x_7, 2);
x_24 = lean_ctor_get(x_7, 3);
x_25 = lean_ctor_get(x_7, 4);
x_26 = lean_ctor_get(x_7, 5);
x_27 = l_Lean_replaceRef(x_19, x_24);
lean_dec(x_19);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 2, x_23);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_25);
lean_ctor_set(x_28, 5, x_26);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances(x_20, x_5, x_6, x_28, x_8, x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_2, 0, x_1);
x_1 = x_14;
x_9 = x_31;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
lean_dec(x_18);
lean_free_object(x_1);
lean_dec(x_11);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = l_List_append___rarg(x_34, x_17);
x_36 = 1;
x_37 = lean_box(x_36);
lean_ctor_set(x_2, 1, x_37);
lean_ctor_set(x_2, 0, x_35);
x_1 = x_14;
x_9 = x_33;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_2);
lean_dec(x_18);
lean_dec(x_17);
lean_free_object(x_1);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_29);
if (x_39 == 0)
{
return x_29;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_29, 0);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_29);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_2);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_11, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 1);
x_49 = lean_ctor_get(x_7, 2);
x_50 = lean_ctor_get(x_7, 3);
x_51 = lean_ctor_get(x_7, 4);
x_52 = lean_ctor_get(x_7, 5);
x_53 = l_Lean_replaceRef(x_45, x_50);
lean_dec(x_45);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
x_54 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_48);
lean_ctor_set(x_54, 2, x_49);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_51);
lean_ctor_set(x_54, 5, x_52);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_55 = l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances(x_46, x_5, x_6, x_54, x_8, x_9);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_ctor_set(x_1, 1, x_43);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_44);
x_1 = x_14;
x_2 = x_58;
x_9 = x_57;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_44);
lean_free_object(x_1);
lean_dec(x_11);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
lean_dec(x_56);
x_62 = l_List_append___rarg(x_61, x_43);
x_63 = 1;
x_64 = lean_box(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
x_1 = x_14;
x_2 = x_65;
x_9 = x_60;
goto _start;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_44);
lean_dec(x_43);
lean_free_object(x_1);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_67 = lean_ctor_get(x_55, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_55, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_69 = x_55;
} else {
 lean_dec_ref(x_55);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_71 = lean_ctor_get(x_1, 1);
lean_inc(x_71);
lean_dec(x_1);
x_72 = lean_ctor_get(x_2, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_2, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_74 = x_2;
} else {
 lean_dec_ref(x_2);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_11, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_11, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_7, 0);
x_78 = lean_ctor_get(x_7, 1);
x_79 = lean_ctor_get(x_7, 2);
x_80 = lean_ctor_get(x_7, 3);
x_81 = lean_ctor_get(x_7, 4);
x_82 = lean_ctor_get(x_7, 5);
x_83 = l_Lean_replaceRef(x_75, x_80);
lean_dec(x_75);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
x_84 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_78);
lean_ctor_set(x_84, 2, x_79);
lean_ctor_set(x_84, 3, x_83);
lean_ctor_set(x_84, 4, x_81);
lean_ctor_set(x_84, 5, x_82);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_85 = l_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstances(x_76, x_5, x_6, x_84, x_8, x_9);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_11);
lean_ctor_set(x_88, 1, x_72);
if (lean_is_scalar(x_74)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_74;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_73);
x_1 = x_71;
x_2 = x_89;
x_9 = x_87;
goto _start;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_73);
lean_dec(x_11);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
lean_dec(x_85);
x_92 = lean_ctor_get(x_86, 0);
lean_inc(x_92);
lean_dec(x_86);
x_93 = l_List_append___rarg(x_92, x_72);
x_94 = 1;
x_95 = lean_box(x_94);
if (lean_is_scalar(x_74)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_74;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_1 = x_71;
x_2 = x_96;
x_9 = x_91;
goto _start;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_98 = lean_ctor_get(x_85, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_85, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_100 = x_85;
} else {
 lean_dec_ref(x_85);
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
}
else
{
uint8_t x_102; 
lean_dec(x_12);
x_102 = !lean_is_exclusive(x_1);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_1, 1);
x_104 = lean_ctor_get(x_1, 0);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_2);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_2, 0);
lean_ctor_set(x_1, 1, x_106);
lean_ctor_set(x_2, 0, x_1);
x_1 = x_103;
goto _start;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_2, 0);
x_109 = lean_ctor_get(x_2, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_1);
lean_ctor_set(x_110, 1, x_109);
x_1 = x_103;
x_2 = x_110;
goto _start;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_1, 1);
lean_inc(x_112);
lean_dec(x_1);
x_113 = lean_ctor_get(x_2, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_2, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_115 = x_2;
} else {
 lean_dec_ref(x_2);
 x_115 = lean_box(0);
}
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_11);
lean_ctor_set(x_116, 1, x_113);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
x_1 = x_112;
x_2 = x_117;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_synthesizeUsingDefault___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_List_reverse___rarg(x_13);
x_15 = l_Lean_Elab_Term_synthesizeUsingDefault___closed__1;
lean_inc(x_6);
x_16 = l_List_forIn_loop___at_Lean_Elab_Term_synthesizeUsingDefault___spec__1(x_14, x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
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
x_21 = lean_st_ref_get(x_6, x_18);
lean_dec(x_6);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_take(x_2, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_24, 1);
lean_dec(x_27);
lean_ctor_set(x_24, 1, x_19);
x_28 = lean_st_ref_set(x_2, x_24, x_25);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_20);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 2);
x_35 = lean_ctor_get(x_24, 3);
x_36 = lean_ctor_get(x_24, 4);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_19);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_37, 3, x_35);
lean_ctor_set(x_37, 4, x_36);
x_38 = lean_st_ref_set(x_2, x_37, x_25);
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
lean_ctor_set(x_41, 0, x_20);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_6);
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
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_synthesizeUsingDefault___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_loop___at_Lean_Elab_Term_synthesizeUsingDefault___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_synthesizeUsingDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_synthesizeUsingDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_5(x_3, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
default: 
{
lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_apply_1(x_4, x_1);
return x_13;
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to create type class instance for ");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_indentExpr(x_9);
x_11 = l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__3;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = 2;
x_14 = l_Lean_Elab_log___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_6, 2);
lean_inc(x_14);
lean_dec(x_6);
x_15 = l_Lean_indentExpr(x_14);
x_16 = l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__3;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Elab_Term_throwTypeMismatchError___rarg(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_18);
return x_19;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.SyntheticMVars.0.Lean.Elab.Term.reportStuckSyntheticMVars");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__1;
x_2 = l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(202u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_11, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
x_22 = lean_ctor_get(x_7, 2);
x_23 = lean_ctor_get(x_7, 3);
x_24 = lean_ctor_get(x_7, 4);
x_25 = lean_ctor_get(x_7, 5);
x_26 = l_Lean_replaceRef(x_18, x_23);
lean_dec(x_18);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_27 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set(x_27, 5, x_25);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_11, 0);
lean_inc(x_28);
lean_dec(x_11);
lean_inc(x_28);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getMVarDecl___boxed), 8, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___closed__1;
x_31 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg), 9, 2);
lean_closure_set(x_31, 0, x_29);
lean_closure_set(x_31, 1, x_30);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_32 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__5___rarg(x_28, x_31, x_3, x_4, x_5, x_6, x_27, x_8, x_9);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___closed__1;
x_13 = x_34;
x_14 = x_33;
goto block_17;
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
case 1:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_19, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_19, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_19, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_19, 4);
lean_inc(x_43);
lean_dec(x_19);
x_44 = lean_ctor_get(x_11, 0);
lean_inc(x_44);
lean_dec(x_11);
lean_inc(x_44);
x_45 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getMVarDecl___boxed), 8, 1);
lean_closure_set(x_45, 0, x_44);
x_46 = lean_alloc_closure((void*)(l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__2___boxed), 13, 5);
lean_closure_set(x_46, 0, x_39);
lean_closure_set(x_46, 1, x_40);
lean_closure_set(x_46, 2, x_41);
lean_closure_set(x_46, 3, x_42);
lean_closure_set(x_46, 4, x_43);
x_47 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg), 9, 2);
lean_closure_set(x_47, 0, x_45);
lean_closure_set(x_47, 1, x_46);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_48 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__5___rarg(x_44, x_47, x_3, x_4, x_5, x_6, x_27, x_8, x_9);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___closed__1;
x_13 = x_50;
x_14 = x_49;
goto block_17;
}
else
{
uint8_t x_51; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
default: 
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_19);
lean_dec(x_11);
x_55 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_56 = l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___closed__3;
x_57 = lean_panic_fn(x_55, x_56);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_58 = lean_apply_7(x_57, x_3, x_4, x_5, x_6, x_27, x_8, x_9);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___closed__1;
x_13 = x_60;
x_14 = x_59;
goto block_17;
}
else
{
uint8_t x_61; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_58);
if (x_61 == 0)
{
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 0);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_58);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
block_17:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_1 = x_12;
x_2 = x_15;
x_9 = x_14;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1(x_13, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_10;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_Syntax_getPos(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 1;
return x_5;
}
}
}
static lean_object* _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg___closed__1;
x_14 = l_List_find_x3f___rarg(x_13, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_box(0);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg___closed__1;
x_22 = l_List_find_x3f___rarg(x_21, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
return x_27;
}
}
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_8, 1);
lean_dec(x_14);
lean_ctor_set(x_8, 1, x_12);
x_15 = lean_st_ref_get(x_9, x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_5, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_List_isEmpty___rarg(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; 
lean_free_object(x_17);
x_23 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_23, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
if (x_2 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_4, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_4, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_4, 4);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_34 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 2);
x_35 = lean_ctor_get(x_4, 5);
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_32);
lean_ctor_set(x_36, 5, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*6, x_23);
lean_ctor_set_uint8(x_36, sizeof(void*)*6 + 1, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*6 + 2, x_34);
x_37 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_36);
x_38 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_37, x_23, x_36, x_5, x_6, x_7, x_8, x_9, x_27);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
x_42 = l_Lean_Elab_Term_synthesizeUsingDefault(x_4, x_5, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_46 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_23, x_23, x_36, x_5, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_50 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_23, x_37, x_4, x_5, x_6, x_7, x_8, x_9, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(x_4, x_5, x_6, x_7, x_8, x_9, x_53);
lean_dec(x_8);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_dec(x_50);
x_56 = lean_box(0);
x_57 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_56, x_4, x_5, x_6, x_7, x_8, x_9, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_50);
if (x_58 == 0)
{
return x_50;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_50, 0);
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_50);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_46, 1);
lean_inc(x_62);
lean_dec(x_46);
x_63 = lean_box(0);
x_64 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_63, x_4, x_5, x_6, x_7, x_8, x_9, x_62);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_46);
if (x_65 == 0)
{
return x_46;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_46, 0);
x_67 = lean_ctor_get(x_46, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_46);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_36);
x_69 = lean_ctor_get(x_42, 1);
lean_inc(x_69);
lean_dec(x_42);
x_70 = lean_box(0);
x_71 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_70, x_4, x_5, x_6, x_7, x_8, x_9, x_69);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_72 = !lean_is_exclusive(x_42);
if (x_72 == 0)
{
return x_42;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_42, 0);
x_74 = lean_ctor_get(x_42, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_42);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_36);
x_76 = lean_ctor_get(x_38, 1);
lean_inc(x_76);
lean_dec(x_38);
x_77 = lean_box(0);
x_78 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_77, x_4, x_5, x_6, x_7, x_8, x_9, x_76);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_79 = !lean_is_exclusive(x_38);
if (x_79 == 0)
{
return x_38;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_38, 0);
x_81 = lean_ctor_get(x_38, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_38);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_83 = !lean_is_exclusive(x_24);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_24, 0);
lean_dec(x_84);
x_85 = lean_box(0);
lean_ctor_set(x_24, 0, x_85);
return x_24;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_24, 1);
lean_inc(x_86);
lean_dec(x_24);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_24, 1);
lean_inc(x_89);
lean_dec(x_24);
x_90 = lean_box(0);
x_91 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_90, x_4, x_5, x_6, x_7, x_8, x_9, x_89);
return x_91;
}
}
else
{
uint8_t x_92; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_92 = !lean_is_exclusive(x_24);
if (x_92 == 0)
{
return x_24;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_24, 0);
x_94 = lean_ctor_get(x_24, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_24);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_96 = lean_box(0);
lean_ctor_set(x_17, 0, x_96);
return x_17;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_17, 0);
x_98 = lean_ctor_get(x_17, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_17);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_List_isEmpty___rarg(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
uint8_t x_101; lean_object* x_102; 
x_101 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_102 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_101, x_101, x_4, x_5, x_6, x_7, x_8, x_9, x_98);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_unbox(x_103);
lean_dec(x_103);
if (x_104 == 0)
{
if (x_2 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_ctor_get(x_4, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_4, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_4, 2);
lean_inc(x_108);
x_109 = lean_ctor_get(x_4, 3);
lean_inc(x_109);
x_110 = lean_ctor_get(x_4, 4);
lean_inc(x_110);
x_111 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_112 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 2);
x_113 = lean_ctor_get(x_4, 5);
lean_inc(x_113);
x_114 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_107);
lean_ctor_set(x_114, 2, x_108);
lean_ctor_set(x_114, 3, x_109);
lean_ctor_set(x_114, 4, x_110);
lean_ctor_set(x_114, 5, x_113);
lean_ctor_set_uint8(x_114, sizeof(void*)*6, x_101);
lean_ctor_set_uint8(x_114, sizeof(void*)*6 + 1, x_111);
lean_ctor_set_uint8(x_114, sizeof(void*)*6 + 2, x_112);
x_115 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_114);
x_116 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_115, x_101, x_114, x_5, x_6, x_7, x_8, x_9, x_105);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_unbox(x_117);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_dec(x_116);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
x_120 = l_Lean_Elab_Term_synthesizeUsingDefault(x_4, x_5, x_6, x_7, x_8, x_9, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_124 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_101, x_101, x_114, x_5, x_6, x_7, x_8, x_9, x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_128 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_101, x_115, x_4, x_5, x_6, x_7, x_8, x_9, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_unbox(x_129);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(x_4, x_5, x_6, x_7, x_8, x_9, x_131);
lean_dec(x_8);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_128, 1);
lean_inc(x_133);
lean_dec(x_128);
x_134 = lean_box(0);
x_135 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_134, x_4, x_5, x_6, x_7, x_8, x_9, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_136 = lean_ctor_get(x_128, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_128, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_138 = x_128;
} else {
 lean_dec_ref(x_128);
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
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_124, 1);
lean_inc(x_140);
lean_dec(x_124);
x_141 = lean_box(0);
x_142 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_141, x_4, x_5, x_6, x_7, x_8, x_9, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_143 = lean_ctor_get(x_124, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_124, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_114);
x_147 = lean_ctor_get(x_120, 1);
lean_inc(x_147);
lean_dec(x_120);
x_148 = lean_box(0);
x_149 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_148, x_4, x_5, x_6, x_7, x_8, x_9, x_147);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_150 = lean_ctor_get(x_120, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_120, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_152 = x_120;
} else {
 lean_dec_ref(x_120);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_114);
x_154 = lean_ctor_get(x_116, 1);
lean_inc(x_154);
lean_dec(x_116);
x_155 = lean_box(0);
x_156 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_155, x_4, x_5, x_6, x_7, x_8, x_9, x_154);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_157 = lean_ctor_get(x_116, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_116, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_159 = x_116;
} else {
 lean_dec_ref(x_116);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_161 = lean_ctor_get(x_102, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_162 = x_102;
} else {
 lean_dec_ref(x_102);
 x_162 = lean_box(0);
}
x_163 = lean_box(0);
if (lean_is_scalar(x_162)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_162;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_161);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_102, 1);
lean_inc(x_165);
lean_dec(x_102);
x_166 = lean_box(0);
x_167 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_166, x_4, x_5, x_6, x_7, x_8, x_9, x_165);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_168 = lean_ctor_get(x_102, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_102, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_170 = x_102;
} else {
 lean_dec_ref(x_102);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_172 = lean_box(0);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_98);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_174 = lean_ctor_get(x_8, 0);
x_175 = lean_ctor_get(x_8, 2);
x_176 = lean_ctor_get(x_8, 3);
x_177 = lean_ctor_get(x_8, 4);
x_178 = lean_ctor_get(x_8, 5);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_8);
x_179 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_179, 0, x_174);
lean_ctor_set(x_179, 1, x_12);
lean_ctor_set(x_179, 2, x_175);
lean_ctor_set(x_179, 3, x_176);
lean_ctor_set(x_179, 4, x_177);
lean_ctor_set(x_179, 5, x_178);
x_180 = lean_st_ref_get(x_9, x_10);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec(x_180);
x_182 = lean_st_ref_get(x_5, x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_185 = x_182;
} else {
 lean_dec_ref(x_182);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
x_187 = l_List_isEmpty___rarg(x_186);
lean_dec(x_186);
if (x_187 == 0)
{
uint8_t x_188; lean_object* x_189; 
lean_dec(x_185);
x_188 = 0;
lean_inc(x_9);
lean_inc(x_179);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_189 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_188, x_188, x_4, x_5, x_6, x_7, x_179, x_9, x_184);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_unbox(x_190);
lean_dec(x_190);
if (x_191 == 0)
{
if (x_2 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; 
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
lean_dec(x_189);
x_193 = lean_ctor_get(x_4, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_4, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_4, 2);
lean_inc(x_195);
x_196 = lean_ctor_get(x_4, 3);
lean_inc(x_196);
x_197 = lean_ctor_get(x_4, 4);
lean_inc(x_197);
x_198 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_199 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 2);
x_200 = lean_ctor_get(x_4, 5);
lean_inc(x_200);
x_201 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_201, 0, x_193);
lean_ctor_set(x_201, 1, x_194);
lean_ctor_set(x_201, 2, x_195);
lean_ctor_set(x_201, 3, x_196);
lean_ctor_set(x_201, 4, x_197);
lean_ctor_set(x_201, 5, x_200);
lean_ctor_set_uint8(x_201, sizeof(void*)*6, x_188);
lean_ctor_set_uint8(x_201, sizeof(void*)*6 + 1, x_198);
lean_ctor_set_uint8(x_201, sizeof(void*)*6 + 2, x_199);
x_202 = 1;
lean_inc(x_9);
lean_inc(x_179);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_201);
x_203 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_202, x_188, x_201, x_5, x_6, x_7, x_179, x_9, x_192);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_unbox(x_204);
lean_dec(x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
lean_dec(x_203);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
x_207 = l_Lean_Elab_Term_synthesizeUsingDefault(x_4, x_5, x_6, x_7, x_179, x_9, x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_unbox(x_208);
lean_dec(x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_210);
lean_dec(x_207);
lean_inc(x_9);
lean_inc(x_179);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_211 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_188, x_188, x_201, x_5, x_6, x_7, x_179, x_9, x_210);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; uint8_t x_213; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_unbox(x_212);
lean_dec(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec(x_211);
lean_inc(x_9);
lean_inc(x_179);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_215 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep(x_188, x_202, x_4, x_5, x_6, x_7, x_179, x_9, x_214);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; uint8_t x_217; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_unbox(x_216);
lean_dec(x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
lean_dec(x_215);
x_219 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars(x_4, x_5, x_6, x_7, x_179, x_9, x_218);
lean_dec(x_179);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_215, 1);
lean_inc(x_220);
lean_dec(x_215);
x_221 = lean_box(0);
x_222 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_221, x_4, x_5, x_6, x_7, x_179, x_9, x_220);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_179);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_223 = lean_ctor_get(x_215, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_215, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_225 = x_215;
} else {
 lean_dec_ref(x_215);
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
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_211, 1);
lean_inc(x_227);
lean_dec(x_211);
x_228 = lean_box(0);
x_229 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_228, x_4, x_5, x_6, x_7, x_179, x_9, x_227);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_179);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_230 = lean_ctor_get(x_211, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_211, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_232 = x_211;
} else {
 lean_dec_ref(x_211);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_201);
x_234 = lean_ctor_get(x_207, 1);
lean_inc(x_234);
lean_dec(x_207);
x_235 = lean_box(0);
x_236 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_235, x_4, x_5, x_6, x_7, x_179, x_9, x_234);
return x_236;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_201);
lean_dec(x_179);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_237 = lean_ctor_get(x_207, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_207, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_239 = x_207;
} else {
 lean_dec_ref(x_207);
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
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_201);
x_241 = lean_ctor_get(x_203, 1);
lean_inc(x_241);
lean_dec(x_203);
x_242 = lean_box(0);
x_243 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_242, x_4, x_5, x_6, x_7, x_179, x_9, x_241);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_201);
lean_dec(x_179);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_244 = lean_ctor_get(x_203, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_203, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_246 = x_203;
} else {
 lean_dec_ref(x_203);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_179);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_248 = lean_ctor_get(x_189, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_249 = x_189;
} else {
 lean_dec_ref(x_189);
 x_249 = lean_box(0);
}
x_250 = lean_box(0);
if (lean_is_scalar(x_249)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_249;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_248);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_189, 1);
lean_inc(x_252);
lean_dec(x_189);
x_253 = lean_box(0);
x_254 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_253, x_4, x_5, x_6, x_7, x_179, x_9, x_252);
return x_254;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_179);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_255 = lean_ctor_get(x_189, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_189, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_257 = x_189;
} else {
 lean_dec_ref(x_189);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
else
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_179);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_259 = lean_box(0);
if (lean_is_scalar(x_185)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_185;
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_184);
return x_260;
}
}
}
}
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg(x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_7, 1);
x_15 = lean_ctor_get(x_7, 2);
x_16 = lean_ctor_get(x_7, 3);
x_17 = l_Lean_replaceRef(x_11, x_16);
lean_dec(x_16);
lean_dec(x_11);
lean_inc(x_15);
lean_inc(x_14);
lean_ctor_set(x_7, 3, x_17);
x_18 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___lambda__1(x_14, x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_14);
x_21 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_22 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
x_29 = lean_ctor_get(x_7, 2);
x_30 = lean_ctor_get(x_7, 3);
x_31 = lean_ctor_get(x_7, 4);
x_32 = lean_ctor_get(x_7, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_33 = l_Lean_replaceRef(x_11, x_30);
lean_dec(x_30);
lean_dec(x_11);
lean_inc(x_29);
lean_inc(x_28);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_31);
lean_ctor_set(x_34, 5, x_32);
x_35 = lean_nat_dec_eq(x_28, x_29);
lean_dec(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(0);
x_37 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___lambda__1(x_28, x_1, x_36, x_3, x_4, x_5, x_6, x_34, x_8, x_12);
lean_dec(x_28);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_28);
x_38 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_39 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_38, x_3, x_4, x_5, x_6, x_34, x_8, x_12);
lean_dec(x_8);
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_box(0);
x_10 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_8, x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_withSynthesize___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_43; lean_object* x_44; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_4, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_70 = lean_st_ref_get(x_8, x_14);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_st_ref_take(x_4, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = !lean_is_exclusive(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_73, 1);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_73, 1, x_77);
x_78 = lean_st_ref_set(x_4, x_73, x_74);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_80 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_84 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_83, x_3, x_4, x_5, x_6, x_7, x_8, x_82);
if (lean_obj_tag(x_84) == 0)
{
if (x_2 == 0)
{
lean_object* x_85; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_16 = x_81;
x_17 = x_85;
goto block_42;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_87 = l_Lean_Elab_Term_synthesizeUsingDefault(x_3, x_4, x_5, x_6, x_7, x_8, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_16 = x_81;
x_17 = x_90;
goto block_42;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_dec(x_87);
lean_inc(x_8);
lean_inc(x_4);
x_92 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_83, x_3, x_4, x_5, x_6, x_7, x_8, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_16 = x_81;
x_17 = x_93;
goto block_42;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_81);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_43 = x_94;
x_44 = x_95;
goto block_69;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_81);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_96 = lean_ctor_get(x_87, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_87, 1);
lean_inc(x_97);
lean_dec(x_87);
x_43 = x_96;
x_44 = x_97;
goto block_69;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_81);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_98 = lean_ctor_get(x_84, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_84, 1);
lean_inc(x_99);
lean_dec(x_84);
x_43 = x_98;
x_44 = x_99;
goto block_69;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_100 = lean_ctor_get(x_80, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_80, 1);
lean_inc(x_101);
lean_dec(x_80);
x_43 = x_100;
x_44 = x_101;
goto block_69;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_102 = lean_ctor_get(x_73, 0);
x_103 = lean_ctor_get(x_73, 2);
x_104 = lean_ctor_get(x_73, 3);
x_105 = lean_ctor_get(x_73, 4);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_73);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_107, 0, x_102);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_107, 2, x_103);
lean_ctor_set(x_107, 3, x_104);
lean_ctor_set(x_107, 4, x_105);
x_108 = lean_st_ref_set(x_4, x_107, x_74);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_110 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_114 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_113, x_3, x_4, x_5, x_6, x_7, x_8, x_112);
if (lean_obj_tag(x_114) == 0)
{
if (x_2 == 0)
{
lean_object* x_115; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_16 = x_111;
x_17 = x_115;
goto block_42;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_117 = l_Lean_Elab_Term_synthesizeUsingDefault(x_3, x_4, x_5, x_6, x_7, x_8, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_unbox(x_118);
lean_dec(x_118);
if (x_119 == 0)
{
lean_object* x_120; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_16 = x_111;
x_17 = x_120;
goto block_42;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_117, 1);
lean_inc(x_121);
lean_dec(x_117);
lean_inc(x_8);
lean_inc(x_4);
x_122 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_2, x_113, x_3, x_4, x_5, x_6, x_7, x_8, x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_16 = x_111;
x_17 = x_123;
goto block_42;
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_111);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
x_43 = x_124;
x_44 = x_125;
goto block_69;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_111);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_126 = lean_ctor_get(x_117, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_117, 1);
lean_inc(x_127);
lean_dec(x_117);
x_43 = x_126;
x_44 = x_127;
goto block_69;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_111);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_128 = lean_ctor_get(x_114, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_114, 1);
lean_inc(x_129);
lean_dec(x_114);
x_43 = x_128;
x_44 = x_129;
goto block_69;
}
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_130 = lean_ctor_get(x_110, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_110, 1);
lean_inc(x_131);
lean_dec(x_110);
x_43 = x_130;
x_44 = x_131;
goto block_69;
}
}
block_42:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_st_ref_get(x_8, x_17);
lean_dec(x_8);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_take(x_4, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_21, 1);
x_25 = l_List_append___rarg(x_24, x_15);
lean_ctor_set(x_21, 1, x_25);
x_26 = lean_st_ref_set(x_4, x_21, x_22);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_16);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
x_33 = lean_ctor_get(x_21, 2);
x_34 = lean_ctor_get(x_21, 3);
x_35 = lean_ctor_get(x_21, 4);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_36 = l_List_append___rarg(x_32, x_15);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_33);
lean_ctor_set(x_37, 3, x_34);
lean_ctor_set(x_37, 4, x_35);
x_38 = lean_st_ref_set(x_4, x_37, x_22);
lean_dec(x_4);
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
lean_ctor_set(x_41, 0, x_16);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
block_69:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_st_ref_get(x_8, x_44);
lean_dec(x_8);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_st_ref_take(x_4, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_48, 1);
x_52 = l_List_append___rarg(x_51, x_15);
lean_ctor_set(x_48, 1, x_52);
x_53 = lean_st_ref_set(x_4, x_48, x_49);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 0, x_43);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_43);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_58 = lean_ctor_get(x_48, 0);
x_59 = lean_ctor_get(x_48, 1);
x_60 = lean_ctor_get(x_48, 2);
x_61 = lean_ctor_get(x_48, 3);
x_62 = lean_ctor_get(x_48, 4);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_48);
x_63 = l_List_append___rarg(x_59, x_15);
x_64 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
x_65 = lean_st_ref_set(x_4, x_64, x_49);
lean_dec(x_4);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
 lean_ctor_set_tag(x_68, 1);
}
lean_ctor_set(x_68, 0, x_43);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
lean_object* l_Lean_Elab_Term_withSynthesize(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withSynthesize___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_withSynthesize___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Elab_Term_withSynthesize___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabTermAndSynthesize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = 1;
x_11 = lean_box(x_10);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 10, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_11);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_7, 3);
x_15 = l_Lean_replaceRef(x_1, x_14);
lean_dec(x_14);
lean_dec(x_1);
lean_ctor_set(x_7, 3, x_15);
x_16 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Elab_Term_withSynthesize___rarg(x_12, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_instantiateMVarsImp(x_18, x_5, x_6, x_7, x_8, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
x_27 = lean_ctor_get(x_7, 2);
x_28 = lean_ctor_get(x_7, 3);
x_29 = lean_ctor_get(x_7, 4);
x_30 = lean_ctor_get(x_7, 5);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_31 = l_Lean_replaceRef(x_1, x_28);
lean_dec(x_28);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 5, x_30);
x_33 = 0;
lean_inc(x_8);
lean_inc(x_32);
lean_inc(x_6);
lean_inc(x_5);
x_34 = l_Lean_Elab_Term_withSynthesize___rarg(x_12, x_33, x_3, x_4, x_5, x_6, x_32, x_8, x_9);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Meta_instantiateMVarsImp(x_35, x_5, x_6, x_32, x_8, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_32);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_40 = x_34;
} else {
 lean_dec_ref(x_34);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_ForEachExpr(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_SyntheticMVars(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_liftTacticElabM___rarg___closed__1 = _init_l_Lean_Elab_Term_liftTacticElabM___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_liftTacticElabM___rarg___closed__1);
l_Lean_Elab_Term_runTactic___closed__1 = _init_l_Lean_Elab_Term_runTactic___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_runTactic___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__2);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__3 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingInstMVar___lambda__1___closed__3);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar___lambda__1___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar___lambda__1___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar___lambda__1___closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizePendingCoeInstMVar___lambda__1___closed__2);
l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__1 = _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__1();
lean_mark_persistent(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__1);
l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__2 = _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__2();
lean_mark_persistent(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__2);
l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__3 = _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__3();
lean_mark_persistent(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__3);
l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__4 = _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__4();
lean_mark_persistent(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__4);
l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__5 = _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__5();
lean_mark_persistent(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__5);
l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__6 = _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__6();
lean_mark_persistent(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__6);
l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__7 = _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__7();
lean_mark_persistent(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__7);
l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__8 = _init_l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__8();
lean_mark_persistent(l_List_filterAuxM___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__1___closed__8);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__1);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__2 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__2();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__2);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__3 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__3();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__3);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__4 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__4();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__4);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__5 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__5();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__5);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__6 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__6();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__6);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__7 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__7();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__7);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__8 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__8();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__8);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__9 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__9();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__9);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__10 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__10();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___closed__10);
l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__1 = _init_l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__1);
l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__2 = _init_l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__2);
l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__3 = _init_l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_commitWhenSome_x3f___at_Lean_Elab_Term_tryToSynthesizeUsingDefaultInstance___spec__3___lambda__1___closed__3);
l_Lean_Elab_Term_synthesizeUsingDefault___closed__1 = _init_l_Lean_Elab_Term_synthesizeUsingDefault___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_synthesizeUsingDefault___closed__1);
l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__1 = _init_l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__1);
l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__2 = _init_l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__2);
l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__3 = _init_l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__3();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___lambda__1___closed__3);
l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___closed__1 = _init_l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___closed__1);
l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___closed__2 = _init_l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___closed__2();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___closed__2);
l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___closed__3 = _init_l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___closed__3();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_reportStuckSyntheticMVars___spec__1___closed__3);
l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg___closed__1 = _init_l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_getSomeSynthethicMVarsRef___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
