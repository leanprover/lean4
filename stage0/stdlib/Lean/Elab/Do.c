// Lean compiler output
// Module: Lean.Elab.Do
// Imports: Init Lean.Elab.Term Lean.Elab.Binders Lean.Elab.Quotation Lean.Elab.Match
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
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__1;
lean_object* l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4;
lean_object* l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__8;
lean_object* l_Lean_Elab_Term_Do_ToTerm_returnToTermCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__11;
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__2;
lean_object* l_Lean_mkAppStx(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__22;
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__17;
extern lean_object* l_Lean_unitToExpr___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Do_8__getDoSeq(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__4;
lean_object* l_Lean_Elab_Term_Do_convertReturnIntoJmpAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___closed__3;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_eraseVars___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__3;
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__2;
lean_object* l_Lean_Elab_Term_Do_mkUnless___closed__2;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_14__mkForInMapYield(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_getLetIdDeclVar(lean_object*);
lean_object* l_Lean_Elab_Term_Do_getLetPatDeclVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__33;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkJmp(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__2;
extern lean_object* l_Lean_fieldIdxKind___closed__2;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__17;
lean_object* l_Lean_Elab_Term_Do_getDoIdDeclVar___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__15;
uint8_t l_Lean_Elab_Term_Do_hasExitPoint___main(lean_object*);
lean_object* l___private_Lean_Elab_Do_5__nameSetToArray(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_hasExitPoint___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_withFor___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__31;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__2;
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__3;
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__8;
lean_object* l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__10;
lean_object* l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__1;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveLocalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__40;
lean_object* l_Lean_Elab_Term_Do_ToTerm_continueToTermCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__9;
lean_object* l_Lean_Elab_Term_Do_elabDo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_extendUpdatedVarsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__13;
lean_object* l___private_Lean_Elab_Do_10__mkDoIfView(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_mkReturnUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_getDoLetRecVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__4;
lean_object* l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_Do_hasContinueBreak___main(lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__2;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__27;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_mkJmp___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_9__expandDoIf(lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__13;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__27;
extern lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_12__mkTuple___spec__1___closed__1;
lean_object* l___private_Lean_Elab_Do_13__mkForInYield___closed__3;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__2;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_Do_attachJPs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_toTerm___main___closed__1;
extern lean_object* l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__9;
lean_object* l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__8;
lean_object* l_Lean_Elab_Term_Do_mkFreshJP___closed__1;
lean_object* l_Lean_Elab_Term_Do_mkJmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_mkFreshJP___closed__4;
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__10;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__2___rarg(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_getDoPatDeclVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__9;
lean_object* l___private_Lean_Elab_Do_14__mkForInMapYield___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__8;
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
lean_object* l___private_Lean_Elab_Do_15__expandLiftMethodAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__4;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__35;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__5;
lean_object* l_Lean_Elab_Term_Do_hasContinueBreak___main___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkResultUVarTuple___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__7;
lean_object* l_Lean_Elab_Term_Do_Code_inhabited;
lean_object* l_Lean_Meta_mkAppM___at___private_Lean_Elab_Term_7__isMonad_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_11__mkPUnit___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__36;
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_13__mkForInYield___closed__10;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_elabDo___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__7;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__9;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__3___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__13;
lean_object* l_Lean_Elab_Term_Do_mkFreshJP___closed__2;
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__41;
lean_object* l_Lean_Elab_Term_Do_ToTerm_returnToTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__12;
extern lean_object* l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__9;
lean_object* l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2;
extern lean_object* l_EST_Monad___closed__1;
lean_object* l___private_Lean_Elab_Do_4__varsToMessageData(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__34;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Do_13__mkForInYield___closed__5;
lean_object* l_Lean_Elab_Term_synthesizeInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__1;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_12__mkTuple___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_assert___closed__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__7;
lean_object* l_List_map___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__1(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_mkReassignCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__8;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
lean_object* l___private_Lean_Elab_Do_13__mkForInYield___closed__14;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__4;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__23;
lean_object* l___private_Lean_Elab_Do_1__hasLiftMethod___boxed(lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__25;
lean_object* l_Lean_Elab_Term_Do_eraseVars(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabParen___closed__5;
lean_object* l___private_Lean_Elab_Do_12__mkTuple___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_mkFreshJP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_expandLiftMethod(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__19;
lean_object* l_Lean_Elab_Term_Do_hasContinueBreak___boxed(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___closed__3;
lean_object* l_Lean_Elab_Term_elabLiftMethod___closed__1;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__20;
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__2;
lean_object* l___private_Lean_Elab_Do_9__expandDoIf___closed__1;
lean_object* l_Lean_Elab_Term_Do_elabDo___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_mkFreshJP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__10;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__32;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__24;
lean_object* l___private_Lean_Elab_Do_2__mkIdBindFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__2;
lean_object* l_Lean_Elab_Term_Do_mkJmp___closed__2;
lean_object* l_Lean_Elab_Term_Do_pullExitPointsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__1;
lean_object* l___private_Lean_Elab_Do_2__mkIdBindFor___closed__1;
lean_object* l_Lean_Elab_Term_Do_eraseOptVar(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__3;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_convertReturnIntoJmp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__11;
lean_object* l_Lean_Elab_Term_Do_addFreshJP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__3;
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__9;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_eraseVars___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_13__mkForInYield(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__7;
lean_object* l_Lean_Meta_assignExprMVar___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTermCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLiftMethod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkJoinPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__20;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Do_15__expandLiftMethodAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_2__mkIdBindFor___closed__2;
extern lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__1;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__29;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_setBlack___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_Do_getLetDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__8;
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__15;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_processInaccessibleAsCtor___closed__1;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__18;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__13;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___closed__1;
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__10;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_getDoLetVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__9;
lean_object* l___private_Lean_Elab_Do_3__extractBind___closed__3;
lean_object* l_Lean_Elab_Term_Do_attachJPs(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__19;
lean_object* l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__1;
lean_object* l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_mkFreshJP___closed__3;
lean_object* l_Lean_Elab_Term_Do_eraseVars___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_2__mkIdBindFor___closed__3;
lean_object* l_Lean_Elab_Term_Do_mkUnless___closed__6;
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__5;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__25;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__1;
lean_object* l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__7;
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__14;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkUVarTuple___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_addFreshJP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__12;
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabTermQuot___closed__1;
extern lean_object* l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__10;
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__13;
lean_object* l___private_Lean_Elab_Do_3__extractBind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_9__expandDoIf___closed__3;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_copyInfo(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_homogenize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__6;
uint8_t l_Lean_Elab_Term_Do_hasExitPoint(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_continueToTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_mkUnless___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__6;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_getDoIdDeclVar(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_withNewVars___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__6;
lean_object* l___private_Lean_Elab_Do_3__extractBind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_Do_pullExitPointsAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_mkBreak(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_pullExitPointsAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_attachJPs___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__5;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___closed__2;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_RBNode_isBlack___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Do_11__mkPUnit(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_15__expandLiftMethodAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__3;
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__12;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_CodeBlock_toMessageData(lean_object*);
lean_object* l___private_Lean_Elab_Do_1__hasLiftMethod___main___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__9;
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__4;
extern lean_object* l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__27;
lean_object* l___private_Lean_Elab_Do_17__regTraceClasses(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__3;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_getDoLetRecVars___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_Do_hasContinueBreak(lean_object*);
extern lean_object* l_Lean_unitToExpr___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_Do_ToTerm_toTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__4;
lean_object* l_Array_filterMapMAux___main___at_Lean_Elab_Term_Do_getLetPatDeclVars___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__3;
extern lean_object* l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__6;
lean_object* l___private_Lean_Elab_Do_3__extractBind___closed__2;
uint8_t l_Std_RBNode_any___main___at_Lean_Elab_Term_Do_extendUpdatedVars___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__11;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_withFor(lean_object*);
lean_object* l___private_Lean_Elab_Do_9__expandDoIf___closed__2;
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__26;
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__1;
lean_object* l___private_Lean_Elab_Do_13__mkForInYield___closed__6;
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__6;
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__6;
lean_object* l___private_Lean_Elab_Do_3__extractBind___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandOptType(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2;
lean_object* l_List_map___main___at___private_Lean_Elab_Do_4__varsToMessageData___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_Do_mkJmp___closed__3;
lean_object* l___private_Lean_CoreM_1__mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l_Lean_Elab_Term_Do_getDoReassignVars___closed__3;
extern lean_object* l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__14;
lean_object* l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4;
lean_object* l___private_Lean_Elab_Do_16__mkMonadAlias___closed__6;
lean_object* l_Lean_Elab_Term_Do_extendUpdatedVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__31;
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_mkReturnUnit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__3;
lean_object* l_Lean_Elab_Term_Do_mkUnless___closed__8;
lean_object* l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__1;
lean_object* l_Array_filterMapMAux___main___at_Lean_Elab_Term_Do_getLetPatDeclVars___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_mkUnless___closed__4;
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__16;
extern lean_object* l___private_Lean_Elab_Term_4__expandCDot___main___closed__2;
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__30;
lean_object* l_Lean_Elab_Term_Do_getLetEqnsDeclVar___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__5;
lean_object* l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__4;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__18;
extern lean_object* l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__2;
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Do_elabDo___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1(lean_object*);
lean_object* l_Std_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___closed__2;
uint8_t l___private_Lean_Elab_Do_1__hasLiftMethod___main(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_Do_elabDo(lean_object*);
lean_object* l_Std_RBNode_appendTrees___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_withNewVars___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__28;
lean_object* l___private_Lean_Elab_Do_16__mkMonadAlias___closed__4;
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__3;
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTermCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_insertVars(lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__26;
lean_object* l___private_Lean_Elab_Do_7__getDoSeqElems(lean_object*);
lean_object* l_Lean_Elab_Term_Do_mkUnless(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_mkJmp___closed__5;
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_8__getDoSeq___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__6;
extern lean_object* l_Lean_Parser_FirstTokens_toStr___closed__3;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__16;
extern lean_object* l_Lean_NameSet_empty;
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__20;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_getDoLetArrowVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_12__mkTuple(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__22;
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__10;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_pullExitPointsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_fold___main___at___private_Lean_Elab_Do_6__union___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__12;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_mkFreshJP_x27___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__2;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLiftMethod___closed__3;
lean_object* l___private_Lean_Elab_Do_6__union(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Elab_Term_Do_getLetDeclVars___closed__3;
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__15;
lean_object* l_Lean_Elab_Term_Do_pullExitPointsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__6;
lean_object* l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_mkUnless___closed__7;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_12__mkTuple___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_Alt_toMessageData___closed__4;
lean_object* l_Lean_Elab_Term_Do_ToTerm_returnToTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Do_elabDo___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_16__mkMonadAlias___closed__2;
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__29;
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l___private_Lean_Elab_Do_16__mkMonadAlias___closed__1;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___closed__3;
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__8;
lean_object* l_Lean_Elab_Term_getPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabLiftMethod(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_getDoLetRecVars___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_del___main___at_Lean_Elab_Term_Do_eraseVars___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkJmp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_concat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__10;
extern lean_object* l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__16;
lean_object* l_Lean_Elab_Term_Do_mkUnless___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_2__mkIdBindFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__24;
lean_object* l_Lean_Macro_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__3;
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__16;
lean_object* l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_getDoPatDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__14;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__7;
extern lean_object* l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__18;
lean_object* l_Lean_Elab_Term_Do_mkIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_hasContinueBreak___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_toDoSeq(lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
lean_object* l_Lean_Elab_Term_Do_getDoLetRecVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_pullExitPoints(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_getDoLetRecVars___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l___private_Lean_Elab_Do_16__mkMonadAlias___closed__5;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__37;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__42;
lean_object* l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__3;
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__11;
lean_object* l_Lean_Elab_Term_Do_addFreshJP_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__13;
lean_object* l_Lean_Elab_Term_Do_ToTerm_reassignToTerm(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
extern lean_object* l_Lean_Meta_caseValueAux___lambda__5___closed__8;
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkUVarTuple(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_mkUnless___closed__1;
lean_object* l___private_Lean_Elab_Util_5__expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__6;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__2___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__8;
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__24;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_getDoReassignVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_mkFreshJP_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___closed__1;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_Do_attachJPs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___closed__1;
extern lean_object* l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__12;
lean_object* l___private_Lean_Elab_Do_16__mkMonadAlias___closed__3;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__2___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_object* l_Lean_Elab_Term_Do_mkAction(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___closed__2;
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__7;
lean_object* l_Lean_Elab_Term_elabLiftMethod___closed__2;
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__4;
extern lean_object* l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__13;
lean_object* l_Lean_Elab_Term_Do_Code_inhabited___closed__1;
extern lean_object* l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__7;
lean_object* l_Lean_Elab_Term_Do_elabDo___closed__1;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__18;
lean_object* l_Lean_Elab_Term_Do_mkVarDeclCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__2(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l_Lean_Elab_Term_Do_getLetEqnsDeclVar(lean_object*);
lean_object* l___private_Lean_Elab_Do_13__mkForInYield___closed__7;
lean_object* l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__7;
lean_object* l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__5;
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkResultUVarTuple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__7;
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__13;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__21;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__38;
lean_object* l_Lean_Elab_Term_Do_Alt_inhabited___closed__1;
lean_object* l_Lean_mkStxStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__21;
uint8_t l___private_Lean_Elab_Do_1__hasLiftMethod(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__2;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_attachJP___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Do_1__hasLiftMethod___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabLetDeclCore___closed__4;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_pullExitPointsAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_13__mkForInYield___closed__4;
lean_object* l___private_Lean_Elab_Do_13__mkForInYield___closed__11;
lean_object* l_List_toString___at___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___spec__1(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Elab_Term_elabLiftMethod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Elab_Term_Do_elabDo___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkUVarTuple___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__1;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_4__expandCDot___main___closed__3;
lean_object* l_Lean_Elab_Term_Do_mkJmp___closed__1;
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__14;
lean_object* l_Std_RBNode_del___main___at_Lean_Elab_Term_Do_eraseVars___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_getLetDeclVars___closed__2;
lean_object* l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__5;
lean_object* l_Lean_Elab_Term_Do_mkJmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
lean_object* l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_Do_mkFreshJP___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracer_trace___at_Lean_Elab_Term_Do_elabDo___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_13__mkForInYield___closed__8;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Term_Do_CodeBlock_toMessageData___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_Do_mkContinue(lean_object*);
lean_object* l_Lean_Elab_Term_Do_getLetPatDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__9;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_mkReassignCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__2;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__1;
lean_object* l_Lean_Elab_Term_Do_getLetDeclVars___closed__1;
lean_object* l_Lean_Elab_Term_Do_getLetDeclVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_Do_13__mkForInYield___closed__2;
lean_object* l_Lean_Elab_Term_Do_ToTerm_toTerm___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_mkReturn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_mkReassignCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__4;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_Do_elabDo___closed__1;
lean_object* l___private_Lean_Elab_Do_13__mkForInYield___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracer_trace___at_Lean_Elab_Term_Do_elabDo___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__1;
lean_object* l___private_Lean_Elab_Do_13__mkForInYield___closed__1;
lean_object* l_Lean_indentD(lean_object*);
lean_object* l___private_Lean_Elab_Do_13__mkForInYield___closed__9;
extern lean_object* l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__11;
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__8;
lean_object* l_Std_RBNode_erase___at_Lean_Elab_Term_Do_eraseVars___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_getLetIdDeclVar___boxed(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_Do_mkFreshJP___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_attachJP(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__23;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__26;
lean_object* l_Lean_Elab_Term_Do_insertVars___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__3;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__11;
extern lean_object* l_Lean_Meta_mkPure___rarg___closed__4;
lean_object* l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_Do_pullExitPointsAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_erase___at_Lean_Elab_Term_Do_eraseVars___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__17;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__12;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_simp_macro_scopes(lean_object*);
lean_object* l_Lean_Elab_Term_Do_mkJmp___closed__4;
lean_object* l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__1;
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Elab_Term_Do_elabDo___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__6;
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__2;
extern lean_object* l_IO_Prim_fopenFlags___closed__1;
extern lean_object* l_System_FilePath_dirName___closed__1;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_hasExitPoint___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkUVarTuple___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_hasContinueBreak___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_mkJmp___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__1;
lean_object* l_Lean_Elab_Term_Do_getDoReassignVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__5;
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__2;
lean_object* l___private_Lean_Elab_Do_16__mkMonadAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__12;
extern lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__3;
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkIte___closed__1;
lean_object* l_Lean_Elab_Term_Do_getDoLetArrowVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_any___main___at_Lean_Elab_Term_Do_extendUpdatedVars___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_2__mkIdBindFor___closed__4;
lean_object* l_ReaderT_inhabited___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Std_RBNode_fold___main___at_Lean_registerTagAttribute___spec__1(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_hasExitPoint___main___boxed(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_13__mkForInYield___closed__13;
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__6;
lean_object* l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__5;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_Inhabited___closed__1;
lean_object* l_Lean_Elab_Term_Do_getDoReassignVars___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___closed__3;
lean_object* l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__6;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__19;
lean_object* l_Lean_Elab_Term_Do_mkFreshJP_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__16;
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__12;
lean_object* l_Lean_Elab_Term_Do_mkUnless___closed__5;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
lean_object* l_List_map___main___at___private_Lean_Elab_Do_7__getDoSeqElems___spec__1(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Do_1__hasLiftMethod___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel___at___private_Lean_Elab_Term_9__tryLiftAndCoe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__39;
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__5;
lean_object* l_Lean_Elab_Term_Do_getDoLetVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__18;
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__5;
extern lean_object* l___private_Lean_Elab_Util_6__regTraceClasses___closed__1;
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__25;
lean_object* l___private_Lean_Elab_Do_13__mkForInYield___closed__12;
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__2;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__14;
lean_object* l_Lean_Elab_Term_Do_hasExitPoint___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__28;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_withNewVars(lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__6;
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__15;
lean_object* l_Lean_Elab_Term_Do_addFreshJP_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Do_4__varsToMessageData___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__13;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_continueToTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__30;
extern lean_object* l_Lean_Meta_mkArrow___rarg___closed__2;
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__6;
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Elab_Term_Do_Alt_inhabited;
lean_object* l_Lean_Elab_Term_Do_getDoReassignVars___closed__2;
lean_object* _init_l_Lean_Elab_Term_elabLiftMethod___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of `(<- ...)`, must be nested inside a 'do' expression");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabLiftMethod___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLiftMethod___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabLiftMethod___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabLiftMethod___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabLiftMethod(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_elabLiftMethod___closed__3;
x_11 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabLiftMethod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabLiftMethod(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("liftMethod");
return x_1;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabLiftMethod___boxed), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabLiftMethod(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Do_1__hasLiftMethod___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l___private_Lean_Elab_Do_1__hasLiftMethod___main(x_7);
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
lean_object* _init_l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("do");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doSeqIndent");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doSeqBracketed");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l___private_Lean_Elab_Do_1__hasLiftMethod___main(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2;
x_5 = lean_name_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4;
x_7 = lean_name_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__6;
x_9 = lean_name_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTermQuot___closed__1;
x_11 = lean_name_eq(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__2;
x_13 = lean_name_eq(x_2, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_array_get_size(x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Do_1__hasLiftMethod___main___spec__1(x_3, x_3, x_14, x_15);
lean_dec(x_14);
return x_16;
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
else
{
uint8_t x_20; 
x_20 = 0;
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = 0;
return x_22;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Do_1__hasLiftMethod___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Do_1__hasLiftMethod___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Do_1__hasLiftMethod___main___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Do_1__hasLiftMethod___main(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l___private_Lean_Elab_Do_1__hasLiftMethod(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Elab_Do_1__hasLiftMethod___main(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Do_1__hasLiftMethod___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Do_1__hasLiftMethod(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Do_2__mkIdBindFor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Id");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Do_2__mkIdBindFor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Do_2__mkIdBindFor___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Do_2__mkIdBindFor___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hasBind");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Do_2__mkIdBindFor___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Do_2__mkIdBindFor___closed__2;
x_2 = l___private_Lean_Elab_Do_2__mkIdBindFor___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Do_2__mkIdBindFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_Meta_getDecLevel___at___private_Lean_Elab_Term_9__tryLiftAndCoe___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l___private_Lean_Elab_Do_2__mkIdBindFor___closed__2;
lean_inc(x_13);
x_15 = l_Lean_mkConst(x_14, x_13);
x_16 = l___private_Lean_Elab_Do_2__mkIdBindFor___closed__4;
x_17 = l_Lean_mkConst(x_16, x_13);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___private_Lean_Elab_Do_2__mkIdBindFor___closed__2;
lean_inc(x_22);
x_24 = l_Lean_mkConst(x_23, x_22);
x_25 = l___private_Lean_Elab_Do_2__mkIdBindFor___closed__4;
x_26 = l_Lean_mkConst(x_25, x_22);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_1);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_20);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
return x_9;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l___private_Lean_Elab_Do_2__mkIdBindFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Do_2__mkIdBindFor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* _init_l___private_Lean_Elab_Do_3__extractBind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid do notation, expected type is not available");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Do_3__extractBind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Do_3__extractBind___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Do_3__extractBind___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Do_3__extractBind___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Do_3__extractBind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_Do_3__extractBind___closed__3;
x_10 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 2);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = 2;
lean_ctor_set_uint8(x_11, 5, x_16);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_12, x_2, x_3, x_17, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_44; uint8_t x_45; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_44 = l_Lean_Expr_getAppFn___main(x_19);
x_45 = l_Lean_Expr_isMVar(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
x_21 = x_20;
goto block_43;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_19);
x_46 = l___private_Lean_Elab_Do_3__extractBind___closed__3;
x_47 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
block_43:
{
if (lean_obj_tag(x_19) == 5)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
x_24 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_22);
x_25 = lean_array_push(x_24, x_22);
x_26 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__6;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l_Lean_Meta_mkAppM___at___private_Lean_Elab_Term_7__isMonad_x3f___spec__1(x_26, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_30 = l_Lean_Elab_Term_synthesizeInst(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_23);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_22);
lean_ctor_set(x_36, 1, x_23);
lean_ctor_set(x_36, 2, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_23);
lean_dec(x_22);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = l___private_Lean_Elab_Do_2__mkIdBindFor(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_38);
lean_dec(x_2);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_23);
lean_dec(x_22);
x_40 = lean_ctor_get(x_27, 1);
lean_inc(x_40);
lean_dec(x_27);
x_41 = l___private_Lean_Elab_Do_2__mkIdBindFor(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_40);
lean_dec(x_2);
return x_41;
}
}
else
{
lean_object* x_42; 
x_42 = l___private_Lean_Elab_Do_2__mkIdBindFor(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_2);
return x_42;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_18);
if (x_52 == 0)
{
return x_18;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_18, 0);
x_54 = lean_ctor_get(x_18, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_18);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_56 = lean_ctor_get_uint8(x_11, 0);
x_57 = lean_ctor_get_uint8(x_11, 1);
x_58 = lean_ctor_get_uint8(x_11, 2);
x_59 = lean_ctor_get_uint8(x_11, 3);
x_60 = lean_ctor_get_uint8(x_11, 4);
x_61 = lean_ctor_get_uint8(x_11, 6);
x_62 = lean_ctor_get_uint8(x_11, 7);
lean_dec(x_11);
x_63 = 2;
x_64 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_64, 0, x_56);
lean_ctor_set_uint8(x_64, 1, x_57);
lean_ctor_set_uint8(x_64, 2, x_58);
lean_ctor_set_uint8(x_64, 3, x_59);
lean_ctor_set_uint8(x_64, 4, x_60);
lean_ctor_set_uint8(x_64, 5, x_63);
lean_ctor_set_uint8(x_64, 6, x_61);
lean_ctor_set_uint8(x_64, 7, x_62);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_13);
lean_ctor_set(x_65, 2, x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_66 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_12, x_2, x_3, x_65, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_90; uint8_t x_91; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_90 = l_Lean_Expr_getAppFn___main(x_67);
x_91 = l_Lean_Expr_isMVar(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
x_69 = x_68;
goto block_89;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_67);
x_92 = l___private_Lean_Elab_Do_3__extractBind___closed__3;
x_93 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_92, x_2, x_3, x_4, x_5, x_6, x_7, x_68);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
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
block_89:
{
if (lean_obj_tag(x_67) == 5)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
x_72 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_70);
x_73 = lean_array_push(x_72, x_70);
x_74 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__6;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_75 = l_Lean_Meta_mkAppM___at___private_Lean_Elab_Term_7__isMonad_x3f___spec__1(x_74, x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_69);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_78 = l_Lean_Elab_Term_synthesizeInst(x_76, x_2, x_3, x_4, x_5, x_6, x_7, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_67);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_70);
lean_ctor_set(x_82, 1, x_71);
lean_ctor_set(x_82, 2, x_79);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_71);
lean_dec(x_70);
x_84 = lean_ctor_get(x_78, 1);
lean_inc(x_84);
lean_dec(x_78);
x_85 = l___private_Lean_Elab_Do_2__mkIdBindFor(x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_84);
lean_dec(x_2);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_71);
lean_dec(x_70);
x_86 = lean_ctor_get(x_75, 1);
lean_inc(x_86);
lean_dec(x_75);
x_87 = l___private_Lean_Elab_Do_2__mkIdBindFor(x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_86);
lean_dec(x_2);
return x_87;
}
}
else
{
lean_object* x_88; 
x_88 = l___private_Lean_Elab_Do_2__mkIdBindFor(x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_69);
lean_dec(x_2);
return x_88;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_98 = lean_ctor_get(x_66, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_66, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_100 = x_66;
} else {
 lean_dec_ref(x_66);
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
}
}
lean_object* l___private_Lean_Elab_Do_3__extractBind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Do_3__extractBind(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_Code_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_Code_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_Do_Code_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_Alt_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Array_empty___closed__1;
x_3 = l_Lean_Elab_Term_Do_Code_inhabited___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_Alt_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_Do_Alt_inhabited___closed__1;
return x_1;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Do_4__varsToMessageData___spec__1(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_simp_macro_scopes(x_4);
x_7 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_List_map___main___at___private_Lean_Elab_Do_4__varsToMessageData___spec__1(x_5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_simp_macro_scopes(x_9);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_List_map___main___at___private_Lean_Elab_Do_4__varsToMessageData___spec__1(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l___private_Lean_Elab_Do_4__varsToMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Array_toList___rarg(x_1);
x_3 = l_List_map___main___at___private_Lean_Elab_Do_4__varsToMessageData___spec__1(x_2);
x_4 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_5 = l_Lean_MessageData_joinSep___main(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Do_4__varsToMessageData___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Do_4__varsToMessageData(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
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
lean_object* l_List_map___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__2(lean_object* x_1) {
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
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__2(x_5);
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
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("| ");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = l_Lean_MessageData_ofList___closed__3;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___closed__3;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_ctor_get(x_9, 2);
lean_inc(x_14);
x_15 = l_Array_toList___rarg(x_14);
lean_dec(x_14);
x_16 = l_List_map___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__2(x_15);
lean_inc(x_3);
x_17 = l_Lean_MessageData_joinSep___main(x_16, x_3);
lean_dec(x_16);
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_Match_Alt_toMessageData___closed__4;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_ctor_get(x_9, 3);
lean_inc(x_21);
lean_dec(x_9);
lean_inc(x_1);
x_22 = l_Lean_Elab_Term_Do_toMessageDataAux___main(x_1, x_21);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_5 = x_25;
x_6 = x_23;
goto _start;
}
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("let ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" := ... ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("break ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("continue ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("return ... ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("if ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" then ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__20;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("else ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__22;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__23;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__12;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__25;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__27;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("jmp ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__29;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__30;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l___private_Lean_Elab_Do_4__varsToMessageData(x_3);
lean_dec(x_3);
x_6 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__3;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__6;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_MessageData_ofList___closed__3;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Elab_Term_Do_toMessageDataAux___main(x_1, x_4);
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l___private_Lean_Elab_Do_4__varsToMessageData(x_14);
lean_dec(x_14);
x_17 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__6;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_MessageData_ofList___closed__3;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_Term_Do_toMessageDataAux___main(x_1, x_15);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
case 2:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 3);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_simp_macro_scopes(x_23);
x_28 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__3;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = x_24;
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__1(x_34, x_33);
x_36 = x_35;
x_37 = l___private_Lean_Elab_Do_4__varsToMessageData(x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
x_39 = l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___closed__2;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_1);
x_41 = l_Lean_Elab_Term_Do_toMessageDataAux___main(x_1, x_25);
x_42 = l_Lean_indentD(x_41);
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_MessageData_ofList___closed__3;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Elab_Term_Do_toMessageDataAux___main(x_1, x_26);
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
case 3:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
lean_dec(x_2);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_48);
x_51 = l_Lean_MessageData_ofList___closed__3;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Elab_Term_Do_toMessageDataAux___main(x_1, x_49);
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
case 4:
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_2);
x_55 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__9;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_1);
return x_56;
}
case 5:
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_2);
x_57 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__12;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_1);
return x_58;
}
case 6:
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_2);
x_59 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__15;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_1);
return x_60;
}
case 7:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_61 = lean_ctor_get(x_2, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_2, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_2, 5);
lean_inc(x_63);
lean_dec(x_2);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_61);
x_65 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__18;
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__21;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_inc(x_1);
x_69 = l_Lean_Elab_Term_Do_toMessageDataAux___main(x_1, x_62);
x_70 = l_Lean_indentD(x_69);
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_MessageData_ofList___closed__3;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__24;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_Elab_Term_Do_toMessageDataAux___main(x_1, x_63);
x_77 = l_Lean_indentD(x_76);
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
case 8:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_79 = lean_ctor_get(x_2, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 3);
lean_inc(x_80);
lean_dec(x_2);
x_81 = l_Array_toList___rarg(x_79);
lean_dec(x_79);
x_82 = l_List_map___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__2(x_81);
x_83 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_84 = l_Lean_MessageData_joinSep___main(x_82, x_83);
lean_dec(x_82);
x_85 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__26;
x_86 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__28;
x_88 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_Lean_MessageData_Inhabited___closed__1;
x_91 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3(x_1, x_80, x_83, x_80, x_89, x_90);
lean_dec(x_80);
x_92 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
default: 
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_1);
x_93 = lean_ctor_get(x_2, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_2, 2);
lean_inc(x_94);
lean_dec(x_2);
x_95 = lean_simp_macro_scopes(x_93);
x_96 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__31;
x_98 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_100 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Array_toList___rarg(x_94);
lean_dec(x_94);
x_102 = l_List_toString___at___private_Lean_Elab_Match_3__elabDiscrsWitMatchTypeAux___main___spec__1(x_101);
x_103 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_105, 0, x_100);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_Do_toMessageDataAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_Do_toMessageDataAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Do_5__nameSetToArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = l_Std_RBNode_fold___main___at_Lean_registerTagAttribute___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_List_map___main___at_Lean_Elab_Term_Do_CodeBlock_toMessageData___spec__1(lean_object* x_1) {
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
x_6 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___main___at_Lean_Elab_Term_Do_CodeBlock_toMessageData___spec__1(x_5);
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
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___main___at_Lean_Elab_Term_Do_CodeBlock_toMessageData___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_CodeBlock_toMessageData(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l___private_Lean_Elab_Do_5__nameSetToArray(x_2);
x_4 = l_Array_toList___rarg(x_3);
lean_dec(x_3);
x_5 = l_List_map___main___at_Lean_Elab_Term_Do_CodeBlock_toMessageData___spec__1(x_4);
x_6 = l_Lean_MessageData_ofList(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Elab_Term_Do_toMessageDataAux___main(x_6, x_7);
return x_8;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_hasExitPoint___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Elab_Term_Do_hasExitPoint___main(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_4);
return x_9;
}
}
}
}
uint8_t l_Lean_Elab_Term_Do_hasExitPoint___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
x_1 = x_2;
goto _start;
}
case 1:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 2);
x_1 = x_4;
goto _start;
}
case 2:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Elab_Term_Do_hasExitPoint___main(x_6);
if (x_8 == 0)
{
x_1 = x_7;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
case 3:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 1);
x_1 = x_11;
goto _start;
}
case 7:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_1, 4);
x_14 = lean_ctor_get(x_1, 5);
x_15 = l_Lean_Elab_Term_Do_hasExitPoint___main(x_13);
if (x_15 == 0)
{
x_1 = x_14;
goto _start;
}
else
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
}
case 8:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_1, 3);
x_19 = lean_array_get_size(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_hasExitPoint___main___spec__1(x_18, x_18, x_19, x_20);
lean_dec(x_19);
return x_21;
}
case 9:
{
uint8_t x_22; 
x_22 = 0;
return x_22;
}
default: 
{
uint8_t x_23; 
x_23 = 1;
return x_23;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_hasExitPoint___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_hasExitPoint___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_Do_hasExitPoint___main___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_Do_hasExitPoint___main(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Elab_Term_Do_hasExitPoint(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Elab_Term_Do_hasExitPoint___main(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_Do_hasExitPoint___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_Do_hasExitPoint(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_hasContinueBreak___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Elab_Term_Do_hasContinueBreak___main(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_4);
return x_9;
}
}
}
}
uint8_t l_Lean_Elab_Term_Do_hasContinueBreak___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_Lean_Elab_Term_Do_hasContinueBreak___main(x_2);
if (x_4 == 0)
{
x_1 = x_3;
goto _start;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
case 3:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
x_1 = x_7;
goto _start;
}
case 4:
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
case 5:
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
case 6:
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
case 7:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 4);
x_13 = lean_ctor_get(x_1, 5);
x_14 = l_Lean_Elab_Term_Do_hasContinueBreak___main(x_12);
if (x_14 == 0)
{
x_1 = x_13;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
case 8:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 3);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_hasContinueBreak___main___spec__1(x_17, x_17, x_18, x_19);
lean_dec(x_18);
return x_20;
}
case 9:
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
default: 
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_1, 2);
x_1 = x_22;
goto _start;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_hasContinueBreak___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_hasContinueBreak___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_Do_hasContinueBreak___main___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_Do_hasContinueBreak___main(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Elab_Term_Do_hasContinueBreak(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Elab_Term_Do_hasContinueBreak___main(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_Do_hasContinueBreak___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_Do_hasContinueBreak(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_mkIdentFrom(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = x_4;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_array_fget(x_4, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_fset(x_4, x_3, x_9);
x_11 = x_8;
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_11, 3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_1, x_2, x_13);
lean_ctor_set(x_11, 3, x_14);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
x_17 = x_11;
x_18 = lean_array_fset(x_10, x_3, x_17);
lean_dec(x_3);
x_3 = x_16;
x_4 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
x_22 = lean_ctor_get(x_11, 2);
x_23 = lean_ctor_get(x_11, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_24 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_1, x_2, x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
x_28 = x_25;
x_29 = lean_array_fset(x_10, x_3, x_28);
lean_dec(x_3);
x_3 = x_27;
x_4 = x_29;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_1, x_2, x_5);
lean_ctor_set(x_3, 2, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_10 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_1, x_2, x_9);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_10);
return x_11;
}
}
case 1:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 2);
x_14 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_1, x_2, x_13);
lean_ctor_set(x_3, 2, x_14);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_18 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_1, x_2, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
case 2:
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_3, 2);
x_22 = lean_ctor_get(x_3, 3);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_1, x_2, x_21);
x_24 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_1, x_2, x_22);
lean_ctor_set(x_3, 3, x_24);
lean_ctor_set(x_3, 2, x_23);
return x_3;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
x_27 = lean_ctor_get(x_3, 2);
x_28 = lean_ctor_get(x_3, 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_1, x_2, x_27);
x_30 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_1, x_2, x_28);
x_31 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_30);
return x_31;
}
}
case 3:
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_3, 1);
x_34 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_1, x_2, x_33);
lean_ctor_set(x_3, 1, x_34);
return x_3;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_3, 0);
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_3);
x_37 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_1, x_2, x_36);
x_38 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
case 6:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
lean_dec(x_3);
x_41 = x_2;
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main___spec__1(x_39, x_42, x_41);
x_44 = x_43;
x_45 = lean_array_push(x_44, x_40);
x_46 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_1);
lean_ctor_set(x_46, 2, x_45);
return x_46;
}
case 7:
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_3);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_3, 4);
x_49 = lean_ctor_get(x_3, 5);
lean_inc(x_2);
lean_inc(x_1);
x_50 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_1, x_2, x_48);
x_51 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_1, x_2, x_49);
lean_ctor_set(x_3, 5, x_51);
lean_ctor_set(x_3, 4, x_50);
return x_3;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_3, 0);
x_53 = lean_ctor_get(x_3, 1);
x_54 = lean_ctor_get(x_3, 2);
x_55 = lean_ctor_get(x_3, 3);
x_56 = lean_ctor_get(x_3, 4);
x_57 = lean_ctor_get(x_3, 5);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_58 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_1, x_2, x_56);
x_59 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_1, x_2, x_57);
x_60 = lean_alloc_ctor(7, 6, 0);
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_53);
lean_ctor_set(x_60, 2, x_54);
lean_ctor_set(x_60, 3, x_55);
lean_ctor_set(x_60, 4, x_58);
lean_ctor_set(x_60, 5, x_59);
return x_60;
}
}
case 8:
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_3);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_3, 3);
x_63 = x_62;
x_64 = lean_unsigned_to_nat(0u);
x_65 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main___spec__2(x_1, x_2, x_64, x_63);
x_66 = x_65;
lean_ctor_set(x_3, 3, x_66);
return x_3;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_3, 0);
x_68 = lean_ctor_get(x_3, 1);
x_69 = lean_ctor_get(x_3, 2);
x_70 = lean_ctor_get(x_3, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_3);
x_71 = x_70;
x_72 = lean_unsigned_to_nat(0u);
x_73 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main___spec__2(x_1, x_2, x_72, x_71);
x_74 = x_73;
x_75 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_68);
lean_ctor_set(x_75, 2, x_69);
lean_ctor_set(x_75, 3, x_74);
return x_75;
}
}
default: 
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_Do_convertReturnIntoJmpAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_Do_convertReturnIntoJmp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_Do_attachJP(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set(x_6, 3, x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_Do_attachJP___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_Do_attachJP(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_Do_attachJPs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_array_fget(x_2, x_9);
x_11 = l_Lean_Elab_Term_Do_attachJP(x_10, x_5);
lean_dec(x_10);
x_3 = x_9;
x_4 = lean_box(0);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_3);
return x_5;
}
}
}
lean_object* l_Lean_Elab_Term_Do_attachJPs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_Do_attachJPs___spec__1(x_1, x_1, x_3, lean_box(0), x_2);
return x_4;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_Do_attachJPs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_Do_attachJPs___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_Do_attachJPs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_Do_attachJPs(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_Do_mkFreshJP___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_CoreM_1__mkFreshNameImp(x_1, x_6, x_7, x_8);
return x_9;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_mkFreshJP___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("jp");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_mkFreshJP___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Do_mkFreshJP___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_mkFreshJP___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("y");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_mkFreshJP___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Do_mkFreshJP___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_Do_mkFreshJP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_22; 
x_22 = l_Array_isEmpty___rarg(x_1);
if (x_22 == 0)
{
x_10 = x_1;
x_11 = x_9;
goto block_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_23 = l_Lean_Elab_Term_Do_mkFreshJP___closed__4;
x_24 = l___private_Lean_CoreM_1__mkFreshNameImp(x_23, x_7, x_8, x_9);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = 0;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_mkOptionalNode___closed__2;
x_31 = lean_array_push(x_30, x_29);
x_10 = x_31;
x_11 = x_26;
goto block_21;
}
block_21:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Elab_Term_Do_mkFreshJP___closed__2;
x_13 = l___private_Lean_CoreM_1__mkFreshNameImp(x_12, x_7, x_8, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_2);
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
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_19, 2, x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
}
lean_object* l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_Do_mkFreshJP___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_Do_mkFreshJP___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_Do_mkFreshJP___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_Do_mkFreshJP(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_mkFreshJP_x27___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_1, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_8, x_1, x_15);
lean_dec(x_1);
x_1 = x_14;
x_2 = x_16;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Term_Do_mkFreshJP_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = x_1;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_mkFreshJP_x27___spec__1(x_11, x_10);
x_13 = x_12;
x_14 = l_Lean_Elab_Term_Do_mkFreshJP(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
lean_object* l_Lean_Elab_Term_Do_mkFreshJP_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_Do_mkFreshJP_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_Do_addFreshJP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = l_Lean_Elab_Term_Do_mkFreshJP(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_3, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
x_17 = lean_array_push(x_15, x_12);
x_18 = lean_st_ref_set(x_3, x_17, x_16);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
lean_object* l_Lean_Elab_Term_Do_addFreshJP___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_Do_addFreshJP(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_Do_addFreshJP_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = x_1;
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_mkFreshJP_x27___spec__1(x_12, x_11);
x_14 = x_13;
x_15 = l_Lean_Elab_Term_Do_addFreshJP(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
lean_object* l_Lean_Elab_Term_Do_addFreshJP_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_Do_addFreshJP_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_box(0);
x_9 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_7, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
x_4 = x_9;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Term_Do_insertVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_2, x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_Do_insertVars___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_Do_insertVars(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_RBNode_del___main___at_Lean_Elab_Term_Do_eraseVars___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = l_Lean_Name_quickLt(x_1, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
x_10 = l_Std_RBNode_appendTrees___main___rarg(x_4, x_7);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l_Std_RBNode_isBlack___rarg(x_7);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Std_RBNode_del___main___at_Lean_Elab_Term_Do_eraseVars___spec__2(x_1, x_7);
x_13 = 0;
lean_ctor_set(x_2, 3, x_12);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_2);
x_14 = l_Std_RBNode_del___main___at_Lean_Elab_Term_Do_eraseVars___spec__2(x_1, x_7);
x_15 = l_Std_RBNode_balRight___rarg(x_4, x_5, x_6, x_14);
return x_15;
}
}
}
else
{
uint8_t x_16; 
x_16 = l_Std_RBNode_isBlack___rarg(x_4);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Std_RBNode_del___main___at_Lean_Elab_Term_Do_eraseVars___spec__2(x_1, x_4);
x_18 = 0;
lean_ctor_set(x_2, 0, x_17);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_18);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_2);
x_19 = l_Std_RBNode_del___main___at_Lean_Elab_Term_Do_eraseVars___spec__2(x_1, x_4);
x_20 = l_Std_RBNode_balLeft___rarg(x_19, x_5, x_6, x_7);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_25 = l_Lean_Name_quickLt(x_1, x_22);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Name_quickLt(x_22, x_1);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_22);
x_27 = l_Std_RBNode_appendTrees___main___rarg(x_21, x_24);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = l_Std_RBNode_isBlack___rarg(x_24);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Std_RBNode_del___main___at_Lean_Elab_Term_Do_eraseVars___spec__2(x_1, x_24);
x_30 = 0;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_23);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Std_RBNode_del___main___at_Lean_Elab_Term_Do_eraseVars___spec__2(x_1, x_24);
x_33 = l_Std_RBNode_balRight___rarg(x_21, x_22, x_23, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = l_Std_RBNode_isBlack___rarg(x_21);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_35 = l_Std_RBNode_del___main___at_Lean_Elab_Term_Do_eraseVars___spec__2(x_1, x_21);
x_36 = 0;
x_37 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_22);
lean_ctor_set(x_37, 2, x_23);
lean_ctor_set(x_37, 3, x_24);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Std_RBNode_del___main___at_Lean_Elab_Term_Do_eraseVars___spec__2(x_1, x_21);
x_39 = l_Std_RBNode_balLeft___rarg(x_38, x_22, x_23, x_24);
return x_39;
}
}
}
}
}
}
lean_object* l_Std_RBNode_erase___at_Lean_Elab_Term_Do_eraseVars___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_RBNode_del___main___at_Lean_Elab_Term_Do_eraseVars___spec__2(x_1, x_2);
x_4 = l_Std_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_eraseVars___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
x_10 = l_Std_RBNode_erase___at_Lean_Elab_Term_Do_eraseVars___spec__1(x_7, x_4);
lean_dec(x_7);
x_3 = x_9;
x_4 = x_10;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Term_Do_eraseVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_eraseVars___spec__3(x_2, x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Std_RBNode_del___main___at_Lean_Elab_Term_Do_eraseVars___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_del___main___at_Lean_Elab_Term_Do_eraseVars___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_RBNode_erase___at_Lean_Elab_Term_Do_eraseVars___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_erase___at_Lean_Elab_Term_Do_eraseVars___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_eraseVars___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_eraseVars___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_Do_eraseVars___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_Do_eraseVars(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_Do_eraseOptVar(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_3, x_4);
return x_5;
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_mkJmp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_mkIdentFrom(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* _init_l_Lean_Elab_Term_Do_mkJmp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Unit.unit");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_mkJmp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_mkJmp___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_mkJmp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_Do_mkJmp___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_Do_mkJmp___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_mkJmp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_unitToExpr___lambda__1___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_mkJmp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Do_mkJmp___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_Do_mkJmp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___rarg(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = x_3;
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_mkJmp___spec__1(x_1, x_13, x_12);
x_15 = x_14;
x_16 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_3);
x_18 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_unitToExpr___lambda__1___closed__2;
x_25 = l_Lean_addMacroScope(x_23, x_24, x_19);
x_26 = l_Lean_SourceInfo_inhabited___closed__1;
x_27 = l_Lean_Elab_Term_Do_mkJmp___closed__3;
x_28 = l_Lean_Elab_Term_Do_mkJmp___closed__5;
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_28);
x_30 = l_Lean_mkOptionalNode___closed__2;
x_31 = lean_array_push(x_30, x_29);
x_32 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_2);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set(x_21, 0, x_32);
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
x_35 = l_Lean_unitToExpr___lambda__1___closed__2;
x_36 = l_Lean_addMacroScope(x_33, x_35, x_19);
x_37 = l_Lean_SourceInfo_inhabited___closed__1;
x_38 = l_Lean_Elab_Term_Do_mkJmp___closed__3;
x_39 = l_Lean_Elab_Term_Do_mkJmp___closed__5;
x_40 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_36);
lean_ctor_set(x_40, 3, x_39);
x_41 = l_Lean_mkOptionalNode___closed__2;
x_42 = lean_array_push(x_41, x_40);
x_43 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_2);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_34);
return x_44;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_mkJmp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_mkJmp___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_Do_mkJmp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_Do_mkJmp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_pullExitPointsAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_mkIdentFrom(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_Do_pullExitPointsAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_CoreM_1__mkFreshNameImp(x_1, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_pullExitPointsAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
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
lean_dec(x_2);
lean_dec(x_1);
x_14 = x_3;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_array_fget(x_3, x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_fset(x_3, x_2, x_17);
x_19 = x_16;
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_19, 2);
x_24 = lean_ctor_get(x_19, 3);
lean_inc(x_1);
x_25 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_eraseVars___spec__3(x_22, x_22, x_17, x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_26 = l_Lean_Elab_Term_Do_pullExitPointsAux___main(x_25, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_ctor_set(x_19, 3, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
x_31 = x_19;
x_32 = lean_array_fset(x_18, x_2, x_31);
lean_dec(x_2);
x_2 = x_30;
x_3 = x_32;
x_11 = x_28;
goto _start;
}
else
{
uint8_t x_34; 
lean_free_object(x_19);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_19, 0);
x_39 = lean_ctor_get(x_19, 1);
x_40 = lean_ctor_get(x_19, 2);
x_41 = lean_ctor_get(x_19, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_19);
lean_inc(x_1);
x_42 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_eraseVars___spec__3(x_39, x_39, x_17, x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_43 = l_Lean_Elab_Term_Do_pullExitPointsAux___main(x_42, x_41, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_39);
lean_ctor_set(x_46, 2, x_40);
lean_ctor_set(x_46, 3, x_44);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_2, x_47);
x_49 = x_46;
x_50 = lean_array_fset(x_18, x_2, x_49);
lean_dec(x_2);
x_2 = x_48;
x_3 = x_50;
x_11 = x_45;
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_43, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_54 = x_43;
} else {
 lean_dec_ref(x_43);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_pullExitPointsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_eraseVars___spec__3(x_12, x_12, x_15, x_1);
x_17 = l_Lean_Elab_Term_Do_pullExitPointsAux___main(x_16, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_2, 2, x_19);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_2, 2, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_12);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
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
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_2, 2);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_eraseVars___spec__3(x_27, x_27, x_30, x_1);
x_32 = l_Lean_Elab_Term_Do_pullExitPointsAux___main(x_31, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_28);
lean_ctor_set(x_36, 2, x_33);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_28);
lean_dec(x_27);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
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
case 1:
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_2);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
x_45 = lean_ctor_get(x_2, 2);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_43, x_43, x_46, x_1);
x_48 = l_Lean_Elab_Term_Do_pullExitPointsAux___main(x_47, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_ctor_set(x_2, 2, x_50);
lean_ctor_set(x_48, 0, x_2);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_48);
lean_ctor_set(x_2, 2, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_2);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_free_object(x_2);
lean_dec(x_44);
lean_dec(x_43);
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_48, 0);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_48);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_2, 0);
x_59 = lean_ctor_get(x_2, 1);
x_60 = lean_ctor_get(x_2, 2);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_2);
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_58, x_58, x_61, x_1);
x_63 = l_Lean_Elab_Term_Do_pullExitPointsAux___main(x_62, x_60, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_58);
lean_ctor_set(x_67, 1, x_59);
lean_ctor_set(x_67, 2, x_64);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_59);
lean_dec(x_58);
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
case 2:
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_2);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_2, 0);
x_75 = lean_ctor_get(x_2, 1);
x_76 = lean_ctor_get(x_2, 2);
x_77 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_78 = l_Lean_Elab_Term_Do_pullExitPointsAux___main(x_1, x_76, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Elab_Term_Do_pullExitPointsAux___main(x_1, x_77, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_80);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_81, 0);
lean_ctor_set(x_2, 3, x_83);
lean_ctor_set(x_2, 2, x_79);
lean_ctor_set(x_81, 0, x_2);
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
lean_ctor_set(x_2, 3, x_84);
lean_ctor_set(x_2, 2, x_79);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_2);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
else
{
uint8_t x_87; 
lean_dec(x_79);
lean_free_object(x_2);
lean_dec(x_75);
lean_dec(x_74);
x_87 = !lean_is_exclusive(x_81);
if (x_87 == 0)
{
return x_81;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_81, 0);
x_89 = lean_ctor_get(x_81, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_81);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_free_object(x_2);
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_78);
if (x_91 == 0)
{
return x_78;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_78, 0);
x_93 = lean_ctor_get(x_78, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_78);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_2, 0);
x_96 = lean_ctor_get(x_2, 1);
x_97 = lean_ctor_get(x_2, 2);
x_98 = lean_ctor_get(x_2, 3);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_99 = l_Lean_Elab_Term_Do_pullExitPointsAux___main(x_1, x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_Elab_Term_Do_pullExitPointsAux___main(x_1, x_98, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
x_106 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_106, 0, x_95);
lean_ctor_set(x_106, 1, x_96);
lean_ctor_set(x_106, 2, x_100);
lean_ctor_set(x_106, 3, x_103);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_100);
lean_dec(x_96);
lean_dec(x_95);
x_108 = lean_ctor_get(x_102, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_102, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_110 = x_102;
} else {
 lean_dec_ref(x_102);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_112 = lean_ctor_get(x_99, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_99, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_114 = x_99;
} else {
 lean_dec_ref(x_99);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
case 3:
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_2);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_2, 0);
x_118 = lean_ctor_get(x_2, 1);
x_119 = l_Lean_Elab_Term_Do_pullExitPointsAux___main(x_1, x_118, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_119, 0);
lean_ctor_set(x_2, 1, x_121);
lean_ctor_set(x_119, 0, x_2);
return x_119;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_119, 0);
x_123 = lean_ctor_get(x_119, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_119);
lean_ctor_set(x_2, 1, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_2);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
else
{
uint8_t x_125; 
lean_free_object(x_2);
lean_dec(x_117);
x_125 = !lean_is_exclusive(x_119);
if (x_125 == 0)
{
return x_119;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_119, 0);
x_127 = lean_ctor_get(x_119, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_119);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_2, 0);
x_130 = lean_ctor_get(x_2, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_2);
x_131 = l_Lean_Elab_Term_Do_pullExitPointsAux___main(x_1, x_130, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
x_135 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_135, 0, x_129);
lean_ctor_set(x_135, 1, x_132);
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_133);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_129);
x_137 = lean_ctor_get(x_131, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_131, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_139 = x_131;
} else {
 lean_dec_ref(x_131);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
case 6:
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_2);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_142 = lean_ctor_get(x_2, 0);
x_143 = lean_ctor_get(x_2, 1);
x_144 = l___private_Lean_Elab_Do_5__nameSetToArray(x_1);
x_145 = x_144;
x_146 = lean_unsigned_to_nat(0u);
lean_inc(x_145);
x_147 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_pullExitPointsAux___main___spec__1(x_142, x_146, x_145);
x_148 = x_147;
x_149 = lean_array_push(x_148, x_143);
x_150 = l_Lean_Elab_Term_Do_mkFreshJP___closed__4;
x_151 = l___private_Lean_CoreM_1__mkFreshNameImp(x_150, x_8, x_9, x_10);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_mkFreshJP_x27___spec__1(x_146, x_145);
x_155 = x_154;
x_156 = 0;
x_157 = lean_box(x_156);
lean_inc(x_152);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_152);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_array_push(x_155, x_158);
x_160 = l_Lean_mkIdentFrom(x_142, x_152);
lean_inc(x_142);
lean_ctor_set(x_2, 1, x_160);
x_161 = l_Lean_Elab_Term_Do_addFreshJP(x_159, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_153);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_161, 0);
x_164 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_164, 0, x_142);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_164, 2, x_149);
lean_ctor_set(x_161, 0, x_164);
return x_161;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_161, 0);
x_166 = lean_ctor_get(x_161, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_161);
x_167 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_167, 0, x_142);
lean_ctor_set(x_167, 1, x_165);
lean_ctor_set(x_167, 2, x_149);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_169 = lean_ctor_get(x_2, 0);
x_170 = lean_ctor_get(x_2, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_2);
x_171 = l___private_Lean_Elab_Do_5__nameSetToArray(x_1);
x_172 = x_171;
x_173 = lean_unsigned_to_nat(0u);
lean_inc(x_172);
x_174 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_pullExitPointsAux___main___spec__1(x_169, x_173, x_172);
x_175 = x_174;
x_176 = lean_array_push(x_175, x_170);
x_177 = l_Lean_Elab_Term_Do_mkFreshJP___closed__4;
x_178 = l___private_Lean_CoreM_1__mkFreshNameImp(x_177, x_8, x_9, x_10);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_mkFreshJP_x27___spec__1(x_173, x_172);
x_182 = x_181;
x_183 = 0;
x_184 = lean_box(x_183);
lean_inc(x_179);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_179);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_array_push(x_182, x_185);
x_187 = l_Lean_mkIdentFrom(x_169, x_179);
lean_inc(x_169);
x_188 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_188, 0, x_169);
lean_ctor_set(x_188, 1, x_187);
x_189 = l_Lean_Elab_Term_Do_addFreshJP(x_186, x_188, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_180);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_192 = x_189;
} else {
 lean_dec_ref(x_189);
 x_192 = lean_box(0);
}
x_193 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_193, 0, x_169);
lean_ctor_set(x_193, 1, x_190);
lean_ctor_set(x_193, 2, x_176);
if (lean_is_scalar(x_192)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_192;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_191);
return x_194;
}
}
case 7:
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_2);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_196 = lean_ctor_get(x_2, 0);
x_197 = lean_ctor_get(x_2, 1);
x_198 = lean_ctor_get(x_2, 2);
x_199 = lean_ctor_get(x_2, 3);
x_200 = lean_ctor_get(x_2, 4);
x_201 = lean_ctor_get(x_2, 5);
lean_inc(x_197);
x_202 = l_Lean_Elab_Term_Do_eraseOptVar(x_1, x_197);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_202);
x_203 = l_Lean_Elab_Term_Do_pullExitPointsAux___main(x_202, x_200, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = l_Lean_Elab_Term_Do_pullExitPointsAux___main(x_202, x_201, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_205);
if (lean_obj_tag(x_206) == 0)
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_206);
if (x_207 == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_206, 0);
lean_ctor_set(x_2, 5, x_208);
lean_ctor_set(x_2, 4, x_204);
lean_ctor_set(x_206, 0, x_2);
return x_206;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_206, 0);
x_210 = lean_ctor_get(x_206, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_206);
lean_ctor_set(x_2, 5, x_209);
lean_ctor_set(x_2, 4, x_204);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_2);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
else
{
uint8_t x_212; 
lean_dec(x_204);
lean_free_object(x_2);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
x_212 = !lean_is_exclusive(x_206);
if (x_212 == 0)
{
return x_206;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_206, 0);
x_214 = lean_ctor_get(x_206, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_206);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
else
{
uint8_t x_216; 
lean_dec(x_202);
lean_free_object(x_2);
lean_dec(x_201);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_216 = !lean_is_exclusive(x_203);
if (x_216 == 0)
{
return x_203;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_203, 0);
x_218 = lean_ctor_get(x_203, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_203);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_220 = lean_ctor_get(x_2, 0);
x_221 = lean_ctor_get(x_2, 1);
x_222 = lean_ctor_get(x_2, 2);
x_223 = lean_ctor_get(x_2, 3);
x_224 = lean_ctor_get(x_2, 4);
x_225 = lean_ctor_get(x_2, 5);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_2);
lean_inc(x_221);
x_226 = l_Lean_Elab_Term_Do_eraseOptVar(x_1, x_221);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_226);
x_227 = l_Lean_Elab_Term_Do_pullExitPointsAux___main(x_226, x_224, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = l_Lean_Elab_Term_Do_pullExitPointsAux___main(x_226, x_225, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_229);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_233 = x_230;
} else {
 lean_dec_ref(x_230);
 x_233 = lean_box(0);
}
x_234 = lean_alloc_ctor(7, 6, 0);
lean_ctor_set(x_234, 0, x_220);
lean_ctor_set(x_234, 1, x_221);
lean_ctor_set(x_234, 2, x_222);
lean_ctor_set(x_234, 3, x_223);
lean_ctor_set(x_234, 4, x_228);
lean_ctor_set(x_234, 5, x_231);
if (lean_is_scalar(x_233)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_233;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_232);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_228);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
x_236 = lean_ctor_get(x_230, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_230, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_238 = x_230;
} else {
 lean_dec_ref(x_230);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_240 = lean_ctor_get(x_227, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_227, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_242 = x_227;
} else {
 lean_dec_ref(x_227);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
}
}
case 8:
{
uint8_t x_244; 
x_244 = !lean_is_exclusive(x_2);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_245 = lean_ctor_get(x_2, 0);
x_246 = lean_ctor_get(x_2, 1);
x_247 = lean_ctor_get(x_2, 2);
x_248 = lean_ctor_get(x_2, 3);
x_249 = x_248;
x_250 = lean_unsigned_to_nat(0u);
x_251 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_Do_pullExitPointsAux___main___spec__3), 11, 3);
lean_closure_set(x_251, 0, x_1);
lean_closure_set(x_251, 1, x_250);
lean_closure_set(x_251, 2, x_249);
x_252 = x_251;
x_253 = lean_apply_8(x_252, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_253) == 0)
{
uint8_t x_254; 
x_254 = !lean_is_exclusive(x_253);
if (x_254 == 0)
{
lean_object* x_255; 
x_255 = lean_ctor_get(x_253, 0);
lean_ctor_set(x_2, 3, x_255);
lean_ctor_set(x_253, 0, x_2);
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
lean_ctor_set(x_2, 3, x_256);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_2);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
else
{
uint8_t x_259; 
lean_free_object(x_2);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
x_259 = !lean_is_exclusive(x_253);
if (x_259 == 0)
{
return x_253;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_253, 0);
x_261 = lean_ctor_get(x_253, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_253);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_263 = lean_ctor_get(x_2, 0);
x_264 = lean_ctor_get(x_2, 1);
x_265 = lean_ctor_get(x_2, 2);
x_266 = lean_ctor_get(x_2, 3);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_2);
x_267 = x_266;
x_268 = lean_unsigned_to_nat(0u);
x_269 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_Do_pullExitPointsAux___main___spec__3), 11, 3);
lean_closure_set(x_269, 0, x_1);
lean_closure_set(x_269, 1, x_268);
lean_closure_set(x_269, 2, x_267);
x_270 = x_269;
x_271 = lean_apply_8(x_270, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_274 = x_271;
} else {
 lean_dec_ref(x_271);
 x_274 = lean_box(0);
}
x_275 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_275, 0, x_263);
lean_ctor_set(x_275, 1, x_264);
lean_ctor_set(x_275, 2, x_265);
lean_ctor_set(x_275, 3, x_272);
if (lean_is_scalar(x_274)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_274;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_273);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_263);
x_277 = lean_ctor_get(x_271, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_271, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_279 = x_271;
} else {
 lean_dec_ref(x_271);
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
case 9:
{
lean_object* x_281; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_2);
lean_ctor_set(x_281, 1, x_10);
return x_281;
}
default: 
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_282 = lean_ctor_get(x_2, 0);
lean_inc(x_282);
x_283 = l___private_Lean_Elab_Do_5__nameSetToArray(x_1);
lean_inc(x_283);
x_284 = l_Lean_Elab_Term_Do_addFreshJP_x27(x_283, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_287 = l_Lean_Elab_Term_Do_mkJmp(x_282, x_285, x_283, x_4, x_5, x_6, x_7, x_8, x_9, x_286);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_287;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_pullExitPointsAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_pullExitPointsAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_Do_pullExitPointsAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Core_mkFreshUserName___at_Lean_Elab_Term_Do_pullExitPointsAux___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_Do_pullExitPointsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_Do_pullExitPointsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_Do_pullExitPoints(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Elab_Term_Do_hasExitPoint___main(x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Array_empty___closed__1;
x_12 = lean_st_mk_ref(x_11, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_NameSet_empty;
lean_inc(x_13);
x_16 = l_Lean_Elab_Term_Do_pullExitPointsAux___main(x_15, x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_13, x_18);
lean_dec(x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_Elab_Term_Do_attachJPs(x_21, x_17);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = l_Lean_Elab_Term_Do_attachJPs(x_23, x_17);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
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
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_NameSet_contains(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_NameSet_contains(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__2(x_1, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_5 = x_14;
goto _start;
}
else
{
lean_dec(x_5);
return x_12;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = x_3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_array_fget(x_3, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fset(x_3, x_2, x_16);
x_18 = x_15;
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_18, 2);
x_23 = lean_ctor_get(x_18, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_24 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_ctor_set(x_18, 3, x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_2, x_27);
x_29 = x_18;
x_30 = lean_array_fset(x_17, x_2, x_29);
lean_dec(x_2);
x_2 = x_28;
x_3 = x_30;
x_10 = x_26;
goto _start;
}
else
{
uint8_t x_32; 
lean_free_object(x_18);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
x_38 = lean_ctor_get(x_18, 2);
x_39 = lean_ctor_get(x_18, 3);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_40 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_37);
lean_ctor_set(x_43, 2, x_38);
lean_ctor_set(x_43, 3, x_41);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_2, x_44);
x_46 = x_43;
x_47 = lean_array_fset(x_17, x_2, x_46);
lean_dec(x_2);
x_2 = x_45;
x_3 = x_47;
x_10 = x_42;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
}
lean_object* l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
x_13 = lean_array_get_size(x_10);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__1(x_1, x_10, x_10, x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_2, 2);
lean_dec(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 0);
lean_dec(x_19);
x_20 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_2, 2, x_22);
lean_ctor_set(x_20, 0, x_2);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_2, 2, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_2);
lean_dec(x_11);
lean_dec(x_10);
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
lean_object* x_30; 
lean_dec(x_2);
x_30 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_31);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
lean_dec(x_10);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_40 = l_Lean_Elab_Term_Do_pullExitPoints(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_40;
}
}
case 1:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_2);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
x_44 = lean_ctor_get(x_2, 2);
x_45 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_ctor_set(x_2, 2, x_47);
lean_ctor_set(x_45, 0, x_2);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_45, 0);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_45);
lean_ctor_set(x_2, 2, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_free_object(x_2);
lean_dec(x_43);
lean_dec(x_42);
x_51 = !lean_is_exclusive(x_45);
if (x_51 == 0)
{
return x_45;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_45, 0);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_45);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_2, 0);
x_56 = lean_ctor_get(x_2, 1);
x_57 = lean_ctor_get(x_2, 2);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_2);
x_58 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_56);
lean_ctor_set(x_62, 2, x_59);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_56);
lean_dec(x_55);
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_58, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_66 = x_58;
} else {
 lean_dec_ref(x_58);
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
case 2:
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_2);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_2, 0);
x_70 = lean_ctor_get(x_2, 1);
x_71 = lean_ctor_get(x_2, 2);
x_72 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_73 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_71, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_75);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_ctor_set(x_2, 3, x_78);
lean_ctor_set(x_2, 2, x_74);
lean_ctor_set(x_76, 0, x_2);
return x_76;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_76, 0);
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_76);
lean_ctor_set(x_2, 3, x_79);
lean_ctor_set(x_2, 2, x_74);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_2);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_74);
lean_free_object(x_2);
lean_dec(x_70);
lean_dec(x_69);
x_82 = !lean_is_exclusive(x_76);
if (x_82 == 0)
{
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_76, 0);
x_84 = lean_ctor_get(x_76, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_76);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_free_object(x_2);
lean_dec(x_72);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_73);
if (x_86 == 0)
{
return x_73;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_73, 0);
x_88 = lean_ctor_get(x_73, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_73);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_2, 0);
x_91 = lean_ctor_get(x_2, 1);
x_92 = lean_ctor_get(x_2, 2);
x_93 = lean_ctor_get(x_2, 3);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_94 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_92, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_93, x_3, x_4, x_5, x_6, x_7, x_8, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
x_101 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_101, 0, x_90);
lean_ctor_set(x_101, 1, x_91);
lean_ctor_set(x_101, 2, x_95);
lean_ctor_set(x_101, 3, x_98);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_95);
lean_dec(x_91);
lean_dec(x_90);
x_103 = lean_ctor_get(x_97, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_97, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_105 = x_97;
} else {
 lean_dec_ref(x_97);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_107 = lean_ctor_get(x_94, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_94, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_109 = x_94;
} else {
 lean_dec_ref(x_94);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
case 3:
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_2);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_2, 0);
x_113 = lean_ctor_get(x_2, 1);
x_114 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_113, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_114, 0);
lean_ctor_set(x_2, 1, x_116);
lean_ctor_set(x_114, 0, x_2);
return x_114;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_114, 0);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_114);
lean_ctor_set(x_2, 1, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_2);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
else
{
uint8_t x_120; 
lean_free_object(x_2);
lean_dec(x_112);
x_120 = !lean_is_exclusive(x_114);
if (x_120 == 0)
{
return x_114;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_114, 0);
x_122 = lean_ctor_get(x_114, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_114);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_2, 0);
x_125 = lean_ctor_get(x_2, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_2);
x_126 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_125, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
x_130 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_130, 0, x_124);
lean_ctor_set(x_130, 1, x_127);
if (lean_is_scalar(x_129)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_129;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_128);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_124);
x_132 = lean_ctor_get(x_126, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_126, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_134 = x_126;
} else {
 lean_dec_ref(x_126);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
}
case 7:
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_2, 1);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_2);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_138 = lean_ctor_get(x_2, 0);
x_139 = lean_ctor_get(x_2, 2);
x_140 = lean_ctor_get(x_2, 3);
x_141 = lean_ctor_get(x_2, 4);
x_142 = lean_ctor_get(x_2, 5);
x_143 = lean_ctor_get(x_2, 1);
lean_dec(x_143);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_144 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_141, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_142, x_3, x_4, x_5, x_6, x_7, x_8, x_146);
if (lean_obj_tag(x_147) == 0)
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_147, 0);
lean_ctor_set(x_2, 5, x_149);
lean_ctor_set(x_2, 4, x_145);
lean_ctor_set(x_147, 0, x_2);
return x_147;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_147, 0);
x_151 = lean_ctor_get(x_147, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_147);
lean_ctor_set(x_2, 5, x_150);
lean_ctor_set(x_2, 4, x_145);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_2);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
else
{
uint8_t x_153; 
lean_dec(x_145);
lean_free_object(x_2);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_153 = !lean_is_exclusive(x_147);
if (x_153 == 0)
{
return x_147;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_147, 0);
x_155 = lean_ctor_get(x_147, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_147);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_free_object(x_2);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_144);
if (x_157 == 0)
{
return x_144;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_144, 0);
x_159 = lean_ctor_get(x_144, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_144);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_161 = lean_ctor_get(x_2, 0);
x_162 = lean_ctor_get(x_2, 2);
x_163 = lean_ctor_get(x_2, 3);
x_164 = lean_ctor_get(x_2, 4);
x_165 = lean_ctor_get(x_2, 5);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_166 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_164, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_165, x_3, x_4, x_5, x_6, x_7, x_8, x_168);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_172 = x_169;
} else {
 lean_dec_ref(x_169);
 x_172 = lean_box(0);
}
x_173 = lean_alloc_ctor(7, 6, 0);
lean_ctor_set(x_173, 0, x_161);
lean_ctor_set(x_173, 1, x_136);
lean_ctor_set(x_173, 2, x_162);
lean_ctor_set(x_173, 3, x_163);
lean_ctor_set(x_173, 4, x_167);
lean_ctor_set(x_173, 5, x_170);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_171);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_167);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
x_175 = lean_ctor_get(x_169, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_169, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_177 = x_169;
} else {
 lean_dec_ref(x_169);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_165);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_179 = lean_ctor_get(x_166, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_166, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_181 = x_166;
} else {
 lean_dec_ref(x_166);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_183 = lean_ctor_get(x_2, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_2, 2);
lean_inc(x_184);
x_185 = lean_ctor_get(x_2, 3);
lean_inc(x_185);
x_186 = lean_ctor_get(x_2, 4);
lean_inc(x_186);
x_187 = lean_ctor_get(x_2, 5);
lean_inc(x_187);
x_188 = lean_ctor_get(x_136, 0);
lean_inc(x_188);
x_189 = l_Lean_NameSet_contains(x_1, x_188);
lean_dec(x_188);
if (x_189 == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_2);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_191 = lean_ctor_get(x_2, 5);
lean_dec(x_191);
x_192 = lean_ctor_get(x_2, 4);
lean_dec(x_192);
x_193 = lean_ctor_get(x_2, 3);
lean_dec(x_193);
x_194 = lean_ctor_get(x_2, 2);
lean_dec(x_194);
x_195 = lean_ctor_get(x_2, 1);
lean_dec(x_195);
x_196 = lean_ctor_get(x_2, 0);
lean_dec(x_196);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_197 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_186, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_187, x_3, x_4, x_5, x_6, x_7, x_8, x_199);
if (lean_obj_tag(x_200) == 0)
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_200);
if (x_201 == 0)
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_200, 0);
lean_ctor_set(x_2, 5, x_202);
lean_ctor_set(x_2, 4, x_198);
lean_ctor_set(x_200, 0, x_2);
return x_200;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_200, 0);
x_204 = lean_ctor_get(x_200, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_200);
lean_ctor_set(x_2, 5, x_203);
lean_ctor_set(x_2, 4, x_198);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_2);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
else
{
uint8_t x_206; 
lean_dec(x_198);
lean_free_object(x_2);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_136);
x_206 = !lean_is_exclusive(x_200);
if (x_206 == 0)
{
return x_200;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_200, 0);
x_208 = lean_ctor_get(x_200, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_200);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
else
{
uint8_t x_210; 
lean_free_object(x_2);
lean_dec(x_187);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_136);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_210 = !lean_is_exclusive(x_197);
if (x_210 == 0)
{
return x_197;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_197, 0);
x_212 = lean_ctor_get(x_197, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_197);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
else
{
lean_object* x_214; 
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_214 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_186, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_187, x_3, x_4, x_5, x_6, x_7, x_8, x_216);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_220 = x_217;
} else {
 lean_dec_ref(x_217);
 x_220 = lean_box(0);
}
x_221 = lean_alloc_ctor(7, 6, 0);
lean_ctor_set(x_221, 0, x_183);
lean_ctor_set(x_221, 1, x_136);
lean_ctor_set(x_221, 2, x_184);
lean_ctor_set(x_221, 3, x_185);
lean_ctor_set(x_221, 4, x_215);
lean_ctor_set(x_221, 5, x_218);
if (lean_is_scalar(x_220)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_220;
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_219);
return x_222;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_215);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_136);
x_223 = lean_ctor_get(x_217, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_217, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_225 = x_217;
} else {
 lean_dec_ref(x_217);
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
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_187);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_136);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_227 = lean_ctor_get(x_214, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_214, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_229 = x_214;
} else {
 lean_dec_ref(x_214);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
}
else
{
lean_object* x_231; 
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_136);
lean_dec(x_1);
x_231 = l_Lean_Elab_Term_Do_pullExitPoints(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_231;
}
}
}
case 8:
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_232 = lean_ctor_get(x_2, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_2, 1);
lean_inc(x_233);
x_234 = lean_ctor_get(x_2, 2);
lean_inc(x_234);
x_235 = lean_ctor_get(x_2, 3);
lean_inc(x_235);
x_236 = lean_array_get_size(x_235);
x_237 = lean_unsigned_to_nat(0u);
x_238 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__3(x_1, x_235, x_235, x_236, x_237);
lean_dec(x_236);
if (x_238 == 0)
{
uint8_t x_239; 
x_239 = !lean_is_exclusive(x_2);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_240 = lean_ctor_get(x_2, 3);
lean_dec(x_240);
x_241 = lean_ctor_get(x_2, 2);
lean_dec(x_241);
x_242 = lean_ctor_get(x_2, 1);
lean_dec(x_242);
x_243 = lean_ctor_get(x_2, 0);
lean_dec(x_243);
x_244 = x_235;
x_245 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__4), 10, 3);
lean_closure_set(x_245, 0, x_1);
lean_closure_set(x_245, 1, x_237);
lean_closure_set(x_245, 2, x_244);
x_246 = x_245;
x_247 = lean_apply_7(x_246, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_247) == 0)
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_247);
if (x_248 == 0)
{
lean_object* x_249; 
x_249 = lean_ctor_get(x_247, 0);
lean_ctor_set(x_2, 3, x_249);
lean_ctor_set(x_247, 0, x_2);
return x_247;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_247, 0);
x_251 = lean_ctor_get(x_247, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_247);
lean_ctor_set(x_2, 3, x_250);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_2);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
else
{
uint8_t x_253; 
lean_free_object(x_2);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
x_253 = !lean_is_exclusive(x_247);
if (x_253 == 0)
{
return x_247;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_247, 0);
x_255 = lean_ctor_get(x_247, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_247);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_2);
x_257 = x_235;
x_258 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__4), 10, 3);
lean_closure_set(x_258, 0, x_1);
lean_closure_set(x_258, 1, x_237);
lean_closure_set(x_258, 2, x_257);
x_259 = x_258;
x_260 = lean_apply_7(x_259, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_263 = x_260;
} else {
 lean_dec_ref(x_260);
 x_263 = lean_box(0);
}
x_264 = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(x_264, 0, x_232);
lean_ctor_set(x_264, 1, x_233);
lean_ctor_set(x_264, 2, x_234);
lean_ctor_set(x_264, 3, x_261);
if (lean_is_scalar(x_263)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_263;
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_262);
return x_265;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
x_266 = lean_ctor_get(x_260, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_260, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_268 = x_260;
} else {
 lean_dec_ref(x_260);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
}
}
else
{
lean_object* x_270; 
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_1);
x_270 = l_Lean_Elab_Term_Do_pullExitPoints(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_270;
}
}
default: 
{
lean_object* x_271; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_2);
lean_ctor_set(x_271, 1, x_9);
return x_271;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_extendUpdatedVarsAux___main___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_Do_extendUpdatedVarsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
uint8_t l_Std_RBNode_any___main___at_Lean_Elab_Term_Do_extendUpdatedVars___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_Lean_NameSet_contains(x_7, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = l_Std_RBNode_any___main___at_Lean_Elab_Term_Do_extendUpdatedVars___spec__1(x_1, x_4);
if (x_10 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_extendUpdatedVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Std_RBNode_any___main___at_Lean_Elab_Term_Do_extendUpdatedVars___spec__1(x_1, x_2);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
lean_ctor_set(x_1, 1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_dec(x_19);
lean_inc(x_2);
x_20 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_2, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_22);
lean_ctor_set(x_20, 0, x_1);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_1);
lean_dec(x_2);
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
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
lean_inc(x_2);
x_31 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_2, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_2);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_2);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_39 = x_31;
} else {
 lean_dec_ref(x_31);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
}
lean_object* l_Std_RBNode_any___main___at_Lean_Elab_Term_Do_extendUpdatedVars___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_RBNode_any___main___at_Lean_Elab_Term_Do_extendUpdatedVars___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Std_RBNode_fold___main___at___private_Lean_Elab_Do_6__union___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Std_RBNode_fold___main___at___private_Lean_Elab_Do_6__union___spec__1(x_1, x_3);
x_7 = lean_box(0);
x_8 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_6, x_4, x_7);
x_1 = x_8;
x_2 = x_5;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_Do_6__union(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_fold___main___at___private_Lean_Elab_Do_6__union___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_Do_homogenize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = l_Std_RBNode_fold___main___at___private_Lean_Elab_Do_6__union___spec__1(x_11, x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_12);
x_13 = l_Lean_Elab_Term_Do_extendUpdatedVars(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_Do_extendUpdatedVars(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
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
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_14);
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
else
{
uint8_t x_28; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_mkVarDeclCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_eraseVars___spec__3(x_1, x_1, x_7, x_6);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_mkReassignCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_NameSet_contains(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
x_10 = 1;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_mkReassignCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
x_13 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_1, x_1, x_12, x_11);
x_14 = lean_array_get_size(x_1);
x_15 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_mkReassignCore___spec__1(x_1, x_11, x_1, x_14, x_12);
lean_dec(x_14);
lean_dec(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
lean_inc(x_13);
x_21 = l_Lean_Elab_Term_Do_extendUpdatedVarsAux___main(x_13, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_13);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_13);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_mkReassignCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_Do_mkReassignCore___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_Do_mkAction(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
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
x_8 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
lean_object* l_Lean_Elab_Term_Do_mkReturn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = l_Lean_NameSet_empty;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_Do_mkBreak(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = l_Lean_NameSet_empty;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_Do_mkContinue(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = l_Lean_NameSet_empty;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_Do_mkIte(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = l_Lean_Syntax_isNone(x_2);
x_14 = l_Lean_Elab_Term_Do_homogenize(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (x_13 == 0)
{
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
x_19 = l_Lean_Syntax_getId(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(7, 6, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_2);
lean_ctor_set(x_26, 3, x_3);
lean_ctor_set(x_26, 4, x_24);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set(x_21, 0, x_26);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_alloc_ctor(7, 6, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_20);
lean_ctor_set(x_30, 2, x_2);
lean_ctor_set(x_30, 3, x_3);
lean_ctor_set(x_30, 4, x_27);
lean_ctor_set(x_30, 5, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_14, 0, x_31);
return x_14;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Syntax_getArg(x_2, x_34);
x_36 = l_Lean_Syntax_getId(x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_dec(x_32);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_42 = x_38;
} else {
 lean_dec_ref(x_38);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_alloc_ctor(7, 6, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_37);
lean_ctor_set(x_44, 2, x_2);
lean_ctor_set(x_44, 3, x_3);
lean_ctor_set(x_44, 4, x_40);
lean_ctor_set(x_44, 5, x_43);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_33);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_14);
if (x_47 == 0)
{
return x_14;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_14, 0);
x_49 = lean_ctor_get(x_14, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_14);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_14);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_14, 0);
x_53 = lean_box(0);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_54, 0);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(7, 6, 0);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_53);
lean_ctor_set(x_59, 2, x_2);
lean_ctor_set(x_59, 3, x_3);
lean_ctor_set(x_59, 4, x_57);
lean_ctor_set(x_59, 5, x_58);
lean_ctor_set(x_54, 0, x_59);
lean_ctor_set(x_14, 0, x_54);
return x_14;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_54, 0);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_54);
x_62 = lean_ctor_get(x_55, 0);
lean_inc(x_62);
lean_dec(x_55);
x_63 = lean_alloc_ctor(7, 6, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_53);
lean_ctor_set(x_63, 2, x_2);
lean_ctor_set(x_63, 3, x_3);
lean_ctor_set(x_63, 4, x_60);
lean_ctor_set(x_63, 5, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_14, 0, x_64);
return x_14;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_65 = lean_ctor_get(x_14, 0);
x_66 = lean_ctor_get(x_14, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_14);
x_67 = lean_box(0);
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_72 = x_68;
} else {
 lean_dec_ref(x_68);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
lean_dec(x_69);
x_74 = lean_alloc_ctor(7, 6, 0);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_67);
lean_ctor_set(x_74, 2, x_2);
lean_ctor_set(x_74, 3, x_3);
lean_ctor_set(x_74, 4, x_70);
lean_ctor_set(x_74, 5, x_73);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_72;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_66);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_14);
if (x_77 == 0)
{
return x_14;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_14, 0);
x_79 = lean_ctor_get(x_14, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_14);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_Do_mkUnless___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PUnit.unit");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_mkUnless___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_mkUnless___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_mkUnless___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_Do_mkUnless___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_Do_mkUnless___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_mkUnless___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PUnit");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_mkUnless___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Do_mkUnless___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_mkUnless___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Do_mkUnless___closed__5;
x_2 = l_Lean_unitToExpr___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_mkUnless___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Do_mkUnless___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_mkUnless___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Do_mkUnless___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_Do_mkUnless(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Term_Do_mkUnless___closed__6;
x_19 = l_Lean_addMacroScope(x_16, x_18, x_12);
x_20 = l_Lean_SourceInfo_inhabited___closed__1;
x_21 = l_Lean_Elab_Term_Do_mkUnless___closed__3;
x_22 = l_Lean_Elab_Term_Do_mkUnless___closed__8;
x_23 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_22);
x_24 = l_Lean_Syntax_copyInfo(x_23, x_1);
lean_inc(x_1);
x_25 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = l_Lean_mkOptionalNode___closed__1;
x_29 = lean_alloc_ctor(7, 6, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_17);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_2);
lean_ctor_set(x_29, 4, x_25);
lean_ctor_set(x_29, 5, x_27);
lean_ctor_set(x_3, 0, x_29);
lean_ctor_set(x_14, 0, x_3);
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_3);
x_32 = l_Lean_mkOptionalNode___closed__1;
x_33 = lean_alloc_ctor(7, 6, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_17);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_2);
lean_ctor_set(x_33, 4, x_25);
lean_ctor_set(x_33, 5, x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_14, 0, x_34);
return x_14;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
x_37 = lean_box(0);
x_38 = l_Lean_Elab_Term_Do_mkUnless___closed__6;
x_39 = l_Lean_addMacroScope(x_35, x_38, x_12);
x_40 = l_Lean_SourceInfo_inhabited___closed__1;
x_41 = l_Lean_Elab_Term_Do_mkUnless___closed__3;
x_42 = l_Lean_Elab_Term_Do_mkUnless___closed__8;
x_43 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_39);
lean_ctor_set(x_43, 3, x_42);
x_44 = l_Lean_Syntax_copyInfo(x_43, x_1);
lean_inc(x_1);
x_45 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_44);
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
x_49 = l_Lean_mkOptionalNode___closed__1;
x_50 = lean_alloc_ctor(7, 6, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_37);
lean_ctor_set(x_50, 2, x_49);
lean_ctor_set(x_50, 3, x_2);
lean_ctor_set(x_50, 4, x_45);
lean_ctor_set(x_50, 5, x_46);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_36);
return x_52;
}
}
}
lean_object* l_Lean_Elab_Term_Do_mkUnless___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_Do_mkUnless(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_Do_concat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Elab_Term_Do_homogenize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = l___private_Lean_Elab_Do_5__nameSetToArray(x_16);
x_18 = l_Lean_Elab_Term_Do_mkFreshJP___closed__4;
x_19 = l___private_Lean_CoreM_1__mkFreshNameImp(x_18, x_7, x_8, x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_17);
x_22 = x_17;
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_mkFreshJP_x27___spec__1(x_23, x_22);
x_25 = x_24;
x_26 = 0;
x_27 = lean_box(x_26);
lean_ctor_set(x_11, 1, x_27);
lean_ctor_set(x_11, 0, x_20);
x_28 = lean_array_push(x_25, x_11);
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
x_30 = l_Lean_Elab_Term_Do_mkFreshJP(x_28, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_33, x_17, x_35);
x_37 = l_Lean_Elab_Term_Do_attachJP(x_32, x_36);
lean_dec(x_32);
lean_ctor_set(x_14, 0, x_37);
lean_ctor_set(x_30, 0, x_14);
return x_30;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_14, 0);
x_39 = lean_ctor_get(x_14, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_14);
x_40 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_33, x_17, x_38);
x_41 = l_Lean_Elab_Term_Do_attachJP(x_32, x_40);
lean_dec(x_32);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_30, 0, x_42);
return x_30;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_30, 0);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_30);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_14, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_14, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_48 = x_14;
} else {
 lean_dec_ref(x_14);
 x_48 = lean_box(0);
}
x_49 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_45, x_17, x_46);
x_50 = l_Lean_Elab_Term_Do_attachJP(x_43, x_49);
lean_dec(x_43);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_44);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_53 = lean_ctor_get(x_11, 0);
x_54 = lean_ctor_get(x_11, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_11);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
x_56 = l___private_Lean_Elab_Do_5__nameSetToArray(x_55);
x_57 = l_Lean_Elab_Term_Do_mkFreshJP___closed__4;
x_58 = l___private_Lean_CoreM_1__mkFreshNameImp(x_57, x_7, x_8, x_12);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_56);
x_61 = x_56;
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_mkFreshJP_x27___spec__1(x_62, x_61);
x_64 = x_63;
x_65 = 0;
x_66 = lean_box(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_array_push(x_64, x_67);
x_69 = lean_ctor_get(x_54, 0);
lean_inc(x_69);
lean_dec(x_54);
x_70 = l_Lean_Elab_Term_Do_mkFreshJP(x_68, x_69, x_3, x_4, x_5, x_6, x_7, x_8, x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_53, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_53, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_77 = x_53;
} else {
 lean_dec_ref(x_53);
 x_77 = lean_box(0);
}
x_78 = l_Lean_Elab_Term_Do_convertReturnIntoJmpAux___main(x_74, x_56, x_75);
x_79 = l_Lean_Elab_Term_Do_attachJP(x_71, x_78);
lean_dec(x_71);
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_77;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_76);
if (lean_is_scalar(x_73)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_73;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_72);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_10);
if (x_82 == 0)
{
return x_10;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_10, 0);
x_84 = lean_ctor_get(x_10, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_10);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Do_7__getDoSeqElems___spec__1(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_4, x_6);
lean_dec(x_4);
x_8 = l_List_map___main___at___private_Lean_Elab_Do_7__getDoSeqElems___spec__1(x_5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_9, x_11);
lean_dec(x_9);
x_13 = l_List_map___main___at___private_Lean_Elab_Do_7__getDoSeqElems___spec__1(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l___private_Lean_Elab_Do_7__getDoSeqElems(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
x_2 = l_Lean_Syntax_getKind(x_1);
x_3 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__6;
x_4 = lean_name_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4;
x_6 = lean_name_eq(x_2, x_5);
lean_dec(x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_11 = l_Array_toList___rarg(x_10);
lean_dec(x_10);
x_12 = l_List_map___main___at___private_Lean_Elab_Do_7__getDoSeqElems___spec__1(x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = l_Array_toList___rarg(x_15);
lean_dec(x_15);
x_17 = l_List_map___main___at___private_Lean_Elab_Do_7__getDoSeqElems___spec__1(x_16);
return x_17;
}
}
}
lean_object* l___private_Lean_Elab_Do_8__getDoSeq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Do_8__getDoSeq___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Do_8__getDoSeq(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_Do_getLetIdDeclVar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getId(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_Do_getLetIdDeclVar___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_Do_getLetIdDeclVar(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_filterMapMAux___main___at_Lean_Elab_Term_Do_getLetPatDeclVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; 
x_6 = lean_array_fget(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_10 = lean_array_push(x_3, x_7);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
lean_dec(x_2);
x_2 = x_13;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_getLetPatDeclVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Elab_Term_getPatternVars(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Array_empty___closed__1;
x_15 = l_Array_filterMapMAux___main___at_Lean_Elab_Term_Do_getLetPatDeclVars___spec__1(x_13, x_9, x_14);
lean_dec(x_13);
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
x_18 = l_Array_empty___closed__1;
x_19 = l_Array_filterMapMAux___main___at_Lean_Elab_Term_Do_getLetPatDeclVars___spec__1(x_16, x_9, x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
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
lean_object* l_Array_filterMapMAux___main___at_Lean_Elab_Term_Do_getLetPatDeclVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapMAux___main___at_Lean_Elab_Term_Do_getLetPatDeclVars___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_Do_getLetPatDeclVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_Do_getLetPatDeclVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_Do_getLetEqnsDeclVar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getId(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_Do_getLetEqnsDeclVar___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_Do_getLetEqnsDeclVar(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_getLetDeclVars___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected kind of let declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_getLetDeclVars___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_getLetDeclVars___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_getLetDeclVars___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_getLetDeclVars___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_Do_getLetDeclVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_inc(x_10);
x_11 = l_Lean_Syntax_getKind(x_10);
x_12 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__8;
x_13 = lean_name_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Elab_Term_elabLetDeclCore___closed__2;
x_15 = lean_name_eq(x_11, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Elab_Term_elabLetDeclCore___closed__4;
x_17 = lean_name_eq(x_11, x_16);
lean_dec(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
x_18 = l_Lean_Elab_Term_Do_getLetDeclVars___closed__3;
x_19 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = l_Lean_Elab_Term_Do_getLetEqnsDeclVar(x_10);
lean_dec(x_10);
x_21 = l_Lean_mkOptionalNode___closed__2;
x_22 = lean_array_push(x_21, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_11);
x_24 = l_Lean_Elab_Term_Do_getLetPatDeclVars(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = l_Lean_Elab_Term_Do_getLetIdDeclVar(x_10);
lean_dec(x_10);
x_26 = l_Lean_mkOptionalNode___closed__2;
x_27 = lean_array_push(x_26, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
}
}
lean_object* l_Lean_Elab_Term_Do_getLetDeclVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_Do_getLetDeclVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_Do_getDoLetVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Elab_Term_Do_getLetDeclVars(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_Do_getDoLetVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_Do_getDoLetVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_getDoLetRecVars___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_9, x_10);
lean_dec(x_9);
x_12 = lean_nat_add(x_1, x_10);
x_13 = x_11;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_getDoLetRecVars___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_3, x_12);
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
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_fget(x_2, x_3);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Elab_Term_Do_getLetDeclVars(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_19, x_19, x_21, x_4);
lean_dec(x_19);
x_3 = x_17;
x_4 = x_22;
x_11 = x_20;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* l_Lean_Elab_Term_Do_getDoLetRecVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_empty___closed__1;
x_15 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_12, x_11, x_13, x_14);
lean_dec(x_11);
x_16 = x_15;
x_17 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_getDoLetRecVars___spec__1(x_13, x_16);
x_18 = x_17;
x_19 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_getDoLetRecVars___spec__2(x_1, x_18, x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_18);
return x_19;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_getDoLetRecVars___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_getDoLetRecVars___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_Do_getDoLetRecVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_Do_getDoLetRecVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_Do_getDoIdDeclVar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getId(x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_Do_getDoIdDeclVar___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_Do_getDoIdDeclVar(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_Do_getDoPatDeclVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Elab_Term_getPatternVars(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Array_empty___closed__1;
x_15 = l_Array_filterMapMAux___main___at_Lean_Elab_Term_Do_getLetPatDeclVars___spec__1(x_13, x_9, x_14);
lean_dec(x_13);
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
x_18 = l_Array_empty___closed__1;
x_19 = l_Array_filterMapMAux___main___at_Lean_Elab_Term_Do_getLetPatDeclVars___spec__1(x_16, x_9, x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
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
lean_object* l_Lean_Elab_Term_Do_getDoPatDeclVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_Do_getDoPatDeclVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doIdDecl");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doPatDecl");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected kind of 'do' declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_Do_getDoLetArrowVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_inc(x_10);
x_11 = l_Lean_Syntax_getKind(x_10);
x_12 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
x_13 = lean_name_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__4;
x_15 = lean_name_eq(x_11, x_14);
lean_dec(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
x_16 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__7;
x_17 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_Elab_Term_Do_getDoPatDeclVars(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = l_Lean_Elab_Term_Do_getDoIdDeclVar(x_10);
lean_dec(x_10);
x_20 = l_Lean_mkOptionalNode___closed__2;
x_21 = lean_array_push(x_20, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
}
}
lean_object* l_Lean_Elab_Term_Do_getDoLetArrowVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_Do_getDoLetArrowVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_getDoReassignVars___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected kind of reassignment");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_getDoReassignVars___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_getDoReassignVars___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_getDoReassignVars___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_getDoReassignVars___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_Do_getDoReassignVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_inc(x_10);
x_11 = l_Lean_Syntax_getKind(x_10);
x_12 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__8;
x_13 = lean_name_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Elab_Term_elabLetDeclCore___closed__2;
x_15 = lean_name_eq(x_11, x_14);
lean_dec(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
x_16 = l_Lean_Elab_Term_Do_getDoReassignVars___closed__3;
x_17 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_Elab_Term_Do_getLetPatDeclVars(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = l_Lean_Elab_Term_Do_getLetIdDeclVar(x_10);
lean_dec(x_10);
x_20 = l_Lean_mkOptionalNode___closed__2;
x_21 = lean_array_push(x_20, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
}
}
lean_object* l_Lean_Elab_Term_Do_getDoReassignVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_Do_getDoReassignVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_Do_toDoSeq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = l_Lean_mkAppStx___closed__9;
x_3 = lean_array_push(x_2, x_1);
x_4 = l_Lean_mkOptionalNode___closed__1;
x_5 = lean_array_push(x_3, x_4);
x_6 = l_Lean_nullKind;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_mkOptionalNode___closed__2;
x_9 = lean_array_push(x_8, x_7);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_push(x_8, x_10);
x_12 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
lean_object* _init_l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doIf");
return x_1;
}
}
lean_object* _init_l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_array_fget(x_2, x_9);
x_11 = l_Lean_Syntax_getArg(x_10, x_6);
x_12 = l_Lean_Syntax_getArg(x_11, x_8);
lean_dec(x_11);
x_13 = l_Lean_Syntax_getArgs(x_10);
x_14 = lean_array_set(x_13, x_6, x_12);
x_15 = l_Lean_mkOptionalNode___closed__1;
x_16 = lean_array_push(x_14, x_15);
x_17 = lean_array_push(x_16, x_5);
x_18 = l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__27;
x_19 = l_Lean_mkAtomFrom(x_10, x_18);
lean_dec(x_10);
x_20 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1___closed__2;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
x_22 = l_Lean_Elab_Term_Do_toDoSeq(x_21);
x_23 = l_Lean_mkAppStx___closed__9;
x_24 = lean_array_push(x_23, x_19);
x_25 = lean_array_push(x_24, x_22);
x_26 = l_Lean_nullKind;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_3 = x_9;
x_4 = lean_box(0);
x_5 = x_27;
goto _start;
}
else
{
lean_dec(x_3);
return x_5;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_array_fget(x_2, x_9);
x_11 = l_Lean_Syntax_getArg(x_10, x_6);
x_12 = l_Lean_Syntax_getArg(x_11, x_8);
lean_dec(x_11);
x_13 = l_Lean_Syntax_getArgs(x_10);
x_14 = lean_array_set(x_13, x_6, x_12);
x_15 = l_Lean_mkOptionalNode___closed__1;
x_16 = lean_array_push(x_14, x_15);
x_17 = lean_array_push(x_16, x_5);
x_18 = l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__27;
x_19 = l_Lean_mkAtomFrom(x_10, x_18);
lean_dec(x_10);
x_20 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1___closed__2;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
x_22 = l_Lean_Elab_Term_Do_toDoSeq(x_21);
x_23 = l_Lean_mkAppStx___closed__9;
x_24 = lean_array_push(x_23, x_19);
x_25 = lean_array_push(x_24, x_22);
x_26 = l_Lean_nullKind;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_3 = x_9;
x_4 = lean_box(0);
x_5 = x_27;
goto _start;
}
else
{
lean_dec(x_3);
return x_5;
}
}
}
lean_object* _init_l___private_Lean_Elab_Do_9__expandDoIf___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doReturn");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Do_9__expandDoIf___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_Do_9__expandDoIf___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Do_9__expandDoIf___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("return");
return x_1;
}
}
lean_object* l___private_Lean_Elab_Do_9__expandDoIf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_33; 
x_2 = lean_unsigned_to_nat(5u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(6u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_33 = l_Array_isEmpty___rarg(x_4);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_box(0);
x_7 = x_34;
goto block_32;
}
else
{
uint8_t x_35; 
x_35 = l_Lean_Syntax_isNone(x_6);
if (x_35 == 0)
{
lean_dec(x_6);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_36; 
x_36 = lean_box(0);
x_7 = x_36;
goto block_32;
}
}
block_32:
{
uint8_t x_8; lean_object* x_9; 
lean_dec(x_7);
x_8 = l_Lean_Syntax_isNone(x_6);
x_9 = lean_array_get_size(x_4);
if (x_8 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1(x_1, x_4, x_9, lean_box(0), x_6);
lean_dec(x_4);
x_11 = l_Lean_Syntax_setArg(x_1, x_5, x_10);
x_12 = l_Lean_mkOptionalNode___closed__1;
x_13 = l_Lean_Syntax_setArg(x_11, x_2, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_14 = l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__27;
x_15 = l_Lean_mkAtomFrom(x_1, x_14);
x_16 = l___private_Lean_Elab_Do_9__expandDoIf___closed__3;
x_17 = l_Lean_mkAtomFrom(x_1, x_16);
x_18 = l_Lean_mkAppStx___closed__9;
x_19 = lean_array_push(x_18, x_17);
x_20 = l_Lean_mkOptionalNode___closed__1;
x_21 = lean_array_push(x_19, x_20);
x_22 = l___private_Lean_Elab_Do_9__expandDoIf___closed__2;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_Term_Do_toDoSeq(x_23);
x_25 = lean_array_push(x_18, x_15);
x_26 = lean_array_push(x_25, x_24);
x_27 = l_Lean_nullKind;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__2(x_1, x_4, x_9, lean_box(0), x_28);
lean_dec(x_4);
x_30 = l_Lean_Syntax_setArg(x_1, x_5, x_29);
x_31 = l_Lean_Syntax_setArg(x_30, x_2, x_20);
return x_31;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Do_10__mkDoIfView(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l___private_Lean_Elab_Do_9__expandDoIf(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = lean_unsigned_to_nat(4u);
x_8 = l_Lean_Syntax_getArg(x_2, x_7);
x_9 = lean_unsigned_to_nat(6u);
x_10 = l_Lean_Syntax_getArg(x_2, x_9);
x_11 = l_Lean_Syntax_getArg(x_10, x_3);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 3, x_8);
lean_ctor_set(x_12, 4, x_11);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Do_11__mkPUnit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Elab_Term_Do_mkUnless___closed__6;
x_7 = l_Lean_addMacroScope(x_5, x_6, x_4);
x_8 = l_Lean_SourceInfo_inhabited___closed__1;
x_9 = l_Lean_Elab_Term_Do_mkUnless___closed__3;
x_10 = l_Lean_Elab_Term_Do_mkUnless___closed__8;
x_11 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_7);
lean_ctor_set(x_11, 3, x_10);
x_12 = l_Lean_Syntax_copyInfo(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Do_11__mkPUnit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Do_11__mkPUnit(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_12__mkTuple___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_12__mkTuple___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_4, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_4, x_11);
lean_dec(x_4);
x_13 = lean_array_fget(x_3, x_12);
x_14 = l_Array_empty___closed__1;
x_15 = lean_array_push(x_14, x_13);
x_16 = lean_array_push(x_14, x_6);
x_17 = l_Lean_nullKind___closed__2;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_12__mkTuple___spec__1___closed__1;
x_20 = lean_array_push(x_19, x_18);
x_21 = l_Lean_Elab_Term_elabParen___closed__5;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_array_push(x_14, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_push(x_15, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_28 = lean_array_push(x_27, x_26);
x_29 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_30 = lean_array_push(x_28, x_29);
x_31 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Syntax_copyInfo(x_32, x_1);
x_4 = x_12;
x_5 = lean_box(0);
x_6 = x_33;
goto _start;
}
else
{
lean_object* x_35; 
lean_dec(x_4);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_6);
lean_ctor_set(x_35, 1, x_8);
return x_35;
}
}
}
lean_object* l___private_Lean_Elab_Do_12__mkTuple(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_2);
x_11 = lean_nat_sub(x_5, x_8);
lean_dec(x_5);
x_12 = l_Array_extract___rarg(x_2, x_6, x_11);
lean_dec(x_11);
x_13 = lean_array_get_size(x_12);
x_14 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_12__mkTuple___spec__1(x_1, x_2, x_12, x_13, lean_box(0), x_10, x_3, x_4);
lean_dec(x_3);
lean_dec(x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_3);
x_15 = l_Lean_Syntax_inhabited;
x_16 = lean_array_get(x_15, x_2, x_6);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_5);
x_18 = l___private_Lean_Elab_Do_11__mkPUnit(x_1, x_3, x_4);
return x_18;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_12__mkTuple___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_12__mkTuple___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Do_12__mkTuple___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Do_12__mkTuple(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkUVarTuple___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_mkIdentFrom(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkUVarTuple(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = x_5;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkUVarTuple___spec__1(x_1, x_7, x_6);
x_9 = x_8;
x_10 = l___private_Lean_Elab_Do_12__mkTuple(x_1, x_9, x_3, x_4);
lean_dec(x_9);
return x_10;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkUVarTuple___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkUVarTuple___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkUVarTuple___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_Do_ToTerm_mkUVarTuple(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkResultUVarTuple(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = l_Array_isEmpty___rarg(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_4);
x_8 = l_Lean_Elab_Term_Do_ToTerm_mkUVarTuple(x_1, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_mkAppStx___closed__9;
x_12 = lean_array_push(x_11, x_2);
x_13 = lean_array_push(x_12, x_9);
x_14 = l___private_Lean_Elab_Do_12__mkTuple(x_1, x_13, x_4, x_10);
lean_dec(x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkResultUVarTuple___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_Do_ToTerm_mkResultUVarTuple(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HasPure.pure");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Do_13__mkForInYield___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Do_13__mkForInYield___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Do_13__mkForInYield___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkPure___rarg___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Do_13__mkForInYield___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ForInStep.yield");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Do_13__mkForInYield___closed__6;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Do_13__mkForInYield___closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Do_13__mkForInYield___closed__7;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ForInStep");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Do_13__mkForInYield___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("yield");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Do_13__mkForInYield___closed__10;
x_2 = l___private_Lean_Elab_Do_13__mkForInYield___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Do_13__mkForInYield___closed__12;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Do_13__mkForInYield___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Do_13__mkForInYield(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_3);
x_5 = l_Lean_Elab_Term_Do_ToTerm_mkUVarTuple(x_1, x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_Meta_mkPure___rarg___closed__4;
lean_inc(x_8);
lean_inc(x_9);
x_11 = l_Lean_addMacroScope(x_9, x_10, x_8);
x_12 = l_Lean_SourceInfo_inhabited___closed__1;
x_13 = l___private_Lean_Elab_Do_13__mkForInYield___closed__3;
x_14 = l___private_Lean_Elab_Do_13__mkForInYield___closed__5;
x_15 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_14);
x_16 = l_Array_empty___closed__1;
x_17 = lean_array_push(x_16, x_15);
x_18 = l___private_Lean_Elab_Do_13__mkForInYield___closed__12;
x_19 = l_Lean_addMacroScope(x_9, x_18, x_8);
x_20 = l___private_Lean_Elab_Do_13__mkForInYield___closed__8;
x_21 = l___private_Lean_Elab_Do_13__mkForInYield___closed__14;
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_21);
x_23 = lean_array_push(x_16, x_22);
x_24 = lean_array_push(x_16, x_7);
x_25 = l_Lean_nullKind___closed__2;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_array_push(x_23, x_26);
x_28 = l_Lean_mkAppStx___closed__8;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_array_push(x_16, x_29);
x_31 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_32 = lean_array_push(x_30, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_35 = lean_array_push(x_34, x_33);
x_36 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_37 = lean_array_push(x_35, x_36);
x_38 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_array_push(x_16, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_25);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_array_push(x_17, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_5, 0, x_43);
return x_5;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_44 = lean_ctor_get(x_5, 0);
x_45 = lean_ctor_get(x_5, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_5);
x_46 = lean_ctor_get(x_3, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
lean_dec(x_3);
x_48 = l_Lean_Meta_mkPure___rarg___closed__4;
lean_inc(x_46);
lean_inc(x_47);
x_49 = l_Lean_addMacroScope(x_47, x_48, x_46);
x_50 = l_Lean_SourceInfo_inhabited___closed__1;
x_51 = l___private_Lean_Elab_Do_13__mkForInYield___closed__3;
x_52 = l___private_Lean_Elab_Do_13__mkForInYield___closed__5;
x_53 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set(x_53, 3, x_52);
x_54 = l_Array_empty___closed__1;
x_55 = lean_array_push(x_54, x_53);
x_56 = l___private_Lean_Elab_Do_13__mkForInYield___closed__12;
x_57 = l_Lean_addMacroScope(x_47, x_56, x_46);
x_58 = l___private_Lean_Elab_Do_13__mkForInYield___closed__8;
x_59 = l___private_Lean_Elab_Do_13__mkForInYield___closed__14;
x_60 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_57);
lean_ctor_set(x_60, 3, x_59);
x_61 = lean_array_push(x_54, x_60);
x_62 = lean_array_push(x_54, x_44);
x_63 = l_Lean_nullKind___closed__2;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_array_push(x_61, x_64);
x_66 = l_Lean_mkAppStx___closed__8;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_array_push(x_54, x_67);
x_69 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_70 = lean_array_push(x_68, x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_73 = lean_array_push(x_72, x_71);
x_74 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_75 = lean_array_push(x_73, x_74);
x_76 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_array_push(x_54, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_63);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_array_push(x_55, x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_66);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_45);
return x_82;
}
}
}
lean_object* l___private_Lean_Elab_Do_13__mkForInYield___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Do_13__mkForInYield(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Do_14__mkForInMapYield(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_4);
x_6 = l_Lean_Elab_Term_Do_ToTerm_mkUVarTuple(x_1, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_mkIdentFrom(x_1, x_2);
x_10 = l_Lean_mkAppStx___closed__9;
x_11 = lean_array_push(x_10, x_9);
x_12 = lean_array_push(x_11, x_7);
lean_inc(x_4);
x_13 = l___private_Lean_Elab_Do_12__mkTuple(x_1, x_12, x_4, x_8);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = l_Lean_Meta_mkPure___rarg___closed__4;
lean_inc(x_16);
lean_inc(x_17);
x_19 = l_Lean_addMacroScope(x_17, x_18, x_16);
x_20 = l_Lean_SourceInfo_inhabited___closed__1;
x_21 = l___private_Lean_Elab_Do_13__mkForInYield___closed__3;
x_22 = l___private_Lean_Elab_Do_13__mkForInYield___closed__5;
x_23 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_22);
x_24 = l_Array_empty___closed__1;
x_25 = lean_array_push(x_24, x_23);
x_26 = l___private_Lean_Elab_Do_13__mkForInYield___closed__12;
x_27 = l_Lean_addMacroScope(x_17, x_26, x_16);
x_28 = l___private_Lean_Elab_Do_13__mkForInYield___closed__8;
x_29 = l___private_Lean_Elab_Do_13__mkForInYield___closed__14;
x_30 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_29);
x_31 = lean_array_push(x_24, x_30);
x_32 = lean_array_push(x_24, x_15);
x_33 = l_Lean_nullKind___closed__2;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_array_push(x_31, x_34);
x_36 = l_Lean_mkAppStx___closed__8;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_array_push(x_24, x_37);
x_39 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_40 = lean_array_push(x_38, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_43 = lean_array_push(x_42, x_41);
x_44 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_45 = lean_array_push(x_43, x_44);
x_46 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_array_push(x_24, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_33);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_array_push(x_25, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_36);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_13, 0, x_51);
return x_13;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_52 = lean_ctor_get(x_13, 0);
x_53 = lean_ctor_get(x_13, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_13);
x_54 = lean_ctor_get(x_4, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_4, 1);
lean_inc(x_55);
lean_dec(x_4);
x_56 = l_Lean_Meta_mkPure___rarg___closed__4;
lean_inc(x_54);
lean_inc(x_55);
x_57 = l_Lean_addMacroScope(x_55, x_56, x_54);
x_58 = l_Lean_SourceInfo_inhabited___closed__1;
x_59 = l___private_Lean_Elab_Do_13__mkForInYield___closed__3;
x_60 = l___private_Lean_Elab_Do_13__mkForInYield___closed__5;
x_61 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_57);
lean_ctor_set(x_61, 3, x_60);
x_62 = l_Array_empty___closed__1;
x_63 = lean_array_push(x_62, x_61);
x_64 = l___private_Lean_Elab_Do_13__mkForInYield___closed__12;
x_65 = l_Lean_addMacroScope(x_55, x_64, x_54);
x_66 = l___private_Lean_Elab_Do_13__mkForInYield___closed__8;
x_67 = l___private_Lean_Elab_Do_13__mkForInYield___closed__14;
x_68 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set(x_68, 2, x_65);
lean_ctor_set(x_68, 3, x_67);
x_69 = lean_array_push(x_62, x_68);
x_70 = lean_array_push(x_62, x_52);
x_71 = l_Lean_nullKind___closed__2;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_array_push(x_69, x_72);
x_74 = l_Lean_mkAppStx___closed__8;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_array_push(x_62, x_75);
x_77 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_78 = lean_array_push(x_76, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_71);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_81 = lean_array_push(x_80, x_79);
x_82 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_83 = lean_array_push(x_81, x_82);
x_84 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = lean_array_push(x_62, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_71);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_array_push(x_63, x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_74);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_53);
return x_90;
}
}
}
lean_object* l___private_Lean_Elab_Do_14__mkForInMapYield___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Do_14__mkForInMapYield(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("DoResult.«return»");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("DoResult");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__5;
x_2 = l___private_Lean_Elab_Do_9__expandDoIf___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_returnToTermCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; uint8_t x_8; 
lean_inc(x_4);
x_7 = l_Lean_Elab_Term_Do_ToTerm_mkResultUVarTuple(x_1, x_2, x_3, x_4, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = l_Lean_Meta_mkPure___rarg___closed__4;
x_13 = l_Lean_addMacroScope(x_11, x_12, x_10);
x_14 = l_Lean_SourceInfo_inhabited___closed__1;
x_15 = l___private_Lean_Elab_Do_13__mkForInYield___closed__3;
x_16 = l___private_Lean_Elab_Do_13__mkForInYield___closed__5;
x_17 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_16);
x_18 = l_Array_empty___closed__1;
x_19 = lean_array_push(x_18, x_17);
x_20 = lean_array_push(x_18, x_9);
x_21 = l_Lean_nullKind___closed__2;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_array_push(x_19, x_22);
x_24 = l_Lean_mkAppStx___closed__8;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_7, 0, x_25);
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_ctor_get(x_4, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_dec(x_4);
x_30 = l_Lean_Meta_mkPure___rarg___closed__4;
x_31 = l_Lean_addMacroScope(x_29, x_30, x_28);
x_32 = l_Lean_SourceInfo_inhabited___closed__1;
x_33 = l___private_Lean_Elab_Do_13__mkForInYield___closed__3;
x_34 = l___private_Lean_Elab_Do_13__mkForInYield___closed__5;
x_35 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_31);
lean_ctor_set(x_35, 3, x_34);
x_36 = l_Array_empty___closed__1;
x_37 = lean_array_push(x_36, x_35);
x_38 = lean_array_push(x_36, x_26);
x_39 = l_Lean_nullKind___closed__2;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_array_push(x_37, x_40);
x_42 = l_Lean_mkAppStx___closed__8;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_27);
return x_44;
}
}
case 1:
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_2);
lean_inc(x_4);
x_45 = l_Lean_Elab_Term_Do_ToTerm_mkUVarTuple(x_1, x_3, x_4, x_5);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_4, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
lean_dec(x_4);
x_50 = l_Lean_Meta_mkPure___rarg___closed__4;
lean_inc(x_48);
lean_inc(x_49);
x_51 = l_Lean_addMacroScope(x_49, x_50, x_48);
x_52 = l_Lean_SourceInfo_inhabited___closed__1;
x_53 = l___private_Lean_Elab_Do_13__mkForInYield___closed__3;
x_54 = l___private_Lean_Elab_Do_13__mkForInYield___closed__5;
x_55 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_51);
lean_ctor_set(x_55, 3, x_54);
x_56 = l_Array_empty___closed__1;
x_57 = lean_array_push(x_56, x_55);
x_58 = l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__6;
x_59 = l_Lean_addMacroScope(x_49, x_58, x_48);
x_60 = l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__3;
x_61 = l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__8;
x_62 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_62, 0, x_52);
lean_ctor_set(x_62, 1, x_60);
lean_ctor_set(x_62, 2, x_59);
lean_ctor_set(x_62, 3, x_61);
x_63 = lean_array_push(x_56, x_62);
x_64 = lean_array_push(x_56, x_47);
x_65 = l_Lean_nullKind___closed__2;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = lean_array_push(x_63, x_66);
x_68 = l_Lean_mkAppStx___closed__8;
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_array_push(x_56, x_69);
x_71 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_72 = lean_array_push(x_70, x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_65);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_75 = lean_array_push(x_74, x_73);
x_76 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_77 = lean_array_push(x_75, x_76);
x_78 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_array_push(x_56, x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_65);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_array_push(x_57, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_68);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_45, 0, x_83);
return x_45;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_84 = lean_ctor_get(x_45, 0);
x_85 = lean_ctor_get(x_45, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_45);
x_86 = lean_ctor_get(x_4, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_4, 1);
lean_inc(x_87);
lean_dec(x_4);
x_88 = l_Lean_Meta_mkPure___rarg___closed__4;
lean_inc(x_86);
lean_inc(x_87);
x_89 = l_Lean_addMacroScope(x_87, x_88, x_86);
x_90 = l_Lean_SourceInfo_inhabited___closed__1;
x_91 = l___private_Lean_Elab_Do_13__mkForInYield___closed__3;
x_92 = l___private_Lean_Elab_Do_13__mkForInYield___closed__5;
x_93 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_93, 2, x_89);
lean_ctor_set(x_93, 3, x_92);
x_94 = l_Array_empty___closed__1;
x_95 = lean_array_push(x_94, x_93);
x_96 = l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__6;
x_97 = l_Lean_addMacroScope(x_87, x_96, x_86);
x_98 = l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__3;
x_99 = l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__8;
x_100 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_98);
lean_ctor_set(x_100, 2, x_97);
lean_ctor_set(x_100, 3, x_99);
x_101 = lean_array_push(x_94, x_100);
x_102 = lean_array_push(x_94, x_84);
x_103 = l_Lean_nullKind___closed__2;
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = lean_array_push(x_101, x_104);
x_106 = l_Lean_mkAppStx___closed__8;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = lean_array_push(x_94, x_107);
x_109 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_110 = lean_array_push(x_108, x_109);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_113 = lean_array_push(x_112, x_111);
x_114 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_115 = lean_array_push(x_113, x_114);
x_116 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = lean_array_push(x_94, x_117);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_103);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_array_push(x_95, x_119);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_106);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_85);
return x_122;
}
}
case 2:
{
lean_object* x_123; 
lean_dec(x_2);
x_123 = l___private_Lean_Elab_Do_13__mkForInYield(x_1, x_3, x_4, x_5);
return x_123;
}
default: 
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_2);
x_124 = lean_ctor_get(x_6, 0);
lean_inc(x_124);
lean_dec(x_6);
x_125 = l___private_Lean_Elab_Do_14__mkForInMapYield(x_1, x_124, x_3, x_4, x_5);
return x_125;
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_Do_ToTerm_returnToTermCore(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_returnToTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Elab_Term_Do_ToTerm_returnToTermCore(x_1, x_2, x_3, x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_Syntax_copyInfo(x_8, x_1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = l_Lean_Syntax_copyInfo(x_10, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_returnToTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_Do_ToTerm_returnToTerm(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_EST_Monad___closed__1;
x_2 = l_Lean_Syntax_inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_inhabited___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__2;
x_2 = lean_alloc_closure((void*)(l_ReaderT_inhabited___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("DoResult.«continue»");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__4;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("continue");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__5;
x_2 = l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_continueToTermCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__3;
x_7 = l_unreachable_x21___rarg(x_6);
x_8 = lean_apply_3(x_7, x_2, x_3, x_4);
return x_8;
}
case 1:
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_3);
x_9 = l_Lean_Elab_Term_Do_ToTerm_mkUVarTuple(x_1, x_2, x_3, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec(x_3);
x_14 = l_Lean_Meta_mkPure___rarg___closed__4;
lean_inc(x_12);
lean_inc(x_13);
x_15 = l_Lean_addMacroScope(x_13, x_14, x_12);
x_16 = l_Lean_SourceInfo_inhabited___closed__1;
x_17 = l___private_Lean_Elab_Do_13__mkForInYield___closed__3;
x_18 = l___private_Lean_Elab_Do_13__mkForInYield___closed__5;
x_19 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_18);
x_20 = l_Array_empty___closed__1;
x_21 = lean_array_push(x_20, x_19);
x_22 = l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__8;
x_23 = l_Lean_addMacroScope(x_13, x_22, x_12);
x_24 = l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__6;
x_25 = l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__10;
x_26 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_array_push(x_20, x_26);
x_28 = lean_array_push(x_20, x_11);
x_29 = l_Lean_nullKind___closed__2;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_array_push(x_27, x_30);
x_32 = l_Lean_mkAppStx___closed__8;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_array_push(x_20, x_33);
x_35 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_36 = lean_array_push(x_34, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_39 = lean_array_push(x_38, x_37);
x_40 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_41 = lean_array_push(x_39, x_40);
x_42 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_array_push(x_20, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_29);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_array_push(x_21, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_32);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_9, 0, x_47);
return x_9;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_48 = lean_ctor_get(x_9, 0);
x_49 = lean_ctor_get(x_9, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_9);
x_50 = lean_ctor_get(x_3, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_3, 1);
lean_inc(x_51);
lean_dec(x_3);
x_52 = l_Lean_Meta_mkPure___rarg___closed__4;
lean_inc(x_50);
lean_inc(x_51);
x_53 = l_Lean_addMacroScope(x_51, x_52, x_50);
x_54 = l_Lean_SourceInfo_inhabited___closed__1;
x_55 = l___private_Lean_Elab_Do_13__mkForInYield___closed__3;
x_56 = l___private_Lean_Elab_Do_13__mkForInYield___closed__5;
x_57 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_53);
lean_ctor_set(x_57, 3, x_56);
x_58 = l_Array_empty___closed__1;
x_59 = lean_array_push(x_58, x_57);
x_60 = l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__8;
x_61 = l_Lean_addMacroScope(x_51, x_60, x_50);
x_62 = l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__6;
x_63 = l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__10;
x_64 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_64, 0, x_54);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_61);
lean_ctor_set(x_64, 3, x_63);
x_65 = lean_array_push(x_58, x_64);
x_66 = lean_array_push(x_58, x_48);
x_67 = l_Lean_nullKind___closed__2;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_array_push(x_65, x_68);
x_70 = l_Lean_mkAppStx___closed__8;
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_array_push(x_58, x_71);
x_73 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_74 = lean_array_push(x_72, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_77 = lean_array_push(x_76, x_75);
x_78 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_79 = lean_array_push(x_77, x_78);
x_80 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_array_push(x_58, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_67);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_array_push(x_59, x_83);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_70);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_49);
return x_86;
}
}
case 2:
{
lean_object* x_87; 
x_87 = l___private_Lean_Elab_Do_13__mkForInYield(x_1, x_2, x_3, x_4);
return x_87;
}
default: 
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_5, 0);
lean_inc(x_88);
lean_dec(x_5);
x_89 = l___private_Lean_Elab_Do_14__mkForInMapYield(x_1, x_88, x_2, x_3, x_4);
return x_89;
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_Do_ToTerm_continueToTermCore(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_continueToTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_Do_ToTerm_continueToTermCore(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_Syntax_copyInfo(x_7, x_1);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = l_Lean_Syntax_copyInfo(x_9, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_continueToTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_Do_ToTerm_continueToTerm(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("DoResult.«break»");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("break");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__5;
x_2 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ForInStep.done");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__8;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__8;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__9;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Do_13__mkForInYield___closed__10;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalDone___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTermCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__3;
x_7 = l_unreachable_x21___rarg(x_6);
x_8 = lean_apply_3(x_7, x_2, x_3, x_4);
return x_8;
}
case 1:
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_3);
x_9 = l_Lean_Elab_Term_Do_ToTerm_mkUVarTuple(x_1, x_2, x_3, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec(x_3);
x_14 = l_Lean_Meta_mkPure___rarg___closed__4;
lean_inc(x_12);
lean_inc(x_13);
x_15 = l_Lean_addMacroScope(x_13, x_14, x_12);
x_16 = l_Lean_SourceInfo_inhabited___closed__1;
x_17 = l___private_Lean_Elab_Do_13__mkForInYield___closed__3;
x_18 = l___private_Lean_Elab_Do_13__mkForInYield___closed__5;
x_19 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_18);
x_20 = l_Array_empty___closed__1;
x_21 = lean_array_push(x_20, x_19);
x_22 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__5;
x_23 = l_Lean_addMacroScope(x_13, x_22, x_12);
x_24 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__3;
x_25 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__7;
x_26 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_array_push(x_20, x_26);
x_28 = lean_array_push(x_20, x_11);
x_29 = l_Lean_nullKind___closed__2;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_array_push(x_27, x_30);
x_32 = l_Lean_mkAppStx___closed__8;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_array_push(x_20, x_33);
x_35 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_36 = lean_array_push(x_34, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_39 = lean_array_push(x_38, x_37);
x_40 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_41 = lean_array_push(x_39, x_40);
x_42 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_array_push(x_20, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_29);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_array_push(x_21, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_32);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_9, 0, x_47);
return x_9;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_48 = lean_ctor_get(x_9, 0);
x_49 = lean_ctor_get(x_9, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_9);
x_50 = lean_ctor_get(x_3, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_3, 1);
lean_inc(x_51);
lean_dec(x_3);
x_52 = l_Lean_Meta_mkPure___rarg___closed__4;
lean_inc(x_50);
lean_inc(x_51);
x_53 = l_Lean_addMacroScope(x_51, x_52, x_50);
x_54 = l_Lean_SourceInfo_inhabited___closed__1;
x_55 = l___private_Lean_Elab_Do_13__mkForInYield___closed__3;
x_56 = l___private_Lean_Elab_Do_13__mkForInYield___closed__5;
x_57 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_53);
lean_ctor_set(x_57, 3, x_56);
x_58 = l_Array_empty___closed__1;
x_59 = lean_array_push(x_58, x_57);
x_60 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__5;
x_61 = l_Lean_addMacroScope(x_51, x_60, x_50);
x_62 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__3;
x_63 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__7;
x_64 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_64, 0, x_54);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_61);
lean_ctor_set(x_64, 3, x_63);
x_65 = lean_array_push(x_58, x_64);
x_66 = lean_array_push(x_58, x_48);
x_67 = l_Lean_nullKind___closed__2;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_array_push(x_65, x_68);
x_70 = l_Lean_mkAppStx___closed__8;
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_array_push(x_58, x_71);
x_73 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_74 = lean_array_push(x_72, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_77 = lean_array_push(x_76, x_75);
x_78 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_79 = lean_array_push(x_77, x_78);
x_80 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_array_push(x_58, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_67);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_array_push(x_59, x_83);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_70);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_49);
return x_86;
}
}
case 2:
{
lean_object* x_87; uint8_t x_88; 
lean_inc(x_3);
x_87 = l_Lean_Elab_Term_Do_ToTerm_mkUVarTuple(x_1, x_2, x_3, x_4);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_ctor_get(x_3, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_3, 1);
lean_inc(x_91);
lean_dec(x_3);
x_92 = l_Lean_Meta_mkPure___rarg___closed__4;
lean_inc(x_90);
lean_inc(x_91);
x_93 = l_Lean_addMacroScope(x_91, x_92, x_90);
x_94 = l_Lean_SourceInfo_inhabited___closed__1;
x_95 = l___private_Lean_Elab_Do_13__mkForInYield___closed__3;
x_96 = l___private_Lean_Elab_Do_13__mkForInYield___closed__5;
x_97 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
lean_ctor_set(x_97, 2, x_93);
lean_ctor_set(x_97, 3, x_96);
x_98 = l_Array_empty___closed__1;
x_99 = lean_array_push(x_98, x_97);
x_100 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__11;
x_101 = l_Lean_addMacroScope(x_91, x_100, x_90);
x_102 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__10;
x_103 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__13;
x_104 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_104, 0, x_94);
lean_ctor_set(x_104, 1, x_102);
lean_ctor_set(x_104, 2, x_101);
lean_ctor_set(x_104, 3, x_103);
x_105 = lean_array_push(x_98, x_104);
x_106 = lean_array_push(x_98, x_89);
x_107 = l_Lean_nullKind___closed__2;
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = lean_array_push(x_105, x_108);
x_110 = l_Lean_mkAppStx___closed__8;
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
x_112 = lean_array_push(x_98, x_111);
x_113 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_114 = lean_array_push(x_112, x_113);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_117 = lean_array_push(x_116, x_115);
x_118 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_119 = lean_array_push(x_117, x_118);
x_120 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_array_push(x_98, x_121);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_107);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_array_push(x_99, x_123);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_110);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set(x_87, 0, x_125);
return x_87;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_126 = lean_ctor_get(x_87, 0);
x_127 = lean_ctor_get(x_87, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_87);
x_128 = lean_ctor_get(x_3, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_3, 1);
lean_inc(x_129);
lean_dec(x_3);
x_130 = l_Lean_Meta_mkPure___rarg___closed__4;
lean_inc(x_128);
lean_inc(x_129);
x_131 = l_Lean_addMacroScope(x_129, x_130, x_128);
x_132 = l_Lean_SourceInfo_inhabited___closed__1;
x_133 = l___private_Lean_Elab_Do_13__mkForInYield___closed__3;
x_134 = l___private_Lean_Elab_Do_13__mkForInYield___closed__5;
x_135 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
lean_ctor_set(x_135, 2, x_131);
lean_ctor_set(x_135, 3, x_134);
x_136 = l_Array_empty___closed__1;
x_137 = lean_array_push(x_136, x_135);
x_138 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__11;
x_139 = l_Lean_addMacroScope(x_129, x_138, x_128);
x_140 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__10;
x_141 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__13;
x_142 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_142, 0, x_132);
lean_ctor_set(x_142, 1, x_140);
lean_ctor_set(x_142, 2, x_139);
lean_ctor_set(x_142, 3, x_141);
x_143 = lean_array_push(x_136, x_142);
x_144 = lean_array_push(x_136, x_126);
x_145 = l_Lean_nullKind___closed__2;
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = lean_array_push(x_143, x_146);
x_148 = l_Lean_mkAppStx___closed__8;
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
x_150 = lean_array_push(x_136, x_149);
x_151 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_152 = lean_array_push(x_150, x_151);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_145);
lean_ctor_set(x_153, 1, x_152);
x_154 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_155 = lean_array_push(x_154, x_153);
x_156 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_157 = lean_array_push(x_155, x_156);
x_158 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
x_160 = lean_array_push(x_136, x_159);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_145);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_array_push(x_137, x_161);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_148);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_127);
return x_164;
}
}
default: 
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_165 = lean_ctor_get(x_5, 0);
lean_inc(x_165);
lean_dec(x_5);
lean_inc(x_3);
x_166 = l_Lean_Elab_Term_Do_ToTerm_mkUVarTuple(x_1, x_2, x_3, x_4);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = l_Lean_mkIdentFrom(x_1, x_165);
x_170 = l_Lean_mkAppStx___closed__9;
x_171 = lean_array_push(x_170, x_169);
x_172 = lean_array_push(x_171, x_167);
lean_inc(x_3);
x_173 = l___private_Lean_Elab_Do_12__mkTuple(x_1, x_172, x_3, x_168);
lean_dec(x_172);
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_175 = lean_ctor_get(x_173, 0);
x_176 = lean_ctor_get(x_3, 2);
lean_inc(x_176);
x_177 = lean_ctor_get(x_3, 1);
lean_inc(x_177);
lean_dec(x_3);
x_178 = l_Lean_Meta_mkPure___rarg___closed__4;
lean_inc(x_176);
lean_inc(x_177);
x_179 = l_Lean_addMacroScope(x_177, x_178, x_176);
x_180 = l_Lean_SourceInfo_inhabited___closed__1;
x_181 = l___private_Lean_Elab_Do_13__mkForInYield___closed__3;
x_182 = l___private_Lean_Elab_Do_13__mkForInYield___closed__5;
x_183 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
lean_ctor_set(x_183, 2, x_179);
lean_ctor_set(x_183, 3, x_182);
x_184 = l_Array_empty___closed__1;
x_185 = lean_array_push(x_184, x_183);
x_186 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__11;
x_187 = l_Lean_addMacroScope(x_177, x_186, x_176);
x_188 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__10;
x_189 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__13;
x_190 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_190, 0, x_180);
lean_ctor_set(x_190, 1, x_188);
lean_ctor_set(x_190, 2, x_187);
lean_ctor_set(x_190, 3, x_189);
x_191 = lean_array_push(x_184, x_190);
x_192 = lean_array_push(x_184, x_175);
x_193 = l_Lean_nullKind___closed__2;
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
x_195 = lean_array_push(x_191, x_194);
x_196 = l_Lean_mkAppStx___closed__8;
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
x_198 = lean_array_push(x_184, x_197);
x_199 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_200 = lean_array_push(x_198, x_199);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_193);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_203 = lean_array_push(x_202, x_201);
x_204 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_205 = lean_array_push(x_203, x_204);
x_206 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_205);
x_208 = lean_array_push(x_184, x_207);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_193);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_array_push(x_185, x_209);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_196);
lean_ctor_set(x_211, 1, x_210);
lean_ctor_set(x_173, 0, x_211);
return x_173;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_212 = lean_ctor_get(x_173, 0);
x_213 = lean_ctor_get(x_173, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_173);
x_214 = lean_ctor_get(x_3, 2);
lean_inc(x_214);
x_215 = lean_ctor_get(x_3, 1);
lean_inc(x_215);
lean_dec(x_3);
x_216 = l_Lean_Meta_mkPure___rarg___closed__4;
lean_inc(x_214);
lean_inc(x_215);
x_217 = l_Lean_addMacroScope(x_215, x_216, x_214);
x_218 = l_Lean_SourceInfo_inhabited___closed__1;
x_219 = l___private_Lean_Elab_Do_13__mkForInYield___closed__3;
x_220 = l___private_Lean_Elab_Do_13__mkForInYield___closed__5;
x_221 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_219);
lean_ctor_set(x_221, 2, x_217);
lean_ctor_set(x_221, 3, x_220);
x_222 = l_Array_empty___closed__1;
x_223 = lean_array_push(x_222, x_221);
x_224 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__11;
x_225 = l_Lean_addMacroScope(x_215, x_224, x_214);
x_226 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__10;
x_227 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__13;
x_228 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_228, 0, x_218);
lean_ctor_set(x_228, 1, x_226);
lean_ctor_set(x_228, 2, x_225);
lean_ctor_set(x_228, 3, x_227);
x_229 = lean_array_push(x_222, x_228);
x_230 = lean_array_push(x_222, x_212);
x_231 = l_Lean_nullKind___closed__2;
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
x_233 = lean_array_push(x_229, x_232);
x_234 = l_Lean_mkAppStx___closed__8;
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_233);
x_236 = lean_array_push(x_222, x_235);
x_237 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_238 = lean_array_push(x_236, x_237);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_231);
lean_ctor_set(x_239, 1, x_238);
x_240 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_241 = lean_array_push(x_240, x_239);
x_242 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_243 = lean_array_push(x_241, x_242);
x_244 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_243);
x_246 = lean_array_push(x_222, x_245);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_231);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_array_push(x_223, x_247);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_234);
lean_ctor_set(x_249, 1, x_248);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_213);
return x_250;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_Do_ToTerm_breakToTermCore(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_Syntax_copyInfo(x_7, x_1);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = l_Lean_Syntax_copyInfo(x_9, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_breakToTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_Do_ToTerm_breakToTerm(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doDbgTrace");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doAssert");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HasBind.bind");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__5;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Meta_assert___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assert!");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__9;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__10;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("dbgTrace");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("dbgTrace!");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__14;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__15;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTermCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_5 = l_Lean_Syntax_getKind(x_1);
x_6 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__2;
x_7 = lean_name_eq(x_5, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_4, x_8);
if (x_7 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__4;
x_12 = lean_name_eq(x_5, x_11);
lean_dec(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_13 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
x_14 = l_Lean_addMacroScope(x_10, x_13, x_4);
x_15 = l_Lean_SourceInfo_inhabited___closed__1;
x_16 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__7;
x_17 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__9;
x_18 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_17);
x_19 = l_Array_empty___closed__1;
x_20 = lean_array_push(x_19, x_18);
x_21 = lean_array_push(x_19, x_1);
x_22 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__18;
x_23 = lean_array_push(x_22, x_2);
x_24 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_array_push(x_19, x_25);
x_27 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_28 = lean_array_push(x_26, x_27);
x_29 = l_Lean_nullKind___closed__2;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_32 = lean_array_push(x_31, x_30);
x_33 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_34 = lean_array_push(x_32, x_33);
x_35 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_array_push(x_21, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_array_push(x_20, x_38);
x_40 = l_Lean_mkAppStx___closed__8;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_9);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_10);
lean_dec(x_4);
x_43 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_44 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__11;
x_45 = lean_array_push(x_44, x_43);
x_46 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_47 = lean_array_push(x_45, x_46);
x_48 = lean_array_push(x_47, x_2);
x_49 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__8;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_9);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_53 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__16;
x_54 = lean_array_push(x_53, x_52);
x_55 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_56 = lean_array_push(x_54, x_55);
x_57 = lean_array_push(x_56, x_2);
x_58 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__13;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_9);
return x_60;
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_actionToTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_5 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore(x_1, x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_Syntax_copyInfo(x_7, x_1);
lean_dec(x_1);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = l_Lean_Syntax_copyInfo(x_9, x_1);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doLet");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doLetRec");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doLetArrow");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doHave");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("WIP ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_mkFreshJP___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_Do_mkFreshJP___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__10;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Meta_Match_processInaccessibleAsCtor___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__15;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__14;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__17;
x_2 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("letrec");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTermCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_6 = l_Lean_Syntax_getKind(x_1);
x_7 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__2;
x_8 = lean_name_eq(x_6, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
if (x_8 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
lean_dec(x_13);
lean_inc(x_5);
lean_inc(x_12);
lean_ctor_set(x_4, 2, x_5);
x_14 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__4;
x_15 = lean_name_eq(x_6, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__6;
x_17 = lean_name_eq(x_6, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_18 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__8;
x_19 = lean_name_eq(x_6, x_18);
lean_dec(x_6);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__5;
x_21 = l_Lean_Macro_throwError___rarg(x_1, x_20, x_4, x_10);
lean_dec(x_4);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_box(0);
x_23 = 0;
x_24 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_25 = l_Lean_Syntax_formatStxAux___main(x_22, x_23, x_24, x_1);
x_26 = lean_box(0);
x_27 = l_Lean_Format_pretty(x_25, x_26);
x_28 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__9;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_Macro_throwError___rarg(x_1, x_29, x_4, x_10);
lean_dec(x_4);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_6);
x_31 = l_Lean_Syntax_getArg(x_1, x_9);
lean_inc(x_31);
x_32 = l_Lean_Syntax_getKind(x_31);
x_33 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
x_34 = lean_name_eq(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__4;
x_36 = lean_name_eq(x_32, x_35);
lean_dec(x_32);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_37 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__5;
x_38 = l_Lean_Macro_throwError___rarg(x_1, x_37, x_4, x_10);
lean_dec(x_4);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_1);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_Syntax_getArg(x_31, x_39);
x_41 = lean_unsigned_to_nat(2u);
x_42 = l_Lean_Syntax_getArg(x_31, x_41);
x_43 = lean_unsigned_to_nat(3u);
x_44 = l_Lean_Syntax_getArg(x_31, x_43);
x_45 = l_Lean_Syntax_isNone(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_46 = l_Lean_Syntax_getArg(x_44, x_9);
lean_dec(x_44);
x_47 = l_Lean_Elab_Term_Do_mkFreshJP___closed__4;
lean_inc(x_5);
lean_inc(x_12);
x_48 = l_Lean_addMacroScope(x_12, x_47, x_5);
x_49 = lean_box(0);
x_50 = l_Lean_SourceInfo_inhabited___closed__1;
x_51 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__11;
x_52 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_48);
lean_ctor_set(x_52, 3, x_49);
lean_inc(x_52);
x_53 = l_Lean_Elab_Term_Do_ToTerm_returnToTerm(x_31, x_52, x_3, x_4, x_10);
lean_dec(x_31);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
lean_inc(x_5);
lean_inc(x_12);
x_57 = l_Lean_addMacroScope(x_12, x_56, x_5);
x_58 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__7;
x_59 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__13;
x_60 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_57);
lean_ctor_set(x_60, 3, x_59);
x_61 = l_Array_empty___closed__1;
x_62 = lean_array_push(x_61, x_60);
x_63 = lean_array_push(x_61, x_46);
x_64 = lean_array_push(x_61, x_52);
x_65 = l_Lean_nullKind___closed__2;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
x_68 = lean_array_push(x_67, x_66);
x_69 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_70 = lean_array_push(x_68, x_69);
x_71 = lean_array_push(x_70, x_55);
x_72 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_array_push(x_61, x_73);
x_75 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_76 = lean_array_push(x_74, x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_65);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_79 = lean_array_push(x_78, x_77);
x_80 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_81 = lean_array_push(x_79, x_80);
x_82 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = lean_array_push(x_63, x_83);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_65);
lean_ctor_set(x_85, 1, x_84);
lean_inc(x_62);
x_86 = lean_array_push(x_62, x_85);
x_87 = l_Lean_mkAppStx___closed__8;
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = lean_array_push(x_61, x_42);
x_90 = l_Lean_Meta_mkArrow___rarg___closed__2;
x_91 = l_Lean_addMacroScope(x_12, x_90, x_5);
x_92 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__2;
x_93 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_93, 0, x_50);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_91);
lean_ctor_set(x_93, 3, x_49);
lean_inc(x_93);
x_94 = lean_array_push(x_61, x_93);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_65);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_array_push(x_67, x_95);
x_97 = lean_array_push(x_96, x_69);
x_98 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__7;
x_99 = lean_array_push(x_98, x_93);
x_100 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__6;
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = lean_array_push(x_61, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_65);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__16;
x_105 = lean_array_push(x_104, x_103);
x_106 = lean_array_push(x_105, x_75);
x_107 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__9;
x_108 = lean_array_push(x_106, x_107);
x_109 = lean_array_push(x_61, x_40);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_65);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_array_push(x_61, x_110);
x_112 = lean_array_push(x_111, x_69);
x_113 = lean_array_push(x_112, x_2);
x_114 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__18;
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = lean_array_push(x_61, x_115);
x_117 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__13;
x_118 = lean_array_push(x_116, x_117);
x_119 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__18;
x_120 = lean_array_push(x_119, x_88);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_114);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_array_push(x_118, x_121);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_65);
lean_ctor_set(x_123, 1, x_122);
x_124 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__16;
x_125 = lean_array_push(x_124, x_123);
x_126 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__11;
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
x_128 = lean_array_push(x_108, x_127);
x_129 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__14;
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = lean_array_push(x_97, x_130);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_72);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_array_push(x_61, x_132);
x_134 = lean_array_push(x_133, x_75);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_65);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_array_push(x_78, x_135);
x_137 = lean_array_push(x_136, x_80);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_82);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_array_push(x_89, x_138);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_65);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_array_push(x_62, x_140);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_87);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_53, 0, x_142);
return x_53;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_143 = lean_ctor_get(x_53, 0);
x_144 = lean_ctor_get(x_53, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_53);
x_145 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
lean_inc(x_5);
lean_inc(x_12);
x_146 = l_Lean_addMacroScope(x_12, x_145, x_5);
x_147 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__7;
x_148 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__13;
x_149 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_149, 0, x_50);
lean_ctor_set(x_149, 1, x_147);
lean_ctor_set(x_149, 2, x_146);
lean_ctor_set(x_149, 3, x_148);
x_150 = l_Array_empty___closed__1;
x_151 = lean_array_push(x_150, x_149);
x_152 = lean_array_push(x_150, x_46);
x_153 = lean_array_push(x_150, x_52);
x_154 = l_Lean_nullKind___closed__2;
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
x_156 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
x_157 = lean_array_push(x_156, x_155);
x_158 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_159 = lean_array_push(x_157, x_158);
x_160 = lean_array_push(x_159, x_143);
x_161 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = lean_array_push(x_150, x_162);
x_164 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_165 = lean_array_push(x_163, x_164);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_154);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_168 = lean_array_push(x_167, x_166);
x_169 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_170 = lean_array_push(x_168, x_169);
x_171 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
x_173 = lean_array_push(x_152, x_172);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_154);
lean_ctor_set(x_174, 1, x_173);
lean_inc(x_151);
x_175 = lean_array_push(x_151, x_174);
x_176 = l_Lean_mkAppStx___closed__8;
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
x_178 = lean_array_push(x_150, x_42);
x_179 = l_Lean_Meta_mkArrow___rarg___closed__2;
x_180 = l_Lean_addMacroScope(x_12, x_179, x_5);
x_181 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__2;
x_182 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_182, 0, x_50);
lean_ctor_set(x_182, 1, x_181);
lean_ctor_set(x_182, 2, x_180);
lean_ctor_set(x_182, 3, x_49);
lean_inc(x_182);
x_183 = lean_array_push(x_150, x_182);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_154);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_array_push(x_156, x_184);
x_186 = lean_array_push(x_185, x_158);
x_187 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__7;
x_188 = lean_array_push(x_187, x_182);
x_189 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__6;
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
x_191 = lean_array_push(x_150, x_190);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_154);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__16;
x_194 = lean_array_push(x_193, x_192);
x_195 = lean_array_push(x_194, x_164);
x_196 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__9;
x_197 = lean_array_push(x_195, x_196);
x_198 = lean_array_push(x_150, x_40);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_154);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_array_push(x_150, x_199);
x_201 = lean_array_push(x_200, x_158);
x_202 = lean_array_push(x_201, x_2);
x_203 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__18;
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_202);
x_205 = lean_array_push(x_150, x_204);
x_206 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__13;
x_207 = lean_array_push(x_205, x_206);
x_208 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__18;
x_209 = lean_array_push(x_208, x_177);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_203);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_array_push(x_207, x_210);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_154);
lean_ctor_set(x_212, 1, x_211);
x_213 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__16;
x_214 = lean_array_push(x_213, x_212);
x_215 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__11;
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_214);
x_217 = lean_array_push(x_197, x_216);
x_218 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__14;
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_217);
x_220 = lean_array_push(x_186, x_219);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_161);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_array_push(x_150, x_221);
x_223 = lean_array_push(x_222, x_164);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_154);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_array_push(x_167, x_224);
x_226 = lean_array_push(x_225, x_169);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_171);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_array_push(x_178, x_227);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_154);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_array_push(x_151, x_229);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_176);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_144);
return x_232;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_44);
lean_dec(x_31);
lean_dec(x_4);
lean_dec(x_3);
x_233 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
lean_inc(x_5);
lean_inc(x_12);
x_234 = l_Lean_addMacroScope(x_12, x_233, x_5);
x_235 = lean_box(0);
x_236 = l_Lean_SourceInfo_inhabited___closed__1;
x_237 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__7;
x_238 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__9;
x_239 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
lean_ctor_set(x_239, 2, x_234);
lean_ctor_set(x_239, 3, x_238);
x_240 = l_Array_empty___closed__1;
x_241 = lean_array_push(x_240, x_239);
x_242 = lean_array_push(x_240, x_42);
x_243 = l_Lean_Meta_mkArrow___rarg___closed__2;
x_244 = l_Lean_addMacroScope(x_12, x_243, x_5);
x_245 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__2;
x_246 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_246, 0, x_236);
lean_ctor_set(x_246, 1, x_245);
lean_ctor_set(x_246, 2, x_244);
lean_ctor_set(x_246, 3, x_235);
lean_inc(x_246);
x_247 = lean_array_push(x_240, x_246);
x_248 = l_Lean_nullKind___closed__2;
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_250 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
x_251 = lean_array_push(x_250, x_249);
x_252 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_253 = lean_array_push(x_251, x_252);
x_254 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__7;
x_255 = lean_array_push(x_254, x_246);
x_256 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__6;
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_255);
x_258 = lean_array_push(x_240, x_257);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_248);
lean_ctor_set(x_259, 1, x_258);
x_260 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__16;
x_261 = lean_array_push(x_260, x_259);
x_262 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_263 = lean_array_push(x_261, x_262);
x_264 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__9;
x_265 = lean_array_push(x_263, x_264);
x_266 = lean_array_push(x_240, x_40);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_248);
lean_ctor_set(x_267, 1, x_266);
x_268 = lean_array_push(x_240, x_267);
x_269 = lean_array_push(x_268, x_252);
x_270 = lean_array_push(x_269, x_2);
x_271 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__18;
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_270);
x_273 = lean_array_push(x_240, x_272);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_248);
lean_ctor_set(x_274, 1, x_273);
x_275 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__16;
x_276 = lean_array_push(x_275, x_274);
x_277 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__11;
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_276);
x_279 = lean_array_push(x_265, x_278);
x_280 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__14;
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_279);
x_282 = lean_array_push(x_253, x_281);
x_283 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_282);
x_285 = lean_array_push(x_240, x_284);
x_286 = lean_array_push(x_285, x_262);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_248);
lean_ctor_set(x_287, 1, x_286);
x_288 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_289 = lean_array_push(x_288, x_287);
x_290 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_291 = lean_array_push(x_289, x_290);
x_292 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_291);
x_294 = lean_array_push(x_242, x_293);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_248);
lean_ctor_set(x_295, 1, x_294);
x_296 = lean_array_push(x_241, x_295);
x_297 = l_Lean_mkAppStx___closed__8;
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_296);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_10);
return x_299;
}
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_300 = lean_unsigned_to_nat(0u);
x_301 = l_Lean_Syntax_getArg(x_31, x_300);
x_302 = l_Lean_Syntax_getArg(x_31, x_9);
x_303 = l_Lean_Elab_Term_expandOptType(x_31, x_302);
lean_dec(x_302);
x_304 = lean_unsigned_to_nat(3u);
x_305 = l_Lean_Syntax_getArg(x_31, x_304);
lean_dec(x_31);
x_306 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
x_307 = l_Lean_addMacroScope(x_12, x_306, x_5);
x_308 = l_Lean_SourceInfo_inhabited___closed__1;
x_309 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__7;
x_310 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__9;
x_311 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_309);
lean_ctor_set(x_311, 2, x_307);
lean_ctor_set(x_311, 3, x_310);
x_312 = l_Array_empty___closed__1;
x_313 = lean_array_push(x_312, x_311);
x_314 = lean_array_push(x_312, x_305);
x_315 = lean_array_push(x_312, x_301);
x_316 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__26;
x_317 = lean_array_push(x_316, x_303);
x_318 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__24;
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_317);
x_320 = lean_array_push(x_312, x_319);
x_321 = l_Lean_nullKind___closed__2;
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_320);
x_323 = lean_array_push(x_315, x_322);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_321);
lean_ctor_set(x_324, 1, x_323);
x_325 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_326 = lean_array_push(x_325, x_324);
x_327 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_328 = lean_array_push(x_326, x_327);
x_329 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_328);
x_331 = lean_array_push(x_312, x_330);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_321);
lean_ctor_set(x_332, 1, x_331);
x_333 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
x_334 = lean_array_push(x_333, x_332);
x_335 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_336 = lean_array_push(x_334, x_335);
x_337 = lean_array_push(x_336, x_2);
x_338 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_337);
x_340 = lean_array_push(x_312, x_339);
x_341 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_342 = lean_array_push(x_340, x_341);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_321);
lean_ctor_set(x_343, 1, x_342);
x_344 = lean_array_push(x_325, x_343);
x_345 = lean_array_push(x_344, x_327);
x_346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_346, 0, x_329);
lean_ctor_set(x_346, 1, x_345);
x_347 = lean_array_push(x_314, x_346);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_321);
lean_ctor_set(x_348, 1, x_347);
x_349 = lean_array_push(x_313, x_348);
x_350 = l_Lean_mkAppStx___closed__8;
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_349);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_10);
return x_352;
}
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_4);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_353 = lean_unsigned_to_nat(0u);
x_354 = l_Lean_Syntax_getArg(x_1, x_353);
x_355 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_356 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_357 = lean_array_push(x_356, x_354);
x_358 = lean_array_push(x_357, x_355);
x_359 = l_Lean_mkOptionalNode___closed__1;
x_360 = lean_array_push(x_358, x_359);
x_361 = lean_array_push(x_360, x_2);
x_362 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__20;
x_363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_361);
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_10);
return x_364;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
x_365 = lean_ctor_get(x_4, 0);
x_366 = lean_ctor_get(x_4, 1);
x_367 = lean_ctor_get(x_4, 3);
x_368 = lean_ctor_get(x_4, 4);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_4);
lean_inc(x_5);
lean_inc(x_366);
x_369 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_369, 0, x_365);
lean_ctor_set(x_369, 1, x_366);
lean_ctor_set(x_369, 2, x_5);
lean_ctor_set(x_369, 3, x_367);
lean_ctor_set(x_369, 4, x_368);
x_370 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__4;
x_371 = lean_name_eq(x_6, x_370);
if (x_371 == 0)
{
lean_object* x_372; uint8_t x_373; 
x_372 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__6;
x_373 = lean_name_eq(x_6, x_372);
if (x_373 == 0)
{
lean_object* x_374; uint8_t x_375; 
lean_dec(x_366);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_374 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__8;
x_375 = lean_name_eq(x_6, x_374);
lean_dec(x_6);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; 
x_376 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__5;
x_377 = l_Lean_Macro_throwError___rarg(x_1, x_376, x_369, x_10);
lean_dec(x_369);
return x_377;
}
else
{
lean_object* x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_378 = lean_box(0);
x_379 = 0;
x_380 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_381 = l_Lean_Syntax_formatStxAux___main(x_378, x_379, x_380, x_1);
x_382 = lean_box(0);
x_383 = l_Lean_Format_pretty(x_381, x_382);
x_384 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__9;
x_385 = lean_string_append(x_384, x_383);
lean_dec(x_383);
x_386 = l_Lean_Macro_throwError___rarg(x_1, x_385, x_369, x_10);
lean_dec(x_369);
return x_386;
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; 
lean_dec(x_6);
x_387 = l_Lean_Syntax_getArg(x_1, x_9);
lean_inc(x_387);
x_388 = l_Lean_Syntax_getKind(x_387);
x_389 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
x_390 = lean_name_eq(x_388, x_389);
if (x_390 == 0)
{
lean_object* x_391; uint8_t x_392; 
x_391 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__4;
x_392 = lean_name_eq(x_388, x_391);
lean_dec(x_388);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; 
lean_dec(x_387);
lean_dec(x_366);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_393 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__5;
x_394 = l_Lean_Macro_throwError___rarg(x_1, x_393, x_369, x_10);
lean_dec(x_369);
return x_394;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; 
lean_dec(x_1);
x_395 = lean_unsigned_to_nat(0u);
x_396 = l_Lean_Syntax_getArg(x_387, x_395);
x_397 = lean_unsigned_to_nat(2u);
x_398 = l_Lean_Syntax_getArg(x_387, x_397);
x_399 = lean_unsigned_to_nat(3u);
x_400 = l_Lean_Syntax_getArg(x_387, x_399);
x_401 = l_Lean_Syntax_isNone(x_400);
if (x_401 == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_402 = l_Lean_Syntax_getArg(x_400, x_9);
lean_dec(x_400);
x_403 = l_Lean_Elab_Term_Do_mkFreshJP___closed__4;
lean_inc(x_5);
lean_inc(x_366);
x_404 = l_Lean_addMacroScope(x_366, x_403, x_5);
x_405 = lean_box(0);
x_406 = l_Lean_SourceInfo_inhabited___closed__1;
x_407 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__11;
x_408 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
lean_ctor_set(x_408, 2, x_404);
lean_ctor_set(x_408, 3, x_405);
lean_inc(x_408);
x_409 = l_Lean_Elab_Term_Do_ToTerm_returnToTerm(x_387, x_408, x_3, x_369, x_10);
lean_dec(x_387);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_412 = x_409;
} else {
 lean_dec_ref(x_409);
 x_412 = lean_box(0);
}
x_413 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
lean_inc(x_5);
lean_inc(x_366);
x_414 = l_Lean_addMacroScope(x_366, x_413, x_5);
x_415 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__7;
x_416 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__13;
x_417 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_417, 0, x_406);
lean_ctor_set(x_417, 1, x_415);
lean_ctor_set(x_417, 2, x_414);
lean_ctor_set(x_417, 3, x_416);
x_418 = l_Array_empty___closed__1;
x_419 = lean_array_push(x_418, x_417);
x_420 = lean_array_push(x_418, x_402);
x_421 = lean_array_push(x_418, x_408);
x_422 = l_Lean_nullKind___closed__2;
x_423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_421);
x_424 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
x_425 = lean_array_push(x_424, x_423);
x_426 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_427 = lean_array_push(x_425, x_426);
x_428 = lean_array_push(x_427, x_410);
x_429 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
x_430 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_428);
x_431 = lean_array_push(x_418, x_430);
x_432 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_433 = lean_array_push(x_431, x_432);
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_422);
lean_ctor_set(x_434, 1, x_433);
x_435 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_436 = lean_array_push(x_435, x_434);
x_437 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_438 = lean_array_push(x_436, x_437);
x_439 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_438);
x_441 = lean_array_push(x_420, x_440);
x_442 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_442, 0, x_422);
lean_ctor_set(x_442, 1, x_441);
lean_inc(x_419);
x_443 = lean_array_push(x_419, x_442);
x_444 = l_Lean_mkAppStx___closed__8;
x_445 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_443);
x_446 = lean_array_push(x_418, x_398);
x_447 = l_Lean_Meta_mkArrow___rarg___closed__2;
x_448 = l_Lean_addMacroScope(x_366, x_447, x_5);
x_449 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__2;
x_450 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_450, 0, x_406);
lean_ctor_set(x_450, 1, x_449);
lean_ctor_set(x_450, 2, x_448);
lean_ctor_set(x_450, 3, x_405);
lean_inc(x_450);
x_451 = lean_array_push(x_418, x_450);
x_452 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_452, 0, x_422);
lean_ctor_set(x_452, 1, x_451);
x_453 = lean_array_push(x_424, x_452);
x_454 = lean_array_push(x_453, x_426);
x_455 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__7;
x_456 = lean_array_push(x_455, x_450);
x_457 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__6;
x_458 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_458, 1, x_456);
x_459 = lean_array_push(x_418, x_458);
x_460 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_460, 0, x_422);
lean_ctor_set(x_460, 1, x_459);
x_461 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__16;
x_462 = lean_array_push(x_461, x_460);
x_463 = lean_array_push(x_462, x_432);
x_464 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__9;
x_465 = lean_array_push(x_463, x_464);
x_466 = lean_array_push(x_418, x_396);
x_467 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_467, 0, x_422);
lean_ctor_set(x_467, 1, x_466);
x_468 = lean_array_push(x_418, x_467);
x_469 = lean_array_push(x_468, x_426);
x_470 = lean_array_push(x_469, x_2);
x_471 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__18;
x_472 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_470);
x_473 = lean_array_push(x_418, x_472);
x_474 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__13;
x_475 = lean_array_push(x_473, x_474);
x_476 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__18;
x_477 = lean_array_push(x_476, x_445);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_471);
lean_ctor_set(x_478, 1, x_477);
x_479 = lean_array_push(x_475, x_478);
x_480 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_480, 0, x_422);
lean_ctor_set(x_480, 1, x_479);
x_481 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__16;
x_482 = lean_array_push(x_481, x_480);
x_483 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__11;
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_482);
x_485 = lean_array_push(x_465, x_484);
x_486 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__14;
x_487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_485);
x_488 = lean_array_push(x_454, x_487);
x_489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_489, 0, x_429);
lean_ctor_set(x_489, 1, x_488);
x_490 = lean_array_push(x_418, x_489);
x_491 = lean_array_push(x_490, x_432);
x_492 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_492, 0, x_422);
lean_ctor_set(x_492, 1, x_491);
x_493 = lean_array_push(x_435, x_492);
x_494 = lean_array_push(x_493, x_437);
x_495 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_495, 0, x_439);
lean_ctor_set(x_495, 1, x_494);
x_496 = lean_array_push(x_446, x_495);
x_497 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_497, 0, x_422);
lean_ctor_set(x_497, 1, x_496);
x_498 = lean_array_push(x_419, x_497);
x_499 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_499, 0, x_444);
lean_ctor_set(x_499, 1, x_498);
if (lean_is_scalar(x_412)) {
 x_500 = lean_alloc_ctor(0, 2, 0);
} else {
 x_500 = x_412;
}
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_411);
return x_500;
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
lean_dec(x_400);
lean_dec(x_387);
lean_dec(x_369);
lean_dec(x_3);
x_501 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
lean_inc(x_5);
lean_inc(x_366);
x_502 = l_Lean_addMacroScope(x_366, x_501, x_5);
x_503 = lean_box(0);
x_504 = l_Lean_SourceInfo_inhabited___closed__1;
x_505 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__7;
x_506 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__9;
x_507 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_507, 0, x_504);
lean_ctor_set(x_507, 1, x_505);
lean_ctor_set(x_507, 2, x_502);
lean_ctor_set(x_507, 3, x_506);
x_508 = l_Array_empty___closed__1;
x_509 = lean_array_push(x_508, x_507);
x_510 = lean_array_push(x_508, x_398);
x_511 = l_Lean_Meta_mkArrow___rarg___closed__2;
x_512 = l_Lean_addMacroScope(x_366, x_511, x_5);
x_513 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__2;
x_514 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_514, 0, x_504);
lean_ctor_set(x_514, 1, x_513);
lean_ctor_set(x_514, 2, x_512);
lean_ctor_set(x_514, 3, x_503);
lean_inc(x_514);
x_515 = lean_array_push(x_508, x_514);
x_516 = l_Lean_nullKind___closed__2;
x_517 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_517, 0, x_516);
lean_ctor_set(x_517, 1, x_515);
x_518 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
x_519 = lean_array_push(x_518, x_517);
x_520 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_521 = lean_array_push(x_519, x_520);
x_522 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__7;
x_523 = lean_array_push(x_522, x_514);
x_524 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__6;
x_525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_525, 0, x_524);
lean_ctor_set(x_525, 1, x_523);
x_526 = lean_array_push(x_508, x_525);
x_527 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_527, 0, x_516);
lean_ctor_set(x_527, 1, x_526);
x_528 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__16;
x_529 = lean_array_push(x_528, x_527);
x_530 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_531 = lean_array_push(x_529, x_530);
x_532 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__9;
x_533 = lean_array_push(x_531, x_532);
x_534 = lean_array_push(x_508, x_396);
x_535 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_535, 0, x_516);
lean_ctor_set(x_535, 1, x_534);
x_536 = lean_array_push(x_508, x_535);
x_537 = lean_array_push(x_536, x_520);
x_538 = lean_array_push(x_537, x_2);
x_539 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__18;
x_540 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_538);
x_541 = lean_array_push(x_508, x_540);
x_542 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_542, 0, x_516);
lean_ctor_set(x_542, 1, x_541);
x_543 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__16;
x_544 = lean_array_push(x_543, x_542);
x_545 = l___private_Lean_Elab_Binders_12__expandFunBindersAux___main___closed__11;
x_546 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_546, 0, x_545);
lean_ctor_set(x_546, 1, x_544);
x_547 = lean_array_push(x_533, x_546);
x_548 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__14;
x_549 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_549, 0, x_548);
lean_ctor_set(x_549, 1, x_547);
x_550 = lean_array_push(x_521, x_549);
x_551 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_551);
lean_ctor_set(x_552, 1, x_550);
x_553 = lean_array_push(x_508, x_552);
x_554 = lean_array_push(x_553, x_530);
x_555 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_555, 0, x_516);
lean_ctor_set(x_555, 1, x_554);
x_556 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_557 = lean_array_push(x_556, x_555);
x_558 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_559 = lean_array_push(x_557, x_558);
x_560 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_561 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_561, 0, x_560);
lean_ctor_set(x_561, 1, x_559);
x_562 = lean_array_push(x_510, x_561);
x_563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_563, 0, x_516);
lean_ctor_set(x_563, 1, x_562);
x_564 = lean_array_push(x_509, x_563);
x_565 = l_Lean_mkAppStx___closed__8;
x_566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_564);
x_567 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_10);
return x_567;
}
}
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
lean_dec(x_388);
lean_dec(x_369);
lean_dec(x_3);
lean_dec(x_1);
x_568 = lean_unsigned_to_nat(0u);
x_569 = l_Lean_Syntax_getArg(x_387, x_568);
x_570 = l_Lean_Syntax_getArg(x_387, x_9);
x_571 = l_Lean_Elab_Term_expandOptType(x_387, x_570);
lean_dec(x_570);
x_572 = lean_unsigned_to_nat(3u);
x_573 = l_Lean_Syntax_getArg(x_387, x_572);
lean_dec(x_387);
x_574 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
x_575 = l_Lean_addMacroScope(x_366, x_574, x_5);
x_576 = l_Lean_SourceInfo_inhabited___closed__1;
x_577 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__7;
x_578 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__9;
x_579 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_579, 0, x_576);
lean_ctor_set(x_579, 1, x_577);
lean_ctor_set(x_579, 2, x_575);
lean_ctor_set(x_579, 3, x_578);
x_580 = l_Array_empty___closed__1;
x_581 = lean_array_push(x_580, x_579);
x_582 = lean_array_push(x_580, x_573);
x_583 = lean_array_push(x_580, x_569);
x_584 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__26;
x_585 = lean_array_push(x_584, x_571);
x_586 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__24;
x_587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_587, 0, x_586);
lean_ctor_set(x_587, 1, x_585);
x_588 = lean_array_push(x_580, x_587);
x_589 = l_Lean_nullKind___closed__2;
x_590 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_588);
x_591 = lean_array_push(x_583, x_590);
x_592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_592, 0, x_589);
lean_ctor_set(x_592, 1, x_591);
x_593 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__22;
x_594 = lean_array_push(x_593, x_592);
x_595 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__34;
x_596 = lean_array_push(x_594, x_595);
x_597 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__20;
x_598 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_598, 0, x_597);
lean_ctor_set(x_598, 1, x_596);
x_599 = lean_array_push(x_580, x_598);
x_600 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_600, 0, x_589);
lean_ctor_set(x_600, 1, x_599);
x_601 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
x_602 = lean_array_push(x_601, x_600);
x_603 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_604 = lean_array_push(x_602, x_603);
x_605 = lean_array_push(x_604, x_2);
x_606 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
x_607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_607, 0, x_606);
lean_ctor_set(x_607, 1, x_605);
x_608 = lean_array_push(x_580, x_607);
x_609 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_610 = lean_array_push(x_608, x_609);
x_611 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_611, 0, x_589);
lean_ctor_set(x_611, 1, x_610);
x_612 = lean_array_push(x_593, x_611);
x_613 = lean_array_push(x_612, x_595);
x_614 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_614, 0, x_597);
lean_ctor_set(x_614, 1, x_613);
x_615 = lean_array_push(x_582, x_614);
x_616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_616, 0, x_589);
lean_ctor_set(x_616, 1, x_615);
x_617 = lean_array_push(x_581, x_616);
x_618 = l_Lean_mkAppStx___closed__8;
x_619 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_619, 0, x_618);
lean_ctor_set(x_619, 1, x_617);
x_620 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_620, 0, x_619);
lean_ctor_set(x_620, 1, x_10);
return x_620;
}
}
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
lean_dec(x_369);
lean_dec(x_366);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_621 = lean_unsigned_to_nat(0u);
x_622 = l_Lean_Syntax_getArg(x_1, x_621);
x_623 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_624 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_625 = lean_array_push(x_624, x_622);
x_626 = lean_array_push(x_625, x_623);
x_627 = l_Lean_mkOptionalNode___closed__1;
x_628 = lean_array_push(x_626, x_627);
x_629 = lean_array_push(x_628, x_2);
x_630 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__20;
x_631 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_631, 0, x_630);
lean_ctor_set(x_631, 1, x_629);
x_632 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_10);
return x_632;
}
}
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_633 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_634 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_635 = lean_array_push(x_634, x_633);
x_636 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_637 = lean_array_push(x_635, x_636);
x_638 = lean_array_push(x_637, x_2);
x_639 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_639);
lean_ctor_set(x_640, 1, x_638);
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_10);
return x_641;
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_declToTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_Syntax_copyInfo(x_8, x_1);
lean_dec(x_1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = l_Lean_Syntax_copyInfo(x_10, x_1);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doReassign");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doReassignArrow");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected kind of 'do' reassignment");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ensureTypeOf!");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__6;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid reassignment");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__9;
x_2 = l_Lean_SourceInfo_inhabited___closed__1;
x_3 = l_Lean_mkStxStrLit(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_5 = l_Lean_Syntax_getKind(x_1);
x_6 = l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__2;
x_7 = lean_name_eq(x_5, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_4, x_8);
if (x_7 == 0)
{
uint8_t x_10; 
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_3, 2);
lean_dec(x_11);
lean_ctor_set(x_3, 2, x_4);
x_12 = l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__4;
x_13 = lean_name_eq(x_5, x_12);
lean_dec(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__5;
x_15 = l_Lean_Macro_throwError___rarg(x_1, x_14, x_3, x_9);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_box(0);
x_17 = 0;
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_19 = l_Lean_Syntax_formatStxAux___main(x_16, x_17, x_18, x_1);
x_20 = lean_box(0);
x_21 = l_Lean_Format_pretty(x_19, x_20);
x_22 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__9;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lean_Macro_throwError___rarg(x_1, x_23, x_3, x_9);
lean_dec(x_3);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
x_27 = lean_ctor_get(x_3, 3);
x_28 = lean_ctor_get(x_3, 4);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_4);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 4, x_28);
x_30 = l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__4;
x_31 = lean_name_eq(x_5, x_30);
lean_dec(x_5);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__5;
x_33 = l_Lean_Macro_throwError___rarg(x_1, x_32, x_29, x_9);
lean_dec(x_29);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_box(0);
x_35 = 0;
x_36 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_37 = l_Lean_Syntax_formatStxAux___main(x_34, x_35, x_36, x_1);
x_38 = lean_box(0);
x_39 = l_Lean_Format_pretty(x_37, x_38);
x_40 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__9;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lean_Macro_throwError___rarg(x_1, x_41, x_29, x_9);
lean_dec(x_29);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l_Lean_Syntax_getArg(x_1, x_43);
lean_dec(x_1);
lean_inc(x_44);
x_45 = l_Lean_Syntax_getKind(x_44);
x_46 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__8;
x_47 = lean_name_eq(x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_48 = l_Lean_mkOptionalNode___closed__2;
x_49 = lean_array_push(x_48, x_44);
x_50 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__6;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_53 = lean_array_push(x_52, x_51);
x_54 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_55 = lean_array_push(x_53, x_54);
x_56 = lean_array_push(x_55, x_2);
x_57 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_9);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_60 = l_Lean_Syntax_getArg(x_44, x_43);
x_61 = lean_unsigned_to_nat(4u);
x_62 = l_Lean_Syntax_getArg(x_44, x_61);
x_63 = l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__8;
x_64 = lean_array_push(x_63, x_60);
x_65 = l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__10;
x_66 = lean_array_push(x_64, x_65);
x_67 = lean_array_push(x_66, x_62);
x_68 = l___regBuiltin_Lean_Elab_Term_elabEnsureTypeOf___closed__2;
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = l_Lean_Syntax_setArg(x_44, x_61, x_69);
x_71 = l_Lean_mkOptionalNode___closed__2;
x_72 = lean_array_push(x_71, x_70);
x_73 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__6;
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_76 = lean_array_push(x_75, x_74);
x_77 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_78 = lean_array_push(x_76, x_77);
x_79 = lean_array_push(x_78, x_2);
x_80 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_9);
return x_82;
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_reassignToTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_Syntax_copyInfo(x_7, x_1);
lean_dec(x_1);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = l_Lean_Syntax_copyInfo(x_9, x_1);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_mkIte___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkIte(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__12;
x_7 = l_Lean_mkAtomFrom(x_1, x_6);
x_8 = l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__25;
x_9 = l_Lean_mkAtomFrom(x_1, x_8);
x_10 = l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__27;
x_11 = l_Lean_mkAtomFrom(x_1, x_10);
x_12 = l_Lean_Elab_Term_Do_ToTerm_mkIte___closed__1;
x_13 = lean_array_push(x_12, x_7);
x_14 = lean_array_push(x_13, x_2);
x_15 = lean_array_push(x_14, x_3);
x_16 = lean_array_push(x_15, x_9);
x_17 = lean_array_push(x_16, x_4);
x_18 = lean_array_push(x_17, x_11);
x_19 = lean_array_push(x_18, x_5);
x_20 = l___private_Lean_Elab_Quotation_6__compileStxMatch___main___closed__13;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkIte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_Do_ToTerm_mkIte(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("typeOf!");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_9 = x_3;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_array_fget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_fset(x_3, x_2, x_12);
x_14 = x_11;
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_19 = l_Lean_mkAtomFrom(x_1, x_18);
x_20 = l_Lean_mkAppStx___closed__9;
x_21 = lean_array_push(x_20, x_19);
x_22 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__12;
x_23 = lean_array_push(x_21, x_22);
x_24 = l_Lean_nullKind;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Prod_HasRepr___rarg___closed__1;
x_27 = l_Lean_mkAtomFrom(x_1, x_26);
x_28 = l_Lean_mkIdentFrom(x_1, x_17);
x_29 = l_Lean_mkOptionalNode___closed__2;
x_30 = lean_array_push(x_29, x_28);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Option_HasRepr___rarg___closed__3;
x_33 = l_Lean_mkAtomFrom(x_1, x_32);
x_34 = l_Lean_Meta_caseValueAux___lambda__5___closed__8;
x_35 = lean_array_push(x_34, x_27);
x_36 = lean_array_push(x_35, x_31);
x_37 = lean_array_push(x_36, x_25);
x_38 = l_Lean_mkOptionalNode___closed__1;
x_39 = lean_array_push(x_37, x_38);
x_40 = lean_array_push(x_39, x_33);
x_41 = l_Lean_Elab_Term_mkExplicitBinder___closed__2;
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_2, x_43);
x_45 = x_42;
x_46 = lean_array_fset(x_13, x_2, x_45);
lean_dec(x_2);
x_2 = x_44;
x_3 = x_46;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_48 = lean_ctor_get(x_14, 0);
lean_inc(x_48);
lean_dec(x_14);
x_49 = l_Lean_mkIdentFrom(x_1, x_48);
x_50 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___closed__3;
lean_inc(x_49);
x_51 = lean_array_push(x_50, x_49);
x_52 = l___regBuiltin_Lean_Elab_Term_elabTypeOf___closed__2;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_55 = l_Lean_mkAtomFrom(x_1, x_54);
x_56 = l_Lean_mkAppStx___closed__9;
x_57 = lean_array_push(x_56, x_55);
x_58 = lean_array_push(x_57, x_53);
x_59 = l_Lean_nullKind;
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l_Prod_HasRepr___rarg___closed__1;
x_62 = l_Lean_mkAtomFrom(x_1, x_61);
x_63 = l_Lean_mkOptionalNode___closed__2;
x_64 = lean_array_push(x_63, x_49);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Option_HasRepr___rarg___closed__3;
x_67 = l_Lean_mkAtomFrom(x_1, x_66);
x_68 = l_Lean_Meta_caseValueAux___lambda__5___closed__8;
x_69 = lean_array_push(x_68, x_62);
x_70 = lean_array_push(x_69, x_65);
x_71 = lean_array_push(x_70, x_60);
x_72 = l_Lean_mkOptionalNode___closed__1;
x_73 = lean_array_push(x_71, x_72);
x_74 = lean_array_push(x_73, x_67);
x_75 = l_Lean_Elab_Term_mkExplicitBinder___closed__2;
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_add(x_2, x_77);
x_79 = x_76;
x_80 = lean_array_fset(x_13, x_2, x_79);
lean_dec(x_2);
x_2 = x_78;
x_3 = x_80;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = x_2;
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_10 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___boxed), 6, 3);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 2);
lean_dec(x_14);
lean_ctor_set(x_6, 2, x_7);
x_15 = x_10;
lean_inc(x_5);
x_16 = lean_apply_3(x_15, x_5, x_6, x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = l_Array_empty___closed__1;
x_21 = lean_array_push(x_20, x_19);
x_22 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__14;
x_23 = lean_array_push(x_21, x_22);
x_24 = l_Lean_mkAppStx___closed__8;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_mkIdentFrom(x_3, x_1);
x_27 = lean_array_push(x_20, x_26);
x_28 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_18, x_18, x_9, x_20);
lean_dec(x_18);
x_29 = l_Lean_nullKind___closed__2;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_array_push(x_27, x_30);
x_32 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__26;
x_33 = lean_array_push(x_32, x_25);
x_34 = l_Lean_Elab_Term_elabLetDeclCore___closed__6;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_array_push(x_20, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_array_push(x_31, x_37);
x_39 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_40 = lean_array_push(x_38, x_39);
x_41 = lean_array_push(x_40, x_3);
x_42 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__8;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_array_push(x_20, x_43);
x_45 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__6;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_48 = lean_array_push(x_47, x_46);
x_49 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_50 = lean_array_push(x_48, x_49);
x_51 = lean_array_push(x_50, x_4);
x_52 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_16, 0, x_53);
return x_16;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_54 = lean_ctor_get(x_16, 0);
x_55 = lean_ctor_get(x_16, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_16);
x_56 = lean_ctor_get(x_5, 0);
lean_inc(x_56);
lean_dec(x_5);
x_57 = l_Array_empty___closed__1;
x_58 = lean_array_push(x_57, x_56);
x_59 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__14;
x_60 = lean_array_push(x_58, x_59);
x_61 = l_Lean_mkAppStx___closed__8;
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Lean_mkIdentFrom(x_3, x_1);
x_64 = lean_array_push(x_57, x_63);
x_65 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_54, x_54, x_9, x_57);
lean_dec(x_54);
x_66 = l_Lean_nullKind___closed__2;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_array_push(x_64, x_67);
x_69 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__26;
x_70 = lean_array_push(x_69, x_62);
x_71 = l_Lean_Elab_Term_elabLetDeclCore___closed__6;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_array_push(x_57, x_72);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_66);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_array_push(x_68, x_74);
x_76 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_77 = lean_array_push(x_75, x_76);
x_78 = lean_array_push(x_77, x_3);
x_79 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__8;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_array_push(x_57, x_80);
x_82 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__6;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_85 = lean_array_push(x_84, x_83);
x_86 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_87 = lean_array_push(x_85, x_86);
x_88 = lean_array_push(x_87, x_4);
x_89 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_55);
return x_91;
}
}
else
{
uint8_t x_92; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_16);
if (x_92 == 0)
{
return x_16;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_16, 0);
x_94 = lean_ctor_get(x_16, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_16);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_6, 0);
x_97 = lean_ctor_get(x_6, 1);
x_98 = lean_ctor_get(x_6, 3);
x_99 = lean_ctor_get(x_6, 4);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_6);
x_100 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_100, 0, x_96);
lean_ctor_set(x_100, 1, x_97);
lean_ctor_set(x_100, 2, x_7);
lean_ctor_set(x_100, 3, x_98);
lean_ctor_set(x_100, 4, x_99);
x_101 = x_10;
lean_inc(x_5);
x_102 = lean_apply_3(x_101, x_5, x_100, x_12);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_5, 0);
lean_inc(x_106);
lean_dec(x_5);
x_107 = l_Array_empty___closed__1;
x_108 = lean_array_push(x_107, x_106);
x_109 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__14;
x_110 = lean_array_push(x_108, x_109);
x_111 = l_Lean_mkAppStx___closed__8;
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
x_113 = l_Lean_mkIdentFrom(x_3, x_1);
x_114 = lean_array_push(x_107, x_113);
x_115 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_103, x_103, x_9, x_107);
lean_dec(x_103);
x_116 = l_Lean_nullKind___closed__2;
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = lean_array_push(x_114, x_117);
x_119 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__26;
x_120 = lean_array_push(x_119, x_112);
x_121 = l_Lean_Elab_Term_elabLetDeclCore___closed__6;
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
x_123 = lean_array_push(x_107, x_122);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_116);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_array_push(x_118, x_124);
x_126 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_127 = lean_array_push(x_125, x_126);
x_128 = lean_array_push(x_127, x_3);
x_129 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__8;
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = lean_array_push(x_107, x_130);
x_132 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__6;
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_135 = lean_array_push(x_134, x_133);
x_136 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_137 = lean_array_push(x_135, x_136);
x_138 = lean_array_push(x_137, x_4);
x_139 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
if (lean_is_scalar(x_105)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_105;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_104);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_142 = lean_ctor_get(x_102, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_102, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_144 = x_102;
} else {
 lean_dec_ref(x_102);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkJoinPoint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_3);
x_8 = l_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Syntax_copyInfo(x_10, x_3);
lean_dec(x_3);
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
x_14 = l_Lean_Syntax_copyInfo(x_12, x_3);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkJmp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_mkIdentFrom(x_1, x_2);
x_5 = l_Lean_mkAppStx(x_4, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_mkJmp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_Do_ToTerm_mkJmp(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToTerm_toTerm___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("WIP");
return x_1;
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_toTerm___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Elab_Term_Do_ToTerm_toTerm___main(x_6, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Term_Do_ToTerm_declToTerm(x_5, x_8, x_2, x_3, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_dec(x_1);
lean_inc(x_3);
x_17 = l_Lean_Elab_Term_Do_ToTerm_toTerm___main(x_16, x_2, x_3, x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Term_Do_ToTerm_reassignToTerm(x_15, x_18, x_3, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_3);
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
case 2:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 3);
lean_inc(x_28);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_29 = l_Lean_Elab_Term_Do_ToTerm_toTerm___main(x_27, x_2, x_3, x_4);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_3);
lean_inc(x_2);
x_32 = l_Lean_Elab_Term_Do_ToTerm_toTerm___main(x_28, x_2, x_3, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Elab_Term_Do_ToTerm_mkJoinPoint(x_25, x_26, x_30, x_33, x_2, x_3, x_34);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
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
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_29);
if (x_40 == 0)
{
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_29, 0);
x_42 = lean_ctor_get(x_29, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_29);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
case 3:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_dec(x_1);
lean_inc(x_3);
x_46 = l_Lean_Elab_Term_Do_ToTerm_toTerm___main(x_45, x_2, x_3, x_4);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Elab_Term_Do_ToTerm_actionToTerm(x_44, x_47, x_3, x_48);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_44);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 0);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_46);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
case 4:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
lean_dec(x_1);
x_55 = l_Lean_Elab_Term_Do_ToTerm_breakToTerm(x_54, x_2, x_3, x_4);
lean_dec(x_54);
return x_55;
}
case 5:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
lean_dec(x_1);
x_57 = l_Lean_Elab_Term_Do_ToTerm_continueToTerm(x_56, x_2, x_3, x_4);
lean_dec(x_56);
return x_57;
}
case 6:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
lean_dec(x_1);
x_60 = l_Lean_Elab_Term_Do_ToTerm_returnToTerm(x_58, x_59, x_2, x_3, x_4);
lean_dec(x_58);
return x_60;
}
case 7:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 3);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 5);
lean_inc(x_65);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_66 = l_Lean_Elab_Term_Do_ToTerm_toTerm___main(x_64, x_2, x_3, x_4);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Elab_Term_Do_ToTerm_toTerm___main(x_65, x_2, x_3, x_68);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = l_Lean_Elab_Term_Do_ToTerm_mkIte(x_61, x_62, x_63, x_67, x_71);
lean_dec(x_61);
lean_ctor_set(x_69, 0, x_72);
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_69, 0);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_69);
x_75 = l_Lean_Elab_Term_Do_ToTerm_mkIte(x_61, x_62, x_63, x_67, x_73);
lean_dec(x_61);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_67);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
x_77 = !lean_is_exclusive(x_69);
if (x_77 == 0)
{
return x_69;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_69, 0);
x_79 = lean_ctor_get(x_69, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_69);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_66);
if (x_81 == 0)
{
return x_66;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_66, 0);
x_83 = lean_ctor_get(x_66, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_66);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
case 8:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_box(0);
x_86 = l_Lean_Elab_Term_Do_ToTerm_toTerm___main___closed__1;
x_87 = l_Lean_Macro_throwError___rarg(x_85, x_86, x_3, x_4);
lean_dec(x_3);
return x_87;
}
default: 
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_3);
lean_dec(x_2);
x_88 = lean_ctor_get(x_1, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_1, 2);
lean_inc(x_90);
lean_dec(x_1);
x_91 = l_Lean_Elab_Term_Do_ToTerm_mkJmp(x_88, x_89, x_90);
lean_dec(x_88);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_4);
return x_92;
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_toTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_Do_ToTerm_toTerm___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_Do_ToTerm_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
x_8 = l_Lean_Elab_Term_Do_ToTerm_toTerm___main(x_1, x_7, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
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
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_withNewVars___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_1, x_1, x_13, x_12);
lean_ctor_set(x_3, 2, x_14);
x_15 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_3, 2);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_1, x_1, x_20, x_18);
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_19);
x_23 = lean_apply_8(x_2, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_23;
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_withNewVars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Do_ToCodeBlock_withNewVars___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_withNewVars___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_Do_ToCodeBlock_withNewVars___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
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
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* _init_l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' cannot be reassigned");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_array_fget(x_2, x_3);
x_17 = lean_ctor_get(x_1, 2);
x_18 = l_Lean_NameSet_contains(x_17, x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_inc(x_7);
lean_inc(x_16);
x_19 = l_Lean_Elab_Term_resolveLocalName(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_3);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_simp_macro_scopes(x_16);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__3;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_16);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_dec(x_19);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_3, x_36);
lean_dec(x_3);
x_3 = x_37;
x_11 = x_35;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_34);
lean_dec(x_3);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_simp_macro_scopes(x_16);
x_41 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__3;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(x_45, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
lean_dec(x_7);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
return x_46;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_46);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_16);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_3, x_51);
lean_dec(x_3);
x_3 = x_52;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2(x_2, x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_withFor___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
lean_ctor_set_uint8(x_2, sizeof(void*)*3, x_11);
x_12 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = 1;
x_17 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_16);
x_18 = lean_apply_8(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_withFor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Do_ToCodeBlock_withFor___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_8, 3);
x_13 = l_Lean_replaceRef(x_1, x_12);
x_14 = l_Lean_replaceRef(x_13, x_12);
lean_dec(x_13);
x_15 = l_Lean_replaceRef(x_14, x_12);
lean_dec(x_12);
lean_dec(x_14);
lean_ctor_set(x_8, 3, x_15);
x_16 = l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
x_19 = lean_ctor_get(x_8, 2);
x_20 = lean_ctor_get(x_8, 3);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_21 = l_Lean_replaceRef(x_1, x_20);
x_22 = l_Lean_replaceRef(x_21, x_20);
lean_dec(x_21);
x_23 = l_Lean_replaceRef(x_22, x_20);
lean_dec(x_20);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_23);
x_25 = l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_24, x_9, x_10);
lean_dec(x_24);
return x_25;
}
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwErrorAt___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__1___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__2___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__2___rarg), 1, 0);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_77; 
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_77 = l_Lean_Syntax_isIdent(x_1);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_box(0);
x_12 = x_78;
goto block_76;
}
else
{
lean_object* x_79; uint8_t x_80; 
x_79 = l_Lean_Syntax_getId(x_1);
x_80 = l_Lean_NameSet_contains(x_11, x_79);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_79);
x_81 = lean_box(0);
x_12 = x_81;
goto block_76;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_82 = lean_ctor_get(x_2, 0);
lean_inc(x_82);
lean_dec(x_2);
x_83 = lean_ctor_get(x_3, 1);
lean_inc(x_83);
lean_inc(x_79);
x_84 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_84, 0, x_79);
x_85 = l_Std_RBNode_erase___at_Lean_Elab_Term_Do_eraseVars___spec__1(x_79, x_11);
lean_dec(x_79);
x_86 = l___private_Lean_Elab_Do_5__nameSetToArray(x_85);
x_87 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_st_ref_get(x_9, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_st_ref_get(x_9, x_92);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_8, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_8, 2);
lean_inc(x_99);
lean_inc(x_93);
x_100 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_5__expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_100, 0, x_93);
x_101 = x_100;
x_102 = lean_environment_main_module(x_93);
x_103 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_103, 2, x_88);
lean_ctor_set(x_103, 3, x_98);
lean_ctor_set(x_103, 4, x_99);
lean_inc(x_86);
x_104 = l_Lean_Elab_Term_Do_ToTerm_run(x_82, x_83, x_86, x_84, x_103, x_97);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_dec(x_8);
lean_dec(x_3);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_st_ref_take(x_9, x_96);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = !lean_is_exclusive(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_108, 1);
lean_dec(x_111);
lean_ctor_set(x_108, 1, x_106);
x_112 = lean_st_ref_set(x_9, x_108, x_109);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_112, 0);
lean_dec(x_114);
x_115 = 1;
x_116 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_116, 0, x_86);
lean_ctor_set(x_116, 1, x_105);
lean_ctor_set_uint8(x_116, sizeof(void*)*2, x_115);
lean_ctor_set(x_112, 0, x_116);
return x_112;
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
lean_dec(x_112);
x_118 = 1;
x_119 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_119, 0, x_86);
lean_ctor_set(x_119, 1, x_105);
lean_ctor_set_uint8(x_119, sizeof(void*)*2, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_121 = lean_ctor_get(x_108, 0);
x_122 = lean_ctor_get(x_108, 2);
x_123 = lean_ctor_get(x_108, 3);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_108);
x_124 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_106);
lean_ctor_set(x_124, 2, x_122);
lean_ctor_set(x_124, 3, x_123);
x_125 = lean_st_ref_set(x_9, x_124, x_109);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
x_128 = 1;
x_129 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_129, 0, x_86);
lean_ctor_set(x_129, 1, x_105);
lean_ctor_set_uint8(x_129, sizeof(void*)*2, x_128);
if (lean_is_scalar(x_127)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_127;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_126);
return x_130;
}
}
else
{
lean_object* x_131; 
lean_dec(x_86);
x_131 = lean_ctor_get(x_104, 0);
lean_inc(x_131);
lean_dec(x_104);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__1___rarg(x_132, x_135, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_96);
lean_dec(x_3);
lean_dec(x_132);
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
return x_136;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_136);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
else
{
lean_object* x_141; uint8_t x_142; 
lean_dec(x_8);
lean_dec(x_3);
x_141 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__2___rarg(x_96);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
return x_141;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_141, 0);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_141);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
}
}
block_76:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_12);
x_13 = l___private_Lean_Elab_Do_5__nameSetToArray(x_11);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
x_16 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_9, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_9, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_8, 2);
lean_inc(x_28);
lean_inc(x_22);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_5__expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_29, 0, x_22);
x_30 = x_29;
x_31 = lean_environment_main_module(x_22);
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_17);
lean_ctor_set(x_32, 3, x_27);
lean_ctor_set(x_32, 4, x_28);
x_33 = lean_box(2);
lean_inc(x_13);
x_34 = l_Lean_Elab_Term_Do_ToTerm_run(x_14, x_15, x_13, x_33, x_32, x_26);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_8);
lean_dec(x_3);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_take(x_9, x_25);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_38, 1);
lean_dec(x_41);
lean_ctor_set(x_38, 1, x_36);
x_42 = lean_st_ref_set(x_9, x_38, x_39);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = 0;
x_46 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_46, 0, x_13);
lean_ctor_set(x_46, 1, x_35);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_45);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = 0;
x_49 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_49, 0, x_13);
lean_ctor_set(x_49, 1, x_35);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_51 = lean_ctor_get(x_38, 0);
x_52 = lean_ctor_get(x_38, 2);
x_53 = lean_ctor_get(x_38, 3);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_38);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_36);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set(x_54, 3, x_53);
x_55 = lean_st_ref_set(x_9, x_54, x_39);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = 0;
x_59 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_59, 0, x_13);
lean_ctor_set(x_59, 1, x_35);
lean_ctor_set_uint8(x_59, sizeof(void*)*2, x_58);
if (lean_is_scalar(x_57)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_57;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_56);
return x_60;
}
}
else
{
lean_object* x_61; 
lean_dec(x_13);
x_61 = lean_ctor_get(x_34, 0);
lean_inc(x_61);
lean_dec(x_34);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__1___rarg(x_62, x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
lean_dec(x_3);
lean_dec(x_62);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
return x_66;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
lean_object* x_71; uint8_t x_72; 
lean_dec(x_8);
lean_dec(x_3);
x_71 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__2___rarg(x_25);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
return x_71;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_71);
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
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid statement, can only be used inside 'for ... in ... do ...'");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___closed__3;
x_11 = l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("must be last element in a 'do' sequence");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_List_isEmpty___rarg(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___closed__3;
x_12 = l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Do_15__expandLiftMethodAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_15 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main(x_14, x_3, x_4, x_5);
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
lean_object* _init_l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("←");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Do_15__expandLiftMethodAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2;
x_8 = lean_name_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4;
x_10 = lean_name_eq(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__6;
x_12 = lean_name_eq(x_5, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTermQuot___closed__1;
x_14 = lean_name_eq(x_5, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
x_18 = l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__2;
x_19 = lean_name_eq(x_5, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = x_6;
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Do_15__expandLiftMethodAux___main___spec__1), 5, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_20);
x_23 = x_22;
x_24 = lean_apply_3(x_23, x_2, x_3, x_4);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_ctor_set(x_1, 1, x_28);
lean_ctor_set(x_26, 0, x_1);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_26);
lean_ctor_set(x_1, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_24, 0, x_31);
return x_24;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_36 = x_32;
} else {
 lean_dec_ref(x_32);
 x_36 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_34);
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_1);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
return x_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_5);
x_43 = l_Lean_Syntax_inhabited;
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_array_get(x_43, x_6, x_44);
lean_dec(x_6);
x_46 = lean_nat_add(x_4, x_44);
x_47 = !lean_is_exclusive(x_3);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_3, 1);
x_49 = lean_ctor_get(x_3, 2);
lean_dec(x_49);
lean_inc(x_4);
lean_inc(x_48);
lean_ctor_set(x_3, 2, x_4);
x_50 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main(x_45, x_2, x_3, x_46);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = l___private_Lean_Elab_Term_4__expandCDot___main___closed__3;
x_57 = l_Lean_addMacroScope(x_48, x_56, x_4);
x_58 = lean_box(0);
x_59 = l_Lean_SourceInfo_inhabited___closed__1;
x_60 = l___private_Lean_Elab_Term_4__expandCDot___main___closed__2;
x_61 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_57);
lean_ctor_set(x_61, 3, x_58);
x_62 = l_Array_empty___closed__1;
lean_inc(x_61);
x_63 = lean_array_push(x_62, x_61);
x_64 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_65 = lean_array_push(x_63, x_64);
x_66 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4;
x_67 = lean_array_push(x_65, x_66);
x_68 = lean_array_push(x_67, x_54);
x_69 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
lean_ctor_set(x_1, 1, x_68);
lean_ctor_set(x_1, 0, x_69);
x_70 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_71 = lean_array_push(x_70, x_1);
x_72 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__6;
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_array_push(x_62, x_73);
x_75 = lean_array_push(x_74, x_64);
x_76 = l_Lean_nullKind___closed__2;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_array_push(x_62, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_array_push(x_62, x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_9);
lean_ctor_set(x_81, 1, x_80);
x_82 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2;
x_83 = lean_array_push(x_82, x_81);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_7);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Syntax_getArg(x_84, x_44);
lean_dec(x_84);
x_86 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_85);
x_87 = l_List_append___rarg(x_55, x_86);
lean_ctor_set(x_52, 1, x_87);
lean_ctor_set(x_52, 0, x_61);
return x_50;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_88 = lean_ctor_get(x_52, 0);
x_89 = lean_ctor_get(x_52, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_52);
x_90 = l___private_Lean_Elab_Term_4__expandCDot___main___closed__3;
x_91 = l_Lean_addMacroScope(x_48, x_90, x_4);
x_92 = lean_box(0);
x_93 = l_Lean_SourceInfo_inhabited___closed__1;
x_94 = l___private_Lean_Elab_Term_4__expandCDot___main___closed__2;
x_95 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_91);
lean_ctor_set(x_95, 3, x_92);
x_96 = l_Array_empty___closed__1;
lean_inc(x_95);
x_97 = lean_array_push(x_96, x_95);
x_98 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_99 = lean_array_push(x_97, x_98);
x_100 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4;
x_101 = lean_array_push(x_99, x_100);
x_102 = lean_array_push(x_101, x_88);
x_103 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
lean_ctor_set(x_1, 1, x_102);
lean_ctor_set(x_1, 0, x_103);
x_104 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_105 = lean_array_push(x_104, x_1);
x_106 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__6;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = lean_array_push(x_96, x_107);
x_109 = lean_array_push(x_108, x_98);
x_110 = l_Lean_nullKind___closed__2;
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
x_112 = lean_array_push(x_96, x_111);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_array_push(x_96, x_113);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_9);
lean_ctor_set(x_115, 1, x_114);
x_116 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2;
x_117 = lean_array_push(x_116, x_115);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_7);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_Syntax_getArg(x_118, x_44);
lean_dec(x_118);
x_120 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_119);
x_121 = l_List_append___rarg(x_89, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_95);
lean_ctor_set(x_122, 1, x_121);
lean_ctor_set(x_50, 0, x_122);
return x_50;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_123 = lean_ctor_get(x_50, 0);
x_124 = lean_ctor_get(x_50, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_50);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_127 = x_123;
} else {
 lean_dec_ref(x_123);
 x_127 = lean_box(0);
}
x_128 = l___private_Lean_Elab_Term_4__expandCDot___main___closed__3;
x_129 = l_Lean_addMacroScope(x_48, x_128, x_4);
x_130 = lean_box(0);
x_131 = l_Lean_SourceInfo_inhabited___closed__1;
x_132 = l___private_Lean_Elab_Term_4__expandCDot___main___closed__2;
x_133 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set(x_133, 2, x_129);
lean_ctor_set(x_133, 3, x_130);
x_134 = l_Array_empty___closed__1;
lean_inc(x_133);
x_135 = lean_array_push(x_134, x_133);
x_136 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_137 = lean_array_push(x_135, x_136);
x_138 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4;
x_139 = lean_array_push(x_137, x_138);
x_140 = lean_array_push(x_139, x_125);
x_141 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
lean_ctor_set(x_1, 1, x_140);
lean_ctor_set(x_1, 0, x_141);
x_142 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_143 = lean_array_push(x_142, x_1);
x_144 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__6;
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
x_146 = lean_array_push(x_134, x_145);
x_147 = lean_array_push(x_146, x_136);
x_148 = l_Lean_nullKind___closed__2;
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
x_150 = lean_array_push(x_134, x_149);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_array_push(x_134, x_151);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_9);
lean_ctor_set(x_153, 1, x_152);
x_154 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2;
x_155 = lean_array_push(x_154, x_153);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_7);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_Lean_Syntax_getArg(x_156, x_44);
lean_dec(x_156);
x_158 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_157);
x_159 = l_List_append___rarg(x_126, x_158);
if (lean_is_scalar(x_127)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_127;
}
lean_ctor_set(x_160, 0, x_133);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_124);
return x_161;
}
}
else
{
uint8_t x_162; 
lean_dec(x_48);
lean_free_object(x_1);
lean_dec(x_4);
x_162 = !lean_is_exclusive(x_50);
if (x_162 == 0)
{
return x_50;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_50, 0);
x_164 = lean_ctor_get(x_50, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_50);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_166 = lean_ctor_get(x_3, 0);
x_167 = lean_ctor_get(x_3, 1);
x_168 = lean_ctor_get(x_3, 3);
x_169 = lean_ctor_get(x_3, 4);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_167);
x_170 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_170, 0, x_166);
lean_ctor_set(x_170, 1, x_167);
lean_ctor_set(x_170, 2, x_4);
lean_ctor_set(x_170, 3, x_168);
lean_ctor_set(x_170, 4, x_169);
x_171 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main(x_45, x_2, x_170, x_46);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_174 = x_171;
} else {
 lean_dec_ref(x_171);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_172, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_177 = x_172;
} else {
 lean_dec_ref(x_172);
 x_177 = lean_box(0);
}
x_178 = l___private_Lean_Elab_Term_4__expandCDot___main___closed__3;
x_179 = l_Lean_addMacroScope(x_167, x_178, x_4);
x_180 = lean_box(0);
x_181 = l_Lean_SourceInfo_inhabited___closed__1;
x_182 = l___private_Lean_Elab_Term_4__expandCDot___main___closed__2;
x_183 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
lean_ctor_set(x_183, 2, x_179);
lean_ctor_set(x_183, 3, x_180);
x_184 = l_Array_empty___closed__1;
lean_inc(x_183);
x_185 = lean_array_push(x_184, x_183);
x_186 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_187 = lean_array_push(x_185, x_186);
x_188 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4;
x_189 = lean_array_push(x_187, x_188);
x_190 = lean_array_push(x_189, x_175);
x_191 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
lean_ctor_set(x_1, 1, x_190);
lean_ctor_set(x_1, 0, x_191);
x_192 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_193 = lean_array_push(x_192, x_1);
x_194 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__6;
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
x_196 = lean_array_push(x_184, x_195);
x_197 = lean_array_push(x_196, x_186);
x_198 = l_Lean_nullKind___closed__2;
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = lean_array_push(x_184, x_199);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_array_push(x_184, x_201);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_9);
lean_ctor_set(x_203, 1, x_202);
x_204 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2;
x_205 = lean_array_push(x_204, x_203);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_7);
lean_ctor_set(x_206, 1, x_205);
x_207 = l_Lean_Syntax_getArg(x_206, x_44);
lean_dec(x_206);
x_208 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_207);
x_209 = l_List_append___rarg(x_176, x_208);
if (lean_is_scalar(x_177)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_177;
}
lean_ctor_set(x_210, 0, x_183);
lean_ctor_set(x_210, 1, x_209);
if (lean_is_scalar(x_174)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_174;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_173);
return x_211;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_167);
lean_free_object(x_1);
lean_dec(x_4);
x_212 = lean_ctor_get(x_171, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_171, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_214 = x_171;
} else {
 lean_dec_ref(x_171);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
}
}
}
else
{
lean_object* x_216; uint8_t x_217; 
lean_dec(x_1);
x_216 = l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__2;
x_217 = lean_name_eq(x_5, x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_218 = x_6;
x_219 = lean_unsigned_to_nat(0u);
x_220 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Do_15__expandLiftMethodAux___main___spec__1), 5, 2);
lean_closure_set(x_220, 0, x_219);
lean_closure_set(x_220, 1, x_218);
x_221 = x_220;
x_222 = lean_apply_3(x_221, x_2, x_3, x_4);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_225 = x_222;
} else {
 lean_dec_ref(x_222);
 x_225 = lean_box(0);
}
x_226 = lean_ctor_get(x_223, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_223, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_228 = x_223;
} else {
 lean_dec_ref(x_223);
 x_228 = lean_box(0);
}
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_5);
lean_ctor_set(x_229, 1, x_226);
if (lean_is_scalar(x_228)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_228;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_227);
if (lean_is_scalar(x_225)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_225;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_224);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_5);
x_232 = lean_ctor_get(x_222, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_222, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_234 = x_222;
} else {
 lean_dec_ref(x_222);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_5);
x_236 = l_Lean_Syntax_inhabited;
x_237 = lean_unsigned_to_nat(1u);
x_238 = lean_array_get(x_236, x_6, x_237);
lean_dec(x_6);
x_239 = lean_nat_add(x_4, x_237);
x_240 = lean_ctor_get(x_3, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_3, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_3, 3);
lean_inc(x_242);
x_243 = lean_ctor_get(x_3, 4);
lean_inc(x_243);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_244 = x_3;
} else {
 lean_dec_ref(x_3);
 x_244 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_241);
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(0, 5, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_240);
lean_ctor_set(x_245, 1, x_241);
lean_ctor_set(x_245, 2, x_4);
lean_ctor_set(x_245, 3, x_242);
lean_ctor_set(x_245, 4, x_243);
x_246 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main(x_238, x_2, x_245, x_239);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_249 = x_246;
} else {
 lean_dec_ref(x_246);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_247, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_247, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_252 = x_247;
} else {
 lean_dec_ref(x_247);
 x_252 = lean_box(0);
}
x_253 = l___private_Lean_Elab_Term_4__expandCDot___main___closed__3;
x_254 = l_Lean_addMacroScope(x_241, x_253, x_4);
x_255 = lean_box(0);
x_256 = l_Lean_SourceInfo_inhabited___closed__1;
x_257 = l___private_Lean_Elab_Term_4__expandCDot___main___closed__2;
x_258 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
lean_ctor_set(x_258, 2, x_254);
lean_ctor_set(x_258, 3, x_255);
x_259 = l_Array_empty___closed__1;
lean_inc(x_258);
x_260 = lean_array_push(x_259, x_258);
x_261 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_262 = lean_array_push(x_260, x_261);
x_263 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4;
x_264 = lean_array_push(x_262, x_263);
x_265 = lean_array_push(x_264, x_250);
x_266 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_265);
x_268 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_269 = lean_array_push(x_268, x_267);
x_270 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__6;
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_269);
x_272 = lean_array_push(x_259, x_271);
x_273 = lean_array_push(x_272, x_261);
x_274 = l_Lean_nullKind___closed__2;
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_273);
x_276 = lean_array_push(x_259, x_275);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_274);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_array_push(x_259, x_277);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_9);
lean_ctor_set(x_279, 1, x_278);
x_280 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2;
x_281 = lean_array_push(x_280, x_279);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_7);
lean_ctor_set(x_282, 1, x_281);
x_283 = l_Lean_Syntax_getArg(x_282, x_237);
lean_dec(x_282);
x_284 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_283);
x_285 = l_List_append___rarg(x_251, x_284);
if (lean_is_scalar(x_252)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_252;
}
lean_ctor_set(x_286, 0, x_258);
lean_ctor_set(x_286, 1, x_285);
if (lean_is_scalar(x_249)) {
 x_287 = lean_alloc_ctor(0, 2, 0);
} else {
 x_287 = x_249;
}
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_248);
return x_287;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_241);
lean_dec(x_4);
x_288 = lean_ctor_get(x_246, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_246, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_290 = x_246;
} else {
 lean_dec_ref(x_246);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(1, 2, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_289);
return x_291;
}
}
}
}
else
{
lean_object* x_292; lean_object* x_293; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_1);
lean_ctor_set(x_292, 1, x_2);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_4);
return x_293;
}
}
else
{
lean_object* x_294; lean_object* x_295; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_1);
lean_ctor_set(x_294, 1, x_2);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_4);
return x_295;
}
}
else
{
lean_object* x_296; lean_object* x_297; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_1);
lean_ctor_set(x_296, 1, x_2);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_4);
return x_297;
}
}
else
{
lean_object* x_298; lean_object* x_299; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_1);
lean_ctor_set(x_298, 1, x_2);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_4);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; 
lean_dec(x_3);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_1);
lean_ctor_set(x_300, 1, x_2);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_4);
return x_301;
}
}
}
lean_object* l___private_Lean_Elab_Do_15__expandLiftMethodAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_expandLiftMethod(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l___private_Lean_Elab_Do_1__hasLiftMethod___main(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main(x_1, x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_ctor_set(x_11, 1, x_13);
lean_ctor_set(x_11, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_22 = x_18;
} else {
 lean_dec_ref(x_18);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
return x_9;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_mkReturnUnit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_Elab_Term_Do_mkUnless___closed__6;
x_17 = l_Lean_addMacroScope(x_15, x_16, x_11);
x_18 = l_Lean_SourceInfo_inhabited___closed__1;
x_19 = l_Lean_Elab_Term_Do_mkUnless___closed__3;
x_20 = l_Lean_Elab_Term_Do_mkUnless___closed__8;
x_21 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_20);
x_22 = l_Lean_Syntax_copyInfo(x_21, x_1);
x_23 = l_Lean_Elab_Term_Do_mkReturn(x_1, x_22);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = l_Lean_Elab_Term_Do_mkUnless___closed__6;
x_27 = l_Lean_addMacroScope(x_24, x_26, x_11);
x_28 = l_Lean_SourceInfo_inhabited___closed__1;
x_29 = l_Lean_Elab_Term_Do_mkUnless___closed__3;
x_30 = l_Lean_Elab_Term_Do_mkUnless___closed__8;
x_31 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set(x_31, 3, x_30);
x_32 = l_Lean_Syntax_copyInfo(x_31, x_1);
x_33 = l_Lean_Elab_Term_Do_mkReturn(x_1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
}
}
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_mkReturnUnit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_Do_ToCodeBlock_mkReturnUnit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_List_map___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__1(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Syntax_copyInfo(x_5, x_1);
x_8 = l_List_map___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__1(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Lean_Syntax_copyInfo(x_9, x_1);
x_12 = l_List_map___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__1(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_mkIdentFrom(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__3___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__3___rarg), 1, 0);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doUnless");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doFor");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doMatch");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doTry");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doBreak");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doContinue");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doExpr");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected do-element");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__15;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__16;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__17;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Lean_Elab_Do_9__expandDoIf___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__19;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_ToTerm_toTerm___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__21;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_System_FilePath_dirName___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("forIn");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__24;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__24;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__25;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__24;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_Prim_fopenFlags___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_IO_Prim_fopenFlags___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__28;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_IO_Prim_fopenFlags___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("forInMap");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__31;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__31;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__32;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__31;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("2");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__35;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__36;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_fieldIdxKind___closed__2;
x_2 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__37;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("1");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__39;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__40;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_fieldIdxKind___closed__2;
x_2 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__41;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = l_Lean_Elab_Term_Do_ToCodeBlock_mkReturnUnit(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; 
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 2);
x_18 = lean_ctor_get(x_7, 3);
x_19 = l_Lean_replaceRef(x_12, x_18);
x_20 = l_Lean_replaceRef(x_19, x_18);
lean_dec(x_19);
x_21 = l_Lean_replaceRef(x_20, x_18);
lean_dec(x_18);
lean_dec(x_20);
lean_inc(x_17);
lean_inc(x_16);
lean_ctor_set(x_7, 3, x_21);
x_1391 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_1392 = lean_ctor_get(x_1391, 0);
lean_inc(x_1392);
x_1393 = lean_ctor_get(x_1391, 1);
lean_inc(x_1393);
lean_dec(x_1391);
x_1394 = lean_st_ref_get(x_8, x_1393);
x_1395 = lean_ctor_get(x_1394, 0);
lean_inc(x_1395);
x_1396 = lean_ctor_get(x_1394, 1);
lean_inc(x_1396);
lean_dec(x_1394);
x_1397 = lean_ctor_get(x_1395, 0);
lean_inc(x_1397);
lean_dec(x_1395);
x_1398 = lean_st_ref_get(x_8, x_1396);
x_1399 = lean_ctor_get(x_1398, 0);
lean_inc(x_1399);
x_1400 = lean_ctor_get(x_1398, 1);
lean_inc(x_1400);
lean_dec(x_1398);
x_1401 = lean_ctor_get(x_1399, 1);
lean_inc(x_1401);
lean_dec(x_1399);
lean_inc(x_1397);
x_1402 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_5__expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_1402, 0, x_1397);
x_1403 = x_1402;
x_1404 = lean_environment_main_module(x_1397);
lean_inc(x_17);
lean_inc(x_16);
x_1405 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1405, 0, x_1403);
lean_ctor_set(x_1405, 1, x_1404);
lean_ctor_set(x_1405, 2, x_1392);
lean_ctor_set(x_1405, 3, x_16);
lean_ctor_set(x_1405, 4, x_17);
x_1406 = l_Lean_Elab_Term_Do_ToCodeBlock_expandLiftMethod(x_12, x_1405, x_1401);
if (lean_obj_tag(x_1406) == 0)
{
lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; uint8_t x_1412; 
x_1407 = lean_ctor_get(x_1406, 0);
lean_inc(x_1407);
x_1408 = lean_ctor_get(x_1406, 1);
lean_inc(x_1408);
lean_dec(x_1406);
x_1409 = lean_st_ref_take(x_8, x_1400);
x_1410 = lean_ctor_get(x_1409, 0);
lean_inc(x_1410);
x_1411 = lean_ctor_get(x_1409, 1);
lean_inc(x_1411);
lean_dec(x_1409);
x_1412 = !lean_is_exclusive(x_1410);
if (x_1412 == 0)
{
lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; 
x_1413 = lean_ctor_get(x_1410, 1);
lean_dec(x_1413);
lean_ctor_set(x_1410, 1, x_1408);
x_1414 = lean_st_ref_set(x_8, x_1410, x_1411);
x_1415 = lean_ctor_get(x_1414, 1);
lean_inc(x_1415);
lean_dec(x_1414);
x_22 = x_1407;
x_23 = x_1415;
goto block_1390;
}
else
{
lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; 
x_1416 = lean_ctor_get(x_1410, 0);
x_1417 = lean_ctor_get(x_1410, 2);
x_1418 = lean_ctor_get(x_1410, 3);
lean_inc(x_1418);
lean_inc(x_1417);
lean_inc(x_1416);
lean_dec(x_1410);
x_1419 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1419, 0, x_1416);
lean_ctor_set(x_1419, 1, x_1408);
lean_ctor_set(x_1419, 2, x_1417);
lean_ctor_set(x_1419, 3, x_1418);
x_1420 = lean_st_ref_set(x_8, x_1419, x_1411);
x_1421 = lean_ctor_get(x_1420, 1);
lean_inc(x_1421);
lean_dec(x_1420);
x_22 = x_1407;
x_23 = x_1421;
goto block_1390;
}
}
else
{
lean_object* x_1422; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
x_1422 = lean_ctor_get(x_1406, 0);
lean_inc(x_1422);
lean_dec(x_1406);
if (lean_obj_tag(x_1422) == 0)
{
lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; uint8_t x_1428; 
x_1423 = lean_ctor_get(x_1422, 0);
lean_inc(x_1423);
x_1424 = lean_ctor_get(x_1422, 1);
lean_inc(x_1424);
lean_dec(x_1422);
x_1425 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1425, 0, x_1424);
x_1426 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1426, 0, x_1425);
x_1427 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_1423, x_1426, x_3, x_4, x_5, x_6, x_7, x_8, x_1400);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1423);
x_1428 = !lean_is_exclusive(x_1427);
if (x_1428 == 0)
{
return x_1427;
}
else
{
lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; 
x_1429 = lean_ctor_get(x_1427, 0);
x_1430 = lean_ctor_get(x_1427, 1);
lean_inc(x_1430);
lean_inc(x_1429);
lean_dec(x_1427);
x_1431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1431, 0, x_1429);
lean_ctor_set(x_1431, 1, x_1430);
return x_1431;
}
}
else
{
lean_object* x_1432; uint8_t x_1433; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1432 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__3___rarg(x_1400);
x_1433 = !lean_is_exclusive(x_1432);
if (x_1433 == 0)
{
return x_1432;
}
else
{
lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; 
x_1434 = lean_ctor_get(x_1432, 0);
x_1435 = lean_ctor_get(x_1432, 1);
lean_inc(x_1435);
lean_inc(x_1434);
lean_dec(x_1432);
x_1436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1436, 0, x_1434);
lean_ctor_set(x_1436, 1, x_1435);
return x_1436;
}
}
}
block_1390:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_List_isEmpty___rarg(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_17);
lean_dec(x_16);
x_27 = lean_box(0);
if (lean_is_scalar(x_14)) {
 x_28 = lean_alloc_ctor(1, 2, 0);
} else {
 x_28 = x_14;
}
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_List_append___rarg(x_24, x_28);
x_30 = l_List_append___rarg(x_29, x_13);
x_1 = x_30;
x_9 = x_23;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_24);
lean_dec(x_14);
lean_inc(x_25);
x_32 = l_Lean_Syntax_getKind(x_25);
x_33 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__2;
x_34 = lean_name_eq(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__4;
x_36 = lean_name_eq(x_32, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__6;
x_38 = lean_name_eq(x_32, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__2;
x_40 = lean_name_eq(x_32, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__4;
x_42 = lean_name_eq(x_32, x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__8;
x_44 = lean_name_eq(x_32, x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1___closed__2;
x_46 = lean_name_eq(x_32, x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__2;
x_48 = lean_name_eq(x_32, x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__4;
x_50 = lean_name_eq(x_32, x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
lean_dec(x_17);
lean_dec(x_16);
x_51 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__6;
x_52 = lean_name_eq(x_32, x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__8;
x_54 = lean_name_eq(x_32, x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__10;
x_56 = lean_name_eq(x_32, x_55);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__12;
x_58 = lean_name_eq(x_32, x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = l___private_Lean_Elab_Do_9__expandDoIf___closed__2;
x_60 = lean_name_eq(x_32, x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__2;
x_62 = lean_name_eq(x_32, x_61);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__4;
x_64 = lean_name_eq(x_32, x_63);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__14;
x_66 = lean_name_eq(x_32, x_65);
lean_dec(x_32);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_13);
x_67 = lean_box(0);
x_68 = 0;
x_69 = lean_unsigned_to_nat(0u);
x_70 = l_Lean_Syntax_formatStxAux___main(x_67, x_68, x_69, x_25);
x_71 = lean_box(0);
x_72 = l_Lean_Format_pretty(x_70, x_71);
x_73 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__18;
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(x_76, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_unsigned_to_nat(0u);
x_79 = l_Lean_Syntax_getArg(x_25, x_78);
x_80 = l_List_isEmpty___rarg(x_13);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_25);
x_81 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = l_Lean_Elab_Term_Do_mkAction(x_79, x_83);
lean_ctor_set(x_81, 0, x_84);
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_81, 0);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_81);
x_87 = l_Lean_Elab_Term_Do_mkAction(x_79, x_85);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
uint8_t x_89; 
lean_dec(x_79);
x_89 = !lean_is_exclusive(x_81);
if (x_89 == 0)
{
return x_81;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_81, 0);
x_91 = lean_ctor_get(x_81, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_81);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
lean_dec(x_13);
x_93 = lean_st_ref_take(x_8, x_23);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = !lean_is_exclusive(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_97 = lean_ctor_get(x_94, 1);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_add(x_97, x_98);
lean_ctor_set(x_94, 1, x_99);
x_100 = lean_st_ref_set(x_8, x_94, x_95);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = !lean_is_exclusive(x_3);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_103 = lean_ctor_get(x_3, 7);
lean_dec(x_103);
lean_ctor_set(x_3, 7, x_97);
x_104 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_101);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Meta_mkArrow___rarg___closed__2;
x_111 = l_Lean_addMacroScope(x_108, x_110, x_105);
x_112 = lean_box(0);
x_113 = l_Lean_SourceInfo_inhabited___closed__1;
x_114 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__2;
x_115 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_115, 2, x_111);
lean_ctor_set(x_115, 3, x_112);
x_116 = l_Array_empty___closed__1;
x_117 = lean_array_push(x_116, x_115);
x_118 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
lean_inc(x_117);
x_119 = lean_array_push(x_117, x_118);
x_120 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4;
x_121 = lean_array_push(x_119, x_120);
x_122 = lean_array_push(x_121, x_79);
x_123 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_126 = lean_array_push(x_125, x_124);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_37);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_array_push(x_116, x_127);
x_129 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_130 = lean_array_push(x_128, x_129);
x_131 = l_Lean_nullKind___closed__2;
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_133 = lean_array_push(x_116, x_132);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_117);
x_135 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__20;
x_136 = lean_array_push(x_135, x_134);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_59);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_array_push(x_116, x_137);
x_139 = lean_array_push(x_138, x_118);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_131);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_array_push(x_133, x_140);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_131);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_array_push(x_116, x_142);
x_144 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4;
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
x_146 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2;
x_147 = lean_array_push(x_146, x_145);
x_148 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2;
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
x_150 = l_Lean_Syntax_getArg(x_149, x_98);
lean_dec(x_149);
x_151 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_150);
x_152 = l_List_map___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__1(x_25, x_151);
lean_dec(x_25);
x_1 = x_152;
x_9 = x_109;
goto _start;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_154 = lean_ctor_get(x_3, 0);
x_155 = lean_ctor_get(x_3, 1);
x_156 = lean_ctor_get(x_3, 2);
x_157 = lean_ctor_get(x_3, 3);
x_158 = lean_ctor_get(x_3, 4);
x_159 = lean_ctor_get(x_3, 5);
x_160 = lean_ctor_get(x_3, 6);
x_161 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_162 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_3);
x_163 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_163, 0, x_154);
lean_ctor_set(x_163, 1, x_155);
lean_ctor_set(x_163, 2, x_156);
lean_ctor_set(x_163, 3, x_157);
lean_ctor_set(x_163, 4, x_158);
lean_ctor_set(x_163, 5, x_159);
lean_ctor_set(x_163, 6, x_160);
lean_ctor_set(x_163, 7, x_97);
lean_ctor_set_uint8(x_163, sizeof(void*)*8, x_161);
lean_ctor_set_uint8(x_163, sizeof(void*)*8 + 1, x_162);
x_164 = l_Lean_Elab_Term_getCurrMacroScope(x_163, x_4, x_5, x_6, x_7, x_8, x_101);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_166);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = l_Lean_Meta_mkArrow___rarg___closed__2;
x_171 = l_Lean_addMacroScope(x_168, x_170, x_165);
x_172 = lean_box(0);
x_173 = l_Lean_SourceInfo_inhabited___closed__1;
x_174 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__2;
x_175 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
lean_ctor_set(x_175, 2, x_171);
lean_ctor_set(x_175, 3, x_172);
x_176 = l_Array_empty___closed__1;
x_177 = lean_array_push(x_176, x_175);
x_178 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
lean_inc(x_177);
x_179 = lean_array_push(x_177, x_178);
x_180 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4;
x_181 = lean_array_push(x_179, x_180);
x_182 = lean_array_push(x_181, x_79);
x_183 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
x_185 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_186 = lean_array_push(x_185, x_184);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_37);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_array_push(x_176, x_187);
x_189 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_190 = lean_array_push(x_188, x_189);
x_191 = l_Lean_nullKind___closed__2;
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
x_193 = lean_array_push(x_176, x_192);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_177);
x_195 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__20;
x_196 = lean_array_push(x_195, x_194);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_59);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_array_push(x_176, x_197);
x_199 = lean_array_push(x_198, x_178);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_191);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_array_push(x_193, x_200);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_191);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_array_push(x_176, x_202);
x_204 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4;
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_203);
x_206 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2;
x_207 = lean_array_push(x_206, x_205);
x_208 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2;
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
x_210 = l_Lean_Syntax_getArg(x_209, x_98);
lean_dec(x_209);
x_211 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_210);
x_212 = l_List_map___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__1(x_25, x_211);
lean_dec(x_25);
x_1 = x_212;
x_3 = x_163;
x_9 = x_169;
goto _start;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_214 = lean_ctor_get(x_94, 0);
x_215 = lean_ctor_get(x_94, 1);
x_216 = lean_ctor_get(x_94, 2);
x_217 = lean_ctor_get(x_94, 3);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_94);
x_218 = lean_unsigned_to_nat(1u);
x_219 = lean_nat_add(x_215, x_218);
x_220 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_220, 0, x_214);
lean_ctor_set(x_220, 1, x_219);
lean_ctor_set(x_220, 2, x_216);
lean_ctor_set(x_220, 3, x_217);
x_221 = lean_st_ref_set(x_8, x_220, x_95);
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
lean_dec(x_221);
x_223 = lean_ctor_get(x_3, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_3, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_3, 2);
lean_inc(x_225);
x_226 = lean_ctor_get(x_3, 3);
lean_inc(x_226);
x_227 = lean_ctor_get(x_3, 4);
lean_inc(x_227);
x_228 = lean_ctor_get(x_3, 5);
lean_inc(x_228);
x_229 = lean_ctor_get(x_3, 6);
lean_inc(x_229);
x_230 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_231 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 x_232 = x_3;
} else {
 lean_dec_ref(x_3);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(0, 8, 2);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_223);
lean_ctor_set(x_233, 1, x_224);
lean_ctor_set(x_233, 2, x_225);
lean_ctor_set(x_233, 3, x_226);
lean_ctor_set(x_233, 4, x_227);
lean_ctor_set(x_233, 5, x_228);
lean_ctor_set(x_233, 6, x_229);
lean_ctor_set(x_233, 7, x_215);
lean_ctor_set_uint8(x_233, sizeof(void*)*8, x_230);
lean_ctor_set_uint8(x_233, sizeof(void*)*8 + 1, x_231);
x_234 = l_Lean_Elab_Term_getCurrMacroScope(x_233, x_4, x_5, x_6, x_7, x_8, x_222);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_236);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = l_Lean_Meta_mkArrow___rarg___closed__2;
x_241 = l_Lean_addMacroScope(x_238, x_240, x_235);
x_242 = lean_box(0);
x_243 = l_Lean_SourceInfo_inhabited___closed__1;
x_244 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__2;
x_245 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
lean_ctor_set(x_245, 2, x_241);
lean_ctor_set(x_245, 3, x_242);
x_246 = l_Array_empty___closed__1;
x_247 = lean_array_push(x_246, x_245);
x_248 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
lean_inc(x_247);
x_249 = lean_array_push(x_247, x_248);
x_250 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4;
x_251 = lean_array_push(x_249, x_250);
x_252 = lean_array_push(x_251, x_79);
x_253 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_252);
x_255 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_256 = lean_array_push(x_255, x_254);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_37);
lean_ctor_set(x_257, 1, x_256);
x_258 = lean_array_push(x_246, x_257);
x_259 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_260 = lean_array_push(x_258, x_259);
x_261 = l_Lean_nullKind___closed__2;
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_260);
x_263 = lean_array_push(x_246, x_262);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_247);
x_265 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__20;
x_266 = lean_array_push(x_265, x_264);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_59);
lean_ctor_set(x_267, 1, x_266);
x_268 = lean_array_push(x_246, x_267);
x_269 = lean_array_push(x_268, x_248);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_261);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_array_push(x_263, x_270);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_261);
lean_ctor_set(x_272, 1, x_271);
x_273 = lean_array_push(x_246, x_272);
x_274 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4;
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_273);
x_276 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2;
x_277 = lean_array_push(x_276, x_275);
x_278 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2;
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_277);
x_280 = l_Lean_Syntax_getArg(x_279, x_218);
lean_dec(x_279);
x_281 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_280);
x_282 = l_List_map___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__1(x_25, x_281);
lean_dec(x_25);
x_1 = x_282;
x_3 = x_233;
x_9 = x_239;
goto _start;
}
}
}
}
else
{
lean_object* x_284; 
lean_dec(x_32);
x_284 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_284) == 0)
{
uint8_t x_285; 
x_285 = !lean_is_exclusive(x_284);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_284, 0);
x_287 = l_Lean_Elab_Term_Do_mkAction(x_25, x_286);
lean_ctor_set(x_284, 0, x_287);
return x_284;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_288 = lean_ctor_get(x_284, 0);
x_289 = lean_ctor_get(x_284, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_284);
x_290 = l_Lean_Elab_Term_Do_mkAction(x_25, x_288);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_289);
return x_291;
}
}
else
{
uint8_t x_292; 
lean_dec(x_25);
x_292 = !lean_is_exclusive(x_284);
if (x_292 == 0)
{
return x_284;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_284, 0);
x_294 = lean_ctor_get(x_284, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_284);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
}
else
{
lean_object* x_296; 
lean_dec(x_32);
x_296 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_296) == 0)
{
uint8_t x_297; 
x_297 = !lean_is_exclusive(x_296);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_296, 0);
x_299 = l_Lean_Elab_Term_Do_mkAction(x_25, x_298);
lean_ctor_set(x_296, 0, x_299);
return x_296;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_300 = lean_ctor_get(x_296, 0);
x_301 = lean_ctor_get(x_296, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_296);
x_302 = l_Lean_Elab_Term_Do_mkAction(x_25, x_300);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_301);
return x_303;
}
}
else
{
uint8_t x_304; 
lean_dec(x_25);
x_304 = !lean_is_exclusive(x_296);
if (x_304 == 0)
{
return x_296;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_296, 0);
x_306 = lean_ctor_get(x_296, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_296);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
return x_307;
}
}
}
}
else
{
lean_object* x_308; 
lean_dec(x_32);
x_308 = l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_13);
if (lean_obj_tag(x_308) == 0)
{
uint8_t x_309; 
x_309 = !lean_is_exclusive(x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_310 = lean_ctor_get(x_308, 1);
x_311 = lean_ctor_get(x_308, 0);
lean_dec(x_311);
x_312 = lean_unsigned_to_nat(1u);
x_313 = l_Lean_Syntax_getArg(x_25, x_312);
x_314 = l_Lean_Syntax_isNone(x_313);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_315 = lean_unsigned_to_nat(0u);
x_316 = l_Lean_Syntax_getArg(x_313, x_315);
lean_dec(x_313);
x_317 = l_Lean_Elab_Term_Do_mkReturn(x_25, x_316);
lean_ctor_set(x_308, 0, x_317);
return x_308;
}
else
{
lean_object* x_318; 
lean_dec(x_313);
lean_free_object(x_308);
x_318 = l_Lean_Elab_Term_Do_ToCodeBlock_mkReturnUnit(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_310);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_318;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
x_319 = lean_ctor_get(x_308, 1);
lean_inc(x_319);
lean_dec(x_308);
x_320 = lean_unsigned_to_nat(1u);
x_321 = l_Lean_Syntax_getArg(x_25, x_320);
x_322 = l_Lean_Syntax_isNone(x_321);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_323 = lean_unsigned_to_nat(0u);
x_324 = l_Lean_Syntax_getArg(x_321, x_323);
lean_dec(x_321);
x_325 = l_Lean_Elab_Term_Do_mkReturn(x_25, x_324);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_319);
return x_326;
}
else
{
lean_object* x_327; 
lean_dec(x_321);
x_327 = l_Lean_Elab_Term_Do_ToCodeBlock_mkReturnUnit(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_319);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_327;
}
}
}
else
{
uint8_t x_328; 
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_328 = !lean_is_exclusive(x_308);
if (x_328 == 0)
{
return x_308;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_308, 0);
x_330 = lean_ctor_get(x_308, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_308);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
return x_331;
}
}
}
}
else
{
lean_object* x_332; 
lean_dec(x_32);
x_332 = l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; 
x_333 = lean_ctor_get(x_332, 1);
lean_inc(x_333);
lean_dec(x_332);
x_334 = l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_333);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_13);
if (lean_obj_tag(x_334) == 0)
{
uint8_t x_335; 
x_335 = !lean_is_exclusive(x_334);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; 
x_336 = lean_ctor_get(x_334, 0);
lean_dec(x_336);
x_337 = l_Lean_Elab_Term_Do_mkContinue(x_25);
lean_ctor_set(x_334, 0, x_337);
return x_334;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_334, 1);
lean_inc(x_338);
lean_dec(x_334);
x_339 = l_Lean_Elab_Term_Do_mkContinue(x_25);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_338);
return x_340;
}
}
else
{
uint8_t x_341; 
lean_dec(x_25);
x_341 = !lean_is_exclusive(x_334);
if (x_341 == 0)
{
return x_334;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_334, 0);
x_343 = lean_ctor_get(x_334, 1);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_334);
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
return x_344;
}
}
}
else
{
uint8_t x_345; 
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_345 = !lean_is_exclusive(x_332);
if (x_345 == 0)
{
return x_332;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_332, 0);
x_347 = lean_ctor_get(x_332, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_332);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
return x_348;
}
}
}
}
else
{
lean_object* x_349; 
lean_dec(x_32);
x_349 = l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; 
x_350 = lean_ctor_get(x_349, 1);
lean_inc(x_350);
lean_dec(x_349);
x_351 = l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_350);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_13);
if (lean_obj_tag(x_351) == 0)
{
uint8_t x_352; 
x_352 = !lean_is_exclusive(x_351);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; 
x_353 = lean_ctor_get(x_351, 0);
lean_dec(x_353);
x_354 = l_Lean_Elab_Term_Do_mkBreak(x_25);
lean_ctor_set(x_351, 0, x_354);
return x_351;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_351, 1);
lean_inc(x_355);
lean_dec(x_351);
x_356 = l_Lean_Elab_Term_Do_mkBreak(x_25);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_355);
return x_357;
}
}
else
{
uint8_t x_358; 
lean_dec(x_25);
x_358 = !lean_is_exclusive(x_351);
if (x_358 == 0)
{
return x_351;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_351, 0);
x_360 = lean_ctor_get(x_351, 1);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_351);
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
return x_361;
}
}
}
else
{
uint8_t x_362; 
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_362 = !lean_is_exclusive(x_349);
if (x_362 == 0)
{
return x_349;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_349, 0);
x_364 = lean_ctor_get(x_349, 1);
lean_inc(x_364);
lean_inc(x_363);
lean_dec(x_349);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
return x_365;
}
}
}
}
else
{
lean_object* x_366; lean_object* x_367; 
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_13);
x_366 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__22;
x_367 = l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(x_366, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_367;
}
}
else
{
lean_object* x_368; lean_object* x_369; 
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_13);
x_368 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__22;
x_369 = l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(x_368, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_369;
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_1171; 
lean_dec(x_32);
x_370 = lean_unsigned_to_nat(1u);
x_371 = l_Lean_Syntax_getArg(x_25, x_370);
x_372 = lean_unsigned_to_nat(3u);
x_373 = l_Lean_Syntax_getArg(x_25, x_372);
x_374 = lean_unsigned_to_nat(5u);
x_375 = l_Lean_Syntax_getArg(x_25, x_374);
x_376 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_375);
x_1171 = l_Lean_Syntax_isIdent(x_371);
if (x_1171 == 0)
{
lean_object* x_1172; 
x_1172 = l_Array_empty___closed__1;
x_377 = x_1172;
goto block_1170;
}
else
{
lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; 
x_1173 = l_Lean_Syntax_getId(x_371);
x_1174 = l_Lean_mkOptionalNode___closed__2;
x_1175 = lean_array_push(x_1174, x_1173);
x_377 = x_1175;
goto block_1170;
}
block_1170:
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; 
x_378 = lean_st_ref_take(x_8, x_23);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_381 = !lean_is_exclusive(x_379);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; 
x_382 = lean_ctor_get(x_379, 1);
x_383 = lean_nat_add(x_382, x_370);
lean_ctor_set(x_379, 1, x_383);
x_384 = lean_st_ref_set(x_8, x_379, x_380);
x_385 = lean_ctor_get(x_384, 1);
lean_inc(x_385);
lean_dec(x_384);
x_386 = !lean_is_exclusive(x_3);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; lean_object* x_395; 
x_387 = lean_ctor_get(x_3, 7);
lean_dec(x_387);
lean_ctor_set(x_3, 7, x_382);
x_388 = lean_ctor_get(x_2, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_2, 1);
lean_inc(x_389);
x_390 = lean_ctor_get(x_2, 2);
lean_inc(x_390);
x_391 = lean_unsigned_to_nat(0u);
x_392 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_377, x_377, x_391, x_390);
lean_dec(x_377);
x_393 = 1;
x_394 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_394, 0, x_388);
lean_ctor_set(x_394, 1, x_389);
lean_ctor_set(x_394, 2, x_392);
lean_ctor_set_uint8(x_394, sizeof(void*)*3, x_393);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_395 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_376, x_394, x_3, x_4, x_5, x_6, x_7, x_8, x_385);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
lean_inc(x_7);
lean_inc(x_2);
x_398 = l_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm(x_371, x_396, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_397);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; uint8_t x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; uint8_t x_623; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = lean_ctor_get_uint8(x_399, sizeof(void*)*2);
x_402 = lean_ctor_get(x_399, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_399, 1);
lean_inc(x_403);
lean_dec(x_399);
x_599 = x_402;
x_600 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__2(x_25, x_391, x_599);
x_601 = x_600;
x_602 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_400);
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_602, 1);
lean_inc(x_604);
lean_dec(x_602);
x_605 = lean_st_ref_get(x_8, x_604);
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_605, 1);
lean_inc(x_607);
lean_dec(x_605);
x_608 = lean_ctor_get(x_606, 0);
lean_inc(x_608);
lean_dec(x_606);
x_609 = lean_st_ref_get(x_8, x_607);
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
lean_dec(x_609);
x_612 = lean_ctor_get(x_610, 1);
lean_inc(x_612);
lean_dec(x_610);
lean_inc(x_608);
x_613 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_5__expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_613, 0, x_608);
x_614 = x_613;
x_615 = lean_environment_main_module(x_608);
x_616 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_616, 0, x_614);
lean_ctor_set(x_616, 1, x_615);
lean_ctor_set(x_616, 2, x_603);
lean_ctor_set(x_616, 3, x_16);
lean_ctor_set(x_616, 4, x_17);
x_617 = l___private_Lean_Elab_Do_12__mkTuple(x_25, x_601, x_616, x_612);
lean_dec(x_601);
lean_dec(x_25);
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_617, 1);
lean_inc(x_619);
lean_dec(x_617);
x_620 = lean_st_ref_take(x_8, x_611);
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_620, 1);
lean_inc(x_622);
lean_dec(x_620);
x_623 = !lean_is_exclusive(x_621);
if (x_623 == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_624 = lean_ctor_get(x_621, 1);
lean_dec(x_624);
lean_ctor_set(x_621, 1, x_619);
x_625 = lean_st_ref_set(x_8, x_621, x_622);
x_626 = lean_ctor_get(x_625, 1);
lean_inc(x_626);
lean_dec(x_625);
x_404 = x_618;
x_405 = x_626;
goto block_598;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_627 = lean_ctor_get(x_621, 0);
x_628 = lean_ctor_get(x_621, 2);
x_629 = lean_ctor_get(x_621, 3);
lean_inc(x_629);
lean_inc(x_628);
lean_inc(x_627);
lean_dec(x_621);
x_630 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_630, 0, x_627);
lean_ctor_set(x_630, 1, x_619);
lean_ctor_set(x_630, 2, x_628);
lean_ctor_set(x_630, 3, x_629);
x_631 = lean_st_ref_set(x_8, x_630, x_622);
x_632 = lean_ctor_get(x_631, 1);
lean_inc(x_632);
lean_dec(x_631);
x_404 = x_618;
x_405 = x_632;
goto block_598;
}
block_598:
{
lean_object* x_406; lean_object* x_407; 
if (x_401 == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_413 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_405);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec(x_413);
x_416 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_415);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec(x_416);
x_419 = l_Array_empty___closed__1;
x_420 = lean_array_push(x_419, x_373);
x_421 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__23;
x_422 = lean_array_push(x_420, x_421);
x_423 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__27;
x_424 = l_Lean_addMacroScope(x_417, x_423, x_414);
x_425 = lean_box(0);
x_426 = l_Lean_SourceInfo_inhabited___closed__1;
x_427 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__26;
x_428 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_427);
lean_ctor_set(x_428, 2, x_424);
lean_ctor_set(x_428, 3, x_425);
x_429 = lean_array_push(x_422, x_428);
x_430 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__13;
x_431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_429);
x_432 = lean_array_push(x_419, x_431);
lean_inc(x_404);
x_433 = lean_array_push(x_419, x_404);
x_434 = lean_array_push(x_419, x_371);
x_435 = lean_array_push(x_434, x_404);
x_436 = l_Lean_nullKind___closed__2;
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_435);
x_438 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
x_439 = lean_array_push(x_438, x_437);
x_440 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_441 = lean_array_push(x_439, x_440);
x_442 = lean_array_push(x_441, x_403);
x_443 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
x_444 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_442);
lean_inc(x_433);
x_445 = lean_array_push(x_433, x_444);
x_446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_446, 0, x_436);
lean_ctor_set(x_446, 1, x_445);
x_447 = lean_array_push(x_432, x_446);
x_448 = l_Lean_mkAppStx___closed__8;
x_449 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_447);
x_450 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_418);
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
lean_dec(x_450);
x_453 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_452);
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
lean_dec(x_453);
x_456 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__30;
x_457 = l_Lean_addMacroScope(x_454, x_456, x_451);
x_458 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__29;
x_459 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_459, 0, x_426);
lean_ctor_set(x_459, 1, x_458);
lean_ctor_set(x_459, 2, x_457);
lean_ctor_set(x_459, 3, x_425);
lean_inc(x_459);
x_460 = lean_array_push(x_419, x_459);
x_461 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_462 = lean_array_push(x_460, x_461);
x_463 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4;
x_464 = lean_array_push(x_462, x_463);
x_465 = lean_array_push(x_464, x_449);
x_466 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
x_467 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_467, 0, x_466);
lean_ctor_set(x_467, 1, x_465);
x_468 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_469 = lean_array_push(x_468, x_467);
x_470 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_470, 0, x_37);
lean_ctor_set(x_470, 1, x_469);
x_471 = lean_array_push(x_419, x_470);
x_472 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_473 = lean_array_push(x_471, x_472);
x_474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_474, 0, x_436);
lean_ctor_set(x_474, 1, x_473);
x_475 = lean_array_push(x_419, x_474);
x_476 = lean_array_push(x_433, x_461);
x_477 = lean_array_push(x_476, x_461);
x_478 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_479 = lean_array_push(x_477, x_478);
x_480 = lean_array_push(x_479, x_459);
x_481 = l_Lean_Elab_Term_elabLetDeclCore___closed__2;
x_482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_482, 0, x_481);
lean_ctor_set(x_482, 1, x_480);
x_483 = lean_array_push(x_419, x_482);
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_39);
lean_ctor_set(x_484, 1, x_483);
x_485 = lean_array_push(x_419, x_484);
x_486 = lean_array_push(x_485, x_461);
x_487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_487, 0, x_436);
lean_ctor_set(x_487, 1, x_486);
x_488 = lean_array_push(x_475, x_487);
x_489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_489, 0, x_436);
lean_ctor_set(x_489, 1, x_488);
x_490 = lean_array_push(x_419, x_489);
x_491 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4;
x_492 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_492, 0, x_491);
lean_ctor_set(x_492, 1, x_490);
x_493 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2;
x_494 = lean_array_push(x_493, x_492);
x_495 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2;
x_496 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_496, 0, x_495);
lean_ctor_set(x_496, 1, x_494);
x_406 = x_496;
x_407 = x_455;
goto block_412;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_497 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_405);
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
lean_dec(x_497);
x_500 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_499);
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
x_503 = l_Array_empty___closed__1;
x_504 = lean_array_push(x_503, x_373);
x_505 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__23;
x_506 = lean_array_push(x_504, x_505);
x_507 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__34;
x_508 = l_Lean_addMacroScope(x_501, x_507, x_498);
x_509 = lean_box(0);
x_510 = l_Lean_SourceInfo_inhabited___closed__1;
x_511 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__33;
x_512 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_512, 0, x_510);
lean_ctor_set(x_512, 1, x_511);
lean_ctor_set(x_512, 2, x_508);
lean_ctor_set(x_512, 3, x_509);
x_513 = lean_array_push(x_506, x_512);
x_514 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__13;
x_515 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_515, 0, x_514);
lean_ctor_set(x_515, 1, x_513);
x_516 = lean_array_push(x_503, x_515);
lean_inc(x_404);
x_517 = lean_array_push(x_503, x_404);
x_518 = lean_array_push(x_503, x_371);
x_519 = lean_array_push(x_518, x_404);
x_520 = l_Lean_nullKind___closed__2;
x_521 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_521, 0, x_520);
lean_ctor_set(x_521, 1, x_519);
x_522 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
x_523 = lean_array_push(x_522, x_521);
x_524 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_525 = lean_array_push(x_523, x_524);
x_526 = lean_array_push(x_525, x_403);
x_527 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
x_528 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_526);
lean_inc(x_517);
x_529 = lean_array_push(x_517, x_528);
x_530 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_530, 0, x_520);
lean_ctor_set(x_530, 1, x_529);
x_531 = lean_array_push(x_516, x_530);
x_532 = l_Lean_mkAppStx___closed__8;
x_533 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_533, 0, x_532);
lean_ctor_set(x_533, 1, x_531);
x_534 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_502);
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
lean_dec(x_534);
x_537 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_536);
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_537, 1);
lean_inc(x_539);
lean_dec(x_537);
x_540 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__30;
x_541 = l_Lean_addMacroScope(x_538, x_540, x_535);
x_542 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__29;
x_543 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_543, 0, x_510);
lean_ctor_set(x_543, 1, x_542);
lean_ctor_set(x_543, 2, x_541);
lean_ctor_set(x_543, 3, x_509);
x_544 = lean_array_push(x_503, x_543);
x_545 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
lean_inc(x_544);
x_546 = lean_array_push(x_544, x_545);
x_547 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4;
x_548 = lean_array_push(x_546, x_547);
x_549 = lean_array_push(x_548, x_533);
x_550 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
x_551 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_551, 0, x_550);
lean_ctor_set(x_551, 1, x_549);
x_552 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_553 = lean_array_push(x_552, x_551);
x_554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_554, 0, x_37);
lean_ctor_set(x_554, 1, x_553);
x_555 = lean_array_push(x_503, x_554);
x_556 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_557 = lean_array_push(x_555, x_556);
x_558 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_558, 0, x_520);
lean_ctor_set(x_558, 1, x_557);
x_559 = lean_array_push(x_503, x_558);
x_560 = lean_array_push(x_517, x_545);
x_561 = lean_array_push(x_560, x_545);
x_562 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_563 = lean_array_push(x_561, x_562);
x_564 = lean_array_push(x_544, x_505);
x_565 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__38;
lean_inc(x_564);
x_566 = lean_array_push(x_564, x_565);
x_567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_567, 0, x_514);
lean_ctor_set(x_567, 1, x_566);
x_568 = lean_array_push(x_563, x_567);
x_569 = l_Lean_Elab_Term_elabLetDeclCore___closed__2;
x_570 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_570, 0, x_569);
lean_ctor_set(x_570, 1, x_568);
x_571 = lean_array_push(x_503, x_570);
x_572 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_572, 0, x_39);
lean_ctor_set(x_572, 1, x_571);
x_573 = lean_array_push(x_503, x_572);
x_574 = lean_array_push(x_573, x_556);
x_575 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_575, 0, x_520);
lean_ctor_set(x_575, 1, x_574);
x_576 = lean_array_push(x_559, x_575);
x_577 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__42;
x_578 = lean_array_push(x_564, x_577);
x_579 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_579, 0, x_514);
lean_ctor_set(x_579, 1, x_578);
x_580 = lean_array_push(x_503, x_579);
x_581 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_581, 0, x_520);
lean_ctor_set(x_581, 1, x_580);
x_582 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__20;
x_583 = lean_array_push(x_582, x_581);
x_584 = l___private_Lean_Elab_Do_9__expandDoIf___closed__2;
x_585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_585, 0, x_584);
lean_ctor_set(x_585, 1, x_583);
x_586 = lean_array_push(x_503, x_585);
x_587 = lean_array_push(x_586, x_545);
x_588 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_588, 0, x_520);
lean_ctor_set(x_588, 1, x_587);
x_589 = lean_array_push(x_576, x_588);
x_590 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_590, 0, x_520);
lean_ctor_set(x_590, 1, x_589);
x_591 = lean_array_push(x_503, x_590);
x_592 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4;
x_593 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_593, 0, x_592);
lean_ctor_set(x_593, 1, x_591);
x_594 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2;
x_595 = lean_array_push(x_594, x_593);
x_596 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2;
x_597 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_597, 0, x_596);
lean_ctor_set(x_597, 1, x_595);
x_406 = x_597;
x_407 = x_539;
goto block_412;
}
block_412:
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = l_Lean_Syntax_getArg(x_406, x_370);
lean_dec(x_406);
x_409 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_408);
x_410 = l_List_append___rarg(x_409, x_13);
x_1 = x_410;
x_9 = x_407;
goto _start;
}
}
}
else
{
uint8_t x_633; 
lean_dec(x_3);
lean_dec(x_373);
lean_dec(x_371);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_633 = !lean_is_exclusive(x_398);
if (x_633 == 0)
{
return x_398;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_634 = lean_ctor_get(x_398, 0);
x_635 = lean_ctor_get(x_398, 1);
lean_inc(x_635);
lean_inc(x_634);
lean_dec(x_398);
x_636 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_636, 0, x_634);
lean_ctor_set(x_636, 1, x_635);
return x_636;
}
}
}
else
{
uint8_t x_637; 
lean_dec(x_3);
lean_dec(x_373);
lean_dec(x_371);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_637 = !lean_is_exclusive(x_395);
if (x_637 == 0)
{
return x_395;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_638 = lean_ctor_get(x_395, 0);
x_639 = lean_ctor_get(x_395, 1);
lean_inc(x_639);
lean_inc(x_638);
lean_dec(x_395);
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_638);
lean_ctor_set(x_640, 1, x_639);
return x_640;
}
}
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; uint8_t x_648; uint8_t x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; uint8_t x_656; lean_object* x_657; lean_object* x_658; 
x_641 = lean_ctor_get(x_3, 0);
x_642 = lean_ctor_get(x_3, 1);
x_643 = lean_ctor_get(x_3, 2);
x_644 = lean_ctor_get(x_3, 3);
x_645 = lean_ctor_get(x_3, 4);
x_646 = lean_ctor_get(x_3, 5);
x_647 = lean_ctor_get(x_3, 6);
x_648 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_649 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
lean_inc(x_647);
lean_inc(x_646);
lean_inc(x_645);
lean_inc(x_644);
lean_inc(x_643);
lean_inc(x_642);
lean_inc(x_641);
lean_dec(x_3);
x_650 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_650, 0, x_641);
lean_ctor_set(x_650, 1, x_642);
lean_ctor_set(x_650, 2, x_643);
lean_ctor_set(x_650, 3, x_644);
lean_ctor_set(x_650, 4, x_645);
lean_ctor_set(x_650, 5, x_646);
lean_ctor_set(x_650, 6, x_647);
lean_ctor_set(x_650, 7, x_382);
lean_ctor_set_uint8(x_650, sizeof(void*)*8, x_648);
lean_ctor_set_uint8(x_650, sizeof(void*)*8 + 1, x_649);
x_651 = lean_ctor_get(x_2, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_2, 1);
lean_inc(x_652);
x_653 = lean_ctor_get(x_2, 2);
lean_inc(x_653);
x_654 = lean_unsigned_to_nat(0u);
x_655 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_377, x_377, x_654, x_653);
lean_dec(x_377);
x_656 = 1;
x_657 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_657, 0, x_651);
lean_ctor_set(x_657, 1, x_652);
lean_ctor_set(x_657, 2, x_655);
lean_ctor_set_uint8(x_657, sizeof(void*)*3, x_656);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_650);
x_658 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_376, x_657, x_650, x_4, x_5, x_6, x_7, x_8, x_385);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_659 = lean_ctor_get(x_658, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_658, 1);
lean_inc(x_660);
lean_dec(x_658);
lean_inc(x_7);
lean_inc(x_2);
x_661 = l_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm(x_371, x_659, x_2, x_650, x_4, x_5, x_6, x_7, x_8, x_660);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; lean_object* x_663; uint8_t x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; 
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_661, 1);
lean_inc(x_663);
lean_dec(x_661);
x_664 = lean_ctor_get_uint8(x_662, sizeof(void*)*2);
x_665 = lean_ctor_get(x_662, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_662, 1);
lean_inc(x_666);
lean_dec(x_662);
x_862 = x_665;
x_863 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__2(x_25, x_654, x_862);
x_864 = x_863;
x_865 = l_Lean_Elab_Term_getCurrMacroScope(x_650, x_4, x_5, x_6, x_7, x_8, x_663);
x_866 = lean_ctor_get(x_865, 0);
lean_inc(x_866);
x_867 = lean_ctor_get(x_865, 1);
lean_inc(x_867);
lean_dec(x_865);
x_868 = lean_st_ref_get(x_8, x_867);
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_868, 1);
lean_inc(x_870);
lean_dec(x_868);
x_871 = lean_ctor_get(x_869, 0);
lean_inc(x_871);
lean_dec(x_869);
x_872 = lean_st_ref_get(x_8, x_870);
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_872, 1);
lean_inc(x_874);
lean_dec(x_872);
x_875 = lean_ctor_get(x_873, 1);
lean_inc(x_875);
lean_dec(x_873);
lean_inc(x_871);
x_876 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_5__expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_876, 0, x_871);
x_877 = x_876;
x_878 = lean_environment_main_module(x_871);
x_879 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_879, 0, x_877);
lean_ctor_set(x_879, 1, x_878);
lean_ctor_set(x_879, 2, x_866);
lean_ctor_set(x_879, 3, x_16);
lean_ctor_set(x_879, 4, x_17);
x_880 = l___private_Lean_Elab_Do_12__mkTuple(x_25, x_864, x_879, x_875);
lean_dec(x_864);
lean_dec(x_25);
x_881 = lean_ctor_get(x_880, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_880, 1);
lean_inc(x_882);
lean_dec(x_880);
x_883 = lean_st_ref_take(x_8, x_874);
x_884 = lean_ctor_get(x_883, 0);
lean_inc(x_884);
x_885 = lean_ctor_get(x_883, 1);
lean_inc(x_885);
lean_dec(x_883);
x_886 = lean_ctor_get(x_884, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_884, 2);
lean_inc(x_887);
x_888 = lean_ctor_get(x_884, 3);
lean_inc(x_888);
if (lean_is_exclusive(x_884)) {
 lean_ctor_release(x_884, 0);
 lean_ctor_release(x_884, 1);
 lean_ctor_release(x_884, 2);
 lean_ctor_release(x_884, 3);
 x_889 = x_884;
} else {
 lean_dec_ref(x_884);
 x_889 = lean_box(0);
}
if (lean_is_scalar(x_889)) {
 x_890 = lean_alloc_ctor(0, 4, 0);
} else {
 x_890 = x_889;
}
lean_ctor_set(x_890, 0, x_886);
lean_ctor_set(x_890, 1, x_882);
lean_ctor_set(x_890, 2, x_887);
lean_ctor_set(x_890, 3, x_888);
x_891 = lean_st_ref_set(x_8, x_890, x_885);
x_892 = lean_ctor_get(x_891, 1);
lean_inc(x_892);
lean_dec(x_891);
x_667 = x_881;
x_668 = x_892;
goto block_861;
block_861:
{
lean_object* x_669; lean_object* x_670; 
if (x_664 == 0)
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; 
x_676 = l_Lean_Elab_Term_getCurrMacroScope(x_650, x_4, x_5, x_6, x_7, x_8, x_668);
x_677 = lean_ctor_get(x_676, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_676, 1);
lean_inc(x_678);
lean_dec(x_676);
x_679 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_678);
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_679, 1);
lean_inc(x_681);
lean_dec(x_679);
x_682 = l_Array_empty___closed__1;
x_683 = lean_array_push(x_682, x_373);
x_684 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__23;
x_685 = lean_array_push(x_683, x_684);
x_686 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__27;
x_687 = l_Lean_addMacroScope(x_680, x_686, x_677);
x_688 = lean_box(0);
x_689 = l_Lean_SourceInfo_inhabited___closed__1;
x_690 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__26;
x_691 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_691, 0, x_689);
lean_ctor_set(x_691, 1, x_690);
lean_ctor_set(x_691, 2, x_687);
lean_ctor_set(x_691, 3, x_688);
x_692 = lean_array_push(x_685, x_691);
x_693 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__13;
x_694 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_694, 0, x_693);
lean_ctor_set(x_694, 1, x_692);
x_695 = lean_array_push(x_682, x_694);
lean_inc(x_667);
x_696 = lean_array_push(x_682, x_667);
x_697 = lean_array_push(x_682, x_371);
x_698 = lean_array_push(x_697, x_667);
x_699 = l_Lean_nullKind___closed__2;
x_700 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_700, 0, x_699);
lean_ctor_set(x_700, 1, x_698);
x_701 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
x_702 = lean_array_push(x_701, x_700);
x_703 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_704 = lean_array_push(x_702, x_703);
x_705 = lean_array_push(x_704, x_666);
x_706 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
x_707 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_707, 0, x_706);
lean_ctor_set(x_707, 1, x_705);
lean_inc(x_696);
x_708 = lean_array_push(x_696, x_707);
x_709 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_709, 0, x_699);
lean_ctor_set(x_709, 1, x_708);
x_710 = lean_array_push(x_695, x_709);
x_711 = l_Lean_mkAppStx___closed__8;
x_712 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_712, 0, x_711);
lean_ctor_set(x_712, 1, x_710);
x_713 = l_Lean_Elab_Term_getCurrMacroScope(x_650, x_4, x_5, x_6, x_7, x_8, x_681);
x_714 = lean_ctor_get(x_713, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_713, 1);
lean_inc(x_715);
lean_dec(x_713);
x_716 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_715);
x_717 = lean_ctor_get(x_716, 0);
lean_inc(x_717);
x_718 = lean_ctor_get(x_716, 1);
lean_inc(x_718);
lean_dec(x_716);
x_719 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__30;
x_720 = l_Lean_addMacroScope(x_717, x_719, x_714);
x_721 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__29;
x_722 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_722, 0, x_689);
lean_ctor_set(x_722, 1, x_721);
lean_ctor_set(x_722, 2, x_720);
lean_ctor_set(x_722, 3, x_688);
lean_inc(x_722);
x_723 = lean_array_push(x_682, x_722);
x_724 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_725 = lean_array_push(x_723, x_724);
x_726 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4;
x_727 = lean_array_push(x_725, x_726);
x_728 = lean_array_push(x_727, x_712);
x_729 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
x_730 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_730, 0, x_729);
lean_ctor_set(x_730, 1, x_728);
x_731 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_732 = lean_array_push(x_731, x_730);
x_733 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_733, 0, x_37);
lean_ctor_set(x_733, 1, x_732);
x_734 = lean_array_push(x_682, x_733);
x_735 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_736 = lean_array_push(x_734, x_735);
x_737 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_737, 0, x_699);
lean_ctor_set(x_737, 1, x_736);
x_738 = lean_array_push(x_682, x_737);
x_739 = lean_array_push(x_696, x_724);
x_740 = lean_array_push(x_739, x_724);
x_741 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_742 = lean_array_push(x_740, x_741);
x_743 = lean_array_push(x_742, x_722);
x_744 = l_Lean_Elab_Term_elabLetDeclCore___closed__2;
x_745 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_745, 0, x_744);
lean_ctor_set(x_745, 1, x_743);
x_746 = lean_array_push(x_682, x_745);
x_747 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_747, 0, x_39);
lean_ctor_set(x_747, 1, x_746);
x_748 = lean_array_push(x_682, x_747);
x_749 = lean_array_push(x_748, x_724);
x_750 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_750, 0, x_699);
lean_ctor_set(x_750, 1, x_749);
x_751 = lean_array_push(x_738, x_750);
x_752 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_752, 0, x_699);
lean_ctor_set(x_752, 1, x_751);
x_753 = lean_array_push(x_682, x_752);
x_754 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4;
x_755 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_755, 0, x_754);
lean_ctor_set(x_755, 1, x_753);
x_756 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2;
x_757 = lean_array_push(x_756, x_755);
x_758 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2;
x_759 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_759, 0, x_758);
lean_ctor_set(x_759, 1, x_757);
x_669 = x_759;
x_670 = x_718;
goto block_675;
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; 
x_760 = l_Lean_Elab_Term_getCurrMacroScope(x_650, x_4, x_5, x_6, x_7, x_8, x_668);
x_761 = lean_ctor_get(x_760, 0);
lean_inc(x_761);
x_762 = lean_ctor_get(x_760, 1);
lean_inc(x_762);
lean_dec(x_760);
x_763 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_762);
x_764 = lean_ctor_get(x_763, 0);
lean_inc(x_764);
x_765 = lean_ctor_get(x_763, 1);
lean_inc(x_765);
lean_dec(x_763);
x_766 = l_Array_empty___closed__1;
x_767 = lean_array_push(x_766, x_373);
x_768 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__23;
x_769 = lean_array_push(x_767, x_768);
x_770 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__34;
x_771 = l_Lean_addMacroScope(x_764, x_770, x_761);
x_772 = lean_box(0);
x_773 = l_Lean_SourceInfo_inhabited___closed__1;
x_774 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__33;
x_775 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_775, 0, x_773);
lean_ctor_set(x_775, 1, x_774);
lean_ctor_set(x_775, 2, x_771);
lean_ctor_set(x_775, 3, x_772);
x_776 = lean_array_push(x_769, x_775);
x_777 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__13;
x_778 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_778, 0, x_777);
lean_ctor_set(x_778, 1, x_776);
x_779 = lean_array_push(x_766, x_778);
lean_inc(x_667);
x_780 = lean_array_push(x_766, x_667);
x_781 = lean_array_push(x_766, x_371);
x_782 = lean_array_push(x_781, x_667);
x_783 = l_Lean_nullKind___closed__2;
x_784 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_784, 0, x_783);
lean_ctor_set(x_784, 1, x_782);
x_785 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
x_786 = lean_array_push(x_785, x_784);
x_787 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_788 = lean_array_push(x_786, x_787);
x_789 = lean_array_push(x_788, x_666);
x_790 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
x_791 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_791, 0, x_790);
lean_ctor_set(x_791, 1, x_789);
lean_inc(x_780);
x_792 = lean_array_push(x_780, x_791);
x_793 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_793, 0, x_783);
lean_ctor_set(x_793, 1, x_792);
x_794 = lean_array_push(x_779, x_793);
x_795 = l_Lean_mkAppStx___closed__8;
x_796 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_796, 0, x_795);
lean_ctor_set(x_796, 1, x_794);
x_797 = l_Lean_Elab_Term_getCurrMacroScope(x_650, x_4, x_5, x_6, x_7, x_8, x_765);
x_798 = lean_ctor_get(x_797, 0);
lean_inc(x_798);
x_799 = lean_ctor_get(x_797, 1);
lean_inc(x_799);
lean_dec(x_797);
x_800 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_799);
x_801 = lean_ctor_get(x_800, 0);
lean_inc(x_801);
x_802 = lean_ctor_get(x_800, 1);
lean_inc(x_802);
lean_dec(x_800);
x_803 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__30;
x_804 = l_Lean_addMacroScope(x_801, x_803, x_798);
x_805 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__29;
x_806 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_806, 0, x_773);
lean_ctor_set(x_806, 1, x_805);
lean_ctor_set(x_806, 2, x_804);
lean_ctor_set(x_806, 3, x_772);
x_807 = lean_array_push(x_766, x_806);
x_808 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
lean_inc(x_807);
x_809 = lean_array_push(x_807, x_808);
x_810 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4;
x_811 = lean_array_push(x_809, x_810);
x_812 = lean_array_push(x_811, x_796);
x_813 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
x_814 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_814, 0, x_813);
lean_ctor_set(x_814, 1, x_812);
x_815 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_816 = lean_array_push(x_815, x_814);
x_817 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_817, 0, x_37);
lean_ctor_set(x_817, 1, x_816);
x_818 = lean_array_push(x_766, x_817);
x_819 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_820 = lean_array_push(x_818, x_819);
x_821 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_821, 0, x_783);
lean_ctor_set(x_821, 1, x_820);
x_822 = lean_array_push(x_766, x_821);
x_823 = lean_array_push(x_780, x_808);
x_824 = lean_array_push(x_823, x_808);
x_825 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_826 = lean_array_push(x_824, x_825);
x_827 = lean_array_push(x_807, x_768);
x_828 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__38;
lean_inc(x_827);
x_829 = lean_array_push(x_827, x_828);
x_830 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_830, 0, x_777);
lean_ctor_set(x_830, 1, x_829);
x_831 = lean_array_push(x_826, x_830);
x_832 = l_Lean_Elab_Term_elabLetDeclCore___closed__2;
x_833 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_833, 0, x_832);
lean_ctor_set(x_833, 1, x_831);
x_834 = lean_array_push(x_766, x_833);
x_835 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_835, 0, x_39);
lean_ctor_set(x_835, 1, x_834);
x_836 = lean_array_push(x_766, x_835);
x_837 = lean_array_push(x_836, x_819);
x_838 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_838, 0, x_783);
lean_ctor_set(x_838, 1, x_837);
x_839 = lean_array_push(x_822, x_838);
x_840 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__42;
x_841 = lean_array_push(x_827, x_840);
x_842 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_842, 0, x_777);
lean_ctor_set(x_842, 1, x_841);
x_843 = lean_array_push(x_766, x_842);
x_844 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_844, 0, x_783);
lean_ctor_set(x_844, 1, x_843);
x_845 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__20;
x_846 = lean_array_push(x_845, x_844);
x_847 = l___private_Lean_Elab_Do_9__expandDoIf___closed__2;
x_848 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_848, 0, x_847);
lean_ctor_set(x_848, 1, x_846);
x_849 = lean_array_push(x_766, x_848);
x_850 = lean_array_push(x_849, x_808);
x_851 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_851, 0, x_783);
lean_ctor_set(x_851, 1, x_850);
x_852 = lean_array_push(x_839, x_851);
x_853 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_853, 0, x_783);
lean_ctor_set(x_853, 1, x_852);
x_854 = lean_array_push(x_766, x_853);
x_855 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4;
x_856 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_856, 0, x_855);
lean_ctor_set(x_856, 1, x_854);
x_857 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2;
x_858 = lean_array_push(x_857, x_856);
x_859 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2;
x_860 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_860, 0, x_859);
lean_ctor_set(x_860, 1, x_858);
x_669 = x_860;
x_670 = x_802;
goto block_675;
}
block_675:
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_671 = l_Lean_Syntax_getArg(x_669, x_370);
lean_dec(x_669);
x_672 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_671);
x_673 = l_List_append___rarg(x_672, x_13);
x_1 = x_673;
x_3 = x_650;
x_9 = x_670;
goto _start;
}
}
}
else
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; 
lean_dec(x_650);
lean_dec(x_373);
lean_dec(x_371);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_893 = lean_ctor_get(x_661, 0);
lean_inc(x_893);
x_894 = lean_ctor_get(x_661, 1);
lean_inc(x_894);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 x_895 = x_661;
} else {
 lean_dec_ref(x_661);
 x_895 = lean_box(0);
}
if (lean_is_scalar(x_895)) {
 x_896 = lean_alloc_ctor(1, 2, 0);
} else {
 x_896 = x_895;
}
lean_ctor_set(x_896, 0, x_893);
lean_ctor_set(x_896, 1, x_894);
return x_896;
}
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; 
lean_dec(x_650);
lean_dec(x_373);
lean_dec(x_371);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_897 = lean_ctor_get(x_658, 0);
lean_inc(x_897);
x_898 = lean_ctor_get(x_658, 1);
lean_inc(x_898);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 lean_ctor_release(x_658, 1);
 x_899 = x_658;
} else {
 lean_dec_ref(x_658);
 x_899 = lean_box(0);
}
if (lean_is_scalar(x_899)) {
 x_900 = lean_alloc_ctor(1, 2, 0);
} else {
 x_900 = x_899;
}
lean_ctor_set(x_900, 0, x_897);
lean_ctor_set(x_900, 1, x_898);
return x_900;
}
}
}
else
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; uint8_t x_916; uint8_t x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; uint8_t x_925; lean_object* x_926; lean_object* x_927; 
x_901 = lean_ctor_get(x_379, 0);
x_902 = lean_ctor_get(x_379, 1);
x_903 = lean_ctor_get(x_379, 2);
x_904 = lean_ctor_get(x_379, 3);
lean_inc(x_904);
lean_inc(x_903);
lean_inc(x_902);
lean_inc(x_901);
lean_dec(x_379);
x_905 = lean_nat_add(x_902, x_370);
x_906 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_906, 0, x_901);
lean_ctor_set(x_906, 1, x_905);
lean_ctor_set(x_906, 2, x_903);
lean_ctor_set(x_906, 3, x_904);
x_907 = lean_st_ref_set(x_8, x_906, x_380);
x_908 = lean_ctor_get(x_907, 1);
lean_inc(x_908);
lean_dec(x_907);
x_909 = lean_ctor_get(x_3, 0);
lean_inc(x_909);
x_910 = lean_ctor_get(x_3, 1);
lean_inc(x_910);
x_911 = lean_ctor_get(x_3, 2);
lean_inc(x_911);
x_912 = lean_ctor_get(x_3, 3);
lean_inc(x_912);
x_913 = lean_ctor_get(x_3, 4);
lean_inc(x_913);
x_914 = lean_ctor_get(x_3, 5);
lean_inc(x_914);
x_915 = lean_ctor_get(x_3, 6);
lean_inc(x_915);
x_916 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_917 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 x_918 = x_3;
} else {
 lean_dec_ref(x_3);
 x_918 = lean_box(0);
}
if (lean_is_scalar(x_918)) {
 x_919 = lean_alloc_ctor(0, 8, 2);
} else {
 x_919 = x_918;
}
lean_ctor_set(x_919, 0, x_909);
lean_ctor_set(x_919, 1, x_910);
lean_ctor_set(x_919, 2, x_911);
lean_ctor_set(x_919, 3, x_912);
lean_ctor_set(x_919, 4, x_913);
lean_ctor_set(x_919, 5, x_914);
lean_ctor_set(x_919, 6, x_915);
lean_ctor_set(x_919, 7, x_902);
lean_ctor_set_uint8(x_919, sizeof(void*)*8, x_916);
lean_ctor_set_uint8(x_919, sizeof(void*)*8 + 1, x_917);
x_920 = lean_ctor_get(x_2, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_2, 1);
lean_inc(x_921);
x_922 = lean_ctor_get(x_2, 2);
lean_inc(x_922);
x_923 = lean_unsigned_to_nat(0u);
x_924 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_377, x_377, x_923, x_922);
lean_dec(x_377);
x_925 = 1;
x_926 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_926, 0, x_920);
lean_ctor_set(x_926, 1, x_921);
lean_ctor_set(x_926, 2, x_924);
lean_ctor_set_uint8(x_926, sizeof(void*)*3, x_925);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_919);
x_927 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_376, x_926, x_919, x_4, x_5, x_6, x_7, x_8, x_908);
if (lean_obj_tag(x_927) == 0)
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; 
x_928 = lean_ctor_get(x_927, 0);
lean_inc(x_928);
x_929 = lean_ctor_get(x_927, 1);
lean_inc(x_929);
lean_dec(x_927);
lean_inc(x_7);
lean_inc(x_2);
x_930 = l_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm(x_371, x_928, x_2, x_919, x_4, x_5, x_6, x_7, x_8, x_929);
if (lean_obj_tag(x_930) == 0)
{
lean_object* x_931; lean_object* x_932; uint8_t x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; 
x_931 = lean_ctor_get(x_930, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_930, 1);
lean_inc(x_932);
lean_dec(x_930);
x_933 = lean_ctor_get_uint8(x_931, sizeof(void*)*2);
x_934 = lean_ctor_get(x_931, 0);
lean_inc(x_934);
x_935 = lean_ctor_get(x_931, 1);
lean_inc(x_935);
lean_dec(x_931);
x_1131 = x_934;
x_1132 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__2(x_25, x_923, x_1131);
x_1133 = x_1132;
x_1134 = l_Lean_Elab_Term_getCurrMacroScope(x_919, x_4, x_5, x_6, x_7, x_8, x_932);
x_1135 = lean_ctor_get(x_1134, 0);
lean_inc(x_1135);
x_1136 = lean_ctor_get(x_1134, 1);
lean_inc(x_1136);
lean_dec(x_1134);
x_1137 = lean_st_ref_get(x_8, x_1136);
x_1138 = lean_ctor_get(x_1137, 0);
lean_inc(x_1138);
x_1139 = lean_ctor_get(x_1137, 1);
lean_inc(x_1139);
lean_dec(x_1137);
x_1140 = lean_ctor_get(x_1138, 0);
lean_inc(x_1140);
lean_dec(x_1138);
x_1141 = lean_st_ref_get(x_8, x_1139);
x_1142 = lean_ctor_get(x_1141, 0);
lean_inc(x_1142);
x_1143 = lean_ctor_get(x_1141, 1);
lean_inc(x_1143);
lean_dec(x_1141);
x_1144 = lean_ctor_get(x_1142, 1);
lean_inc(x_1144);
lean_dec(x_1142);
lean_inc(x_1140);
x_1145 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_5__expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_1145, 0, x_1140);
x_1146 = x_1145;
x_1147 = lean_environment_main_module(x_1140);
x_1148 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1148, 0, x_1146);
lean_ctor_set(x_1148, 1, x_1147);
lean_ctor_set(x_1148, 2, x_1135);
lean_ctor_set(x_1148, 3, x_16);
lean_ctor_set(x_1148, 4, x_17);
x_1149 = l___private_Lean_Elab_Do_12__mkTuple(x_25, x_1133, x_1148, x_1144);
lean_dec(x_1133);
lean_dec(x_25);
x_1150 = lean_ctor_get(x_1149, 0);
lean_inc(x_1150);
x_1151 = lean_ctor_get(x_1149, 1);
lean_inc(x_1151);
lean_dec(x_1149);
x_1152 = lean_st_ref_take(x_8, x_1143);
x_1153 = lean_ctor_get(x_1152, 0);
lean_inc(x_1153);
x_1154 = lean_ctor_get(x_1152, 1);
lean_inc(x_1154);
lean_dec(x_1152);
x_1155 = lean_ctor_get(x_1153, 0);
lean_inc(x_1155);
x_1156 = lean_ctor_get(x_1153, 2);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1153, 3);
lean_inc(x_1157);
if (lean_is_exclusive(x_1153)) {
 lean_ctor_release(x_1153, 0);
 lean_ctor_release(x_1153, 1);
 lean_ctor_release(x_1153, 2);
 lean_ctor_release(x_1153, 3);
 x_1158 = x_1153;
} else {
 lean_dec_ref(x_1153);
 x_1158 = lean_box(0);
}
if (lean_is_scalar(x_1158)) {
 x_1159 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1159 = x_1158;
}
lean_ctor_set(x_1159, 0, x_1155);
lean_ctor_set(x_1159, 1, x_1151);
lean_ctor_set(x_1159, 2, x_1156);
lean_ctor_set(x_1159, 3, x_1157);
x_1160 = lean_st_ref_set(x_8, x_1159, x_1154);
x_1161 = lean_ctor_get(x_1160, 1);
lean_inc(x_1161);
lean_dec(x_1160);
x_936 = x_1150;
x_937 = x_1161;
goto block_1130;
block_1130:
{
lean_object* x_938; lean_object* x_939; 
if (x_933 == 0)
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; 
x_945 = l_Lean_Elab_Term_getCurrMacroScope(x_919, x_4, x_5, x_6, x_7, x_8, x_937);
x_946 = lean_ctor_get(x_945, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_945, 1);
lean_inc(x_947);
lean_dec(x_945);
x_948 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_947);
x_949 = lean_ctor_get(x_948, 0);
lean_inc(x_949);
x_950 = lean_ctor_get(x_948, 1);
lean_inc(x_950);
lean_dec(x_948);
x_951 = l_Array_empty___closed__1;
x_952 = lean_array_push(x_951, x_373);
x_953 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__23;
x_954 = lean_array_push(x_952, x_953);
x_955 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__27;
x_956 = l_Lean_addMacroScope(x_949, x_955, x_946);
x_957 = lean_box(0);
x_958 = l_Lean_SourceInfo_inhabited___closed__1;
x_959 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__26;
x_960 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_960, 0, x_958);
lean_ctor_set(x_960, 1, x_959);
lean_ctor_set(x_960, 2, x_956);
lean_ctor_set(x_960, 3, x_957);
x_961 = lean_array_push(x_954, x_960);
x_962 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__13;
x_963 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_963, 0, x_962);
lean_ctor_set(x_963, 1, x_961);
x_964 = lean_array_push(x_951, x_963);
lean_inc(x_936);
x_965 = lean_array_push(x_951, x_936);
x_966 = lean_array_push(x_951, x_371);
x_967 = lean_array_push(x_966, x_936);
x_968 = l_Lean_nullKind___closed__2;
x_969 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_969, 0, x_968);
lean_ctor_set(x_969, 1, x_967);
x_970 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
x_971 = lean_array_push(x_970, x_969);
x_972 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_973 = lean_array_push(x_971, x_972);
x_974 = lean_array_push(x_973, x_935);
x_975 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
x_976 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_976, 0, x_975);
lean_ctor_set(x_976, 1, x_974);
lean_inc(x_965);
x_977 = lean_array_push(x_965, x_976);
x_978 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_978, 0, x_968);
lean_ctor_set(x_978, 1, x_977);
x_979 = lean_array_push(x_964, x_978);
x_980 = l_Lean_mkAppStx___closed__8;
x_981 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_981, 0, x_980);
lean_ctor_set(x_981, 1, x_979);
x_982 = l_Lean_Elab_Term_getCurrMacroScope(x_919, x_4, x_5, x_6, x_7, x_8, x_950);
x_983 = lean_ctor_get(x_982, 0);
lean_inc(x_983);
x_984 = lean_ctor_get(x_982, 1);
lean_inc(x_984);
lean_dec(x_982);
x_985 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_984);
x_986 = lean_ctor_get(x_985, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_985, 1);
lean_inc(x_987);
lean_dec(x_985);
x_988 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__30;
x_989 = l_Lean_addMacroScope(x_986, x_988, x_983);
x_990 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__29;
x_991 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_991, 0, x_958);
lean_ctor_set(x_991, 1, x_990);
lean_ctor_set(x_991, 2, x_989);
lean_ctor_set(x_991, 3, x_957);
lean_inc(x_991);
x_992 = lean_array_push(x_951, x_991);
x_993 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_994 = lean_array_push(x_992, x_993);
x_995 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4;
x_996 = lean_array_push(x_994, x_995);
x_997 = lean_array_push(x_996, x_981);
x_998 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
x_999 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_999, 0, x_998);
lean_ctor_set(x_999, 1, x_997);
x_1000 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_1001 = lean_array_push(x_1000, x_999);
x_1002 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1002, 0, x_37);
lean_ctor_set(x_1002, 1, x_1001);
x_1003 = lean_array_push(x_951, x_1002);
x_1004 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_1005 = lean_array_push(x_1003, x_1004);
x_1006 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1006, 0, x_968);
lean_ctor_set(x_1006, 1, x_1005);
x_1007 = lean_array_push(x_951, x_1006);
x_1008 = lean_array_push(x_965, x_993);
x_1009 = lean_array_push(x_1008, x_993);
x_1010 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_1011 = lean_array_push(x_1009, x_1010);
x_1012 = lean_array_push(x_1011, x_991);
x_1013 = l_Lean_Elab_Term_elabLetDeclCore___closed__2;
x_1014 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1014, 0, x_1013);
lean_ctor_set(x_1014, 1, x_1012);
x_1015 = lean_array_push(x_951, x_1014);
x_1016 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1016, 0, x_39);
lean_ctor_set(x_1016, 1, x_1015);
x_1017 = lean_array_push(x_951, x_1016);
x_1018 = lean_array_push(x_1017, x_993);
x_1019 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1019, 0, x_968);
lean_ctor_set(x_1019, 1, x_1018);
x_1020 = lean_array_push(x_1007, x_1019);
x_1021 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1021, 0, x_968);
lean_ctor_set(x_1021, 1, x_1020);
x_1022 = lean_array_push(x_951, x_1021);
x_1023 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4;
x_1024 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1024, 0, x_1023);
lean_ctor_set(x_1024, 1, x_1022);
x_1025 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2;
x_1026 = lean_array_push(x_1025, x_1024);
x_1027 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2;
x_1028 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1028, 0, x_1027);
lean_ctor_set(x_1028, 1, x_1026);
x_938 = x_1028;
x_939 = x_987;
goto block_944;
}
else
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; 
x_1029 = l_Lean_Elab_Term_getCurrMacroScope(x_919, x_4, x_5, x_6, x_7, x_8, x_937);
x_1030 = lean_ctor_get(x_1029, 0);
lean_inc(x_1030);
x_1031 = lean_ctor_get(x_1029, 1);
lean_inc(x_1031);
lean_dec(x_1029);
x_1032 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_1031);
x_1033 = lean_ctor_get(x_1032, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_1032, 1);
lean_inc(x_1034);
lean_dec(x_1032);
x_1035 = l_Array_empty___closed__1;
x_1036 = lean_array_push(x_1035, x_373);
x_1037 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__23;
x_1038 = lean_array_push(x_1036, x_1037);
x_1039 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__34;
x_1040 = l_Lean_addMacroScope(x_1033, x_1039, x_1030);
x_1041 = lean_box(0);
x_1042 = l_Lean_SourceInfo_inhabited___closed__1;
x_1043 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__33;
x_1044 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1044, 0, x_1042);
lean_ctor_set(x_1044, 1, x_1043);
lean_ctor_set(x_1044, 2, x_1040);
lean_ctor_set(x_1044, 3, x_1041);
x_1045 = lean_array_push(x_1038, x_1044);
x_1046 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__13;
x_1047 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1047, 0, x_1046);
lean_ctor_set(x_1047, 1, x_1045);
x_1048 = lean_array_push(x_1035, x_1047);
lean_inc(x_936);
x_1049 = lean_array_push(x_1035, x_936);
x_1050 = lean_array_push(x_1035, x_371);
x_1051 = lean_array_push(x_1050, x_936);
x_1052 = l_Lean_nullKind___closed__2;
x_1053 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1053, 0, x_1052);
lean_ctor_set(x_1053, 1, x_1051);
x_1054 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
x_1055 = lean_array_push(x_1054, x_1053);
x_1056 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_1057 = lean_array_push(x_1055, x_1056);
x_1058 = lean_array_push(x_1057, x_935);
x_1059 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
x_1060 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1060, 0, x_1059);
lean_ctor_set(x_1060, 1, x_1058);
lean_inc(x_1049);
x_1061 = lean_array_push(x_1049, x_1060);
x_1062 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1062, 0, x_1052);
lean_ctor_set(x_1062, 1, x_1061);
x_1063 = lean_array_push(x_1048, x_1062);
x_1064 = l_Lean_mkAppStx___closed__8;
x_1065 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1065, 0, x_1064);
lean_ctor_set(x_1065, 1, x_1063);
x_1066 = l_Lean_Elab_Term_getCurrMacroScope(x_919, x_4, x_5, x_6, x_7, x_8, x_1034);
x_1067 = lean_ctor_get(x_1066, 0);
lean_inc(x_1067);
x_1068 = lean_ctor_get(x_1066, 1);
lean_inc(x_1068);
lean_dec(x_1066);
x_1069 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_1068);
x_1070 = lean_ctor_get(x_1069, 0);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_1069, 1);
lean_inc(x_1071);
lean_dec(x_1069);
x_1072 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__30;
x_1073 = l_Lean_addMacroScope(x_1070, x_1072, x_1067);
x_1074 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__29;
x_1075 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1075, 0, x_1042);
lean_ctor_set(x_1075, 1, x_1074);
lean_ctor_set(x_1075, 2, x_1073);
lean_ctor_set(x_1075, 3, x_1041);
x_1076 = lean_array_push(x_1035, x_1075);
x_1077 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
lean_inc(x_1076);
x_1078 = lean_array_push(x_1076, x_1077);
x_1079 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4;
x_1080 = lean_array_push(x_1078, x_1079);
x_1081 = lean_array_push(x_1080, x_1065);
x_1082 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
x_1083 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1083, 0, x_1082);
lean_ctor_set(x_1083, 1, x_1081);
x_1084 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_1085 = lean_array_push(x_1084, x_1083);
x_1086 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1086, 0, x_37);
lean_ctor_set(x_1086, 1, x_1085);
x_1087 = lean_array_push(x_1035, x_1086);
x_1088 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_1089 = lean_array_push(x_1087, x_1088);
x_1090 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1090, 0, x_1052);
lean_ctor_set(x_1090, 1, x_1089);
x_1091 = lean_array_push(x_1035, x_1090);
x_1092 = lean_array_push(x_1049, x_1077);
x_1093 = lean_array_push(x_1092, x_1077);
x_1094 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_1095 = lean_array_push(x_1093, x_1094);
x_1096 = lean_array_push(x_1076, x_1037);
x_1097 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__38;
lean_inc(x_1096);
x_1098 = lean_array_push(x_1096, x_1097);
x_1099 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1099, 0, x_1046);
lean_ctor_set(x_1099, 1, x_1098);
x_1100 = lean_array_push(x_1095, x_1099);
x_1101 = l_Lean_Elab_Term_elabLetDeclCore___closed__2;
x_1102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1102, 0, x_1101);
lean_ctor_set(x_1102, 1, x_1100);
x_1103 = lean_array_push(x_1035, x_1102);
x_1104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1104, 0, x_39);
lean_ctor_set(x_1104, 1, x_1103);
x_1105 = lean_array_push(x_1035, x_1104);
x_1106 = lean_array_push(x_1105, x_1088);
x_1107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1107, 0, x_1052);
lean_ctor_set(x_1107, 1, x_1106);
x_1108 = lean_array_push(x_1091, x_1107);
x_1109 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__42;
x_1110 = lean_array_push(x_1096, x_1109);
x_1111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1111, 0, x_1046);
lean_ctor_set(x_1111, 1, x_1110);
x_1112 = lean_array_push(x_1035, x_1111);
x_1113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1113, 0, x_1052);
lean_ctor_set(x_1113, 1, x_1112);
x_1114 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__20;
x_1115 = lean_array_push(x_1114, x_1113);
x_1116 = l___private_Lean_Elab_Do_9__expandDoIf___closed__2;
x_1117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1117, 0, x_1116);
lean_ctor_set(x_1117, 1, x_1115);
x_1118 = lean_array_push(x_1035, x_1117);
x_1119 = lean_array_push(x_1118, x_1077);
x_1120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1120, 0, x_1052);
lean_ctor_set(x_1120, 1, x_1119);
x_1121 = lean_array_push(x_1108, x_1120);
x_1122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1122, 0, x_1052);
lean_ctor_set(x_1122, 1, x_1121);
x_1123 = lean_array_push(x_1035, x_1122);
x_1124 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4;
x_1125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1125, 0, x_1124);
lean_ctor_set(x_1125, 1, x_1123);
x_1126 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2;
x_1127 = lean_array_push(x_1126, x_1125);
x_1128 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2;
x_1129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1129, 0, x_1128);
lean_ctor_set(x_1129, 1, x_1127);
x_938 = x_1129;
x_939 = x_1071;
goto block_944;
}
block_944:
{
lean_object* x_940; lean_object* x_941; lean_object* x_942; 
x_940 = l_Lean_Syntax_getArg(x_938, x_370);
lean_dec(x_938);
x_941 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_940);
x_942 = l_List_append___rarg(x_941, x_13);
x_1 = x_942;
x_3 = x_919;
x_9 = x_939;
goto _start;
}
}
}
else
{
lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; 
lean_dec(x_919);
lean_dec(x_373);
lean_dec(x_371);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1162 = lean_ctor_get(x_930, 0);
lean_inc(x_1162);
x_1163 = lean_ctor_get(x_930, 1);
lean_inc(x_1163);
if (lean_is_exclusive(x_930)) {
 lean_ctor_release(x_930, 0);
 lean_ctor_release(x_930, 1);
 x_1164 = x_930;
} else {
 lean_dec_ref(x_930);
 x_1164 = lean_box(0);
}
if (lean_is_scalar(x_1164)) {
 x_1165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1165 = x_1164;
}
lean_ctor_set(x_1165, 0, x_1162);
lean_ctor_set(x_1165, 1, x_1163);
return x_1165;
}
}
else
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; 
lean_dec(x_919);
lean_dec(x_373);
lean_dec(x_371);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1166 = lean_ctor_get(x_927, 0);
lean_inc(x_1166);
x_1167 = lean_ctor_get(x_927, 1);
lean_inc(x_1167);
if (lean_is_exclusive(x_927)) {
 lean_ctor_release(x_927, 0);
 lean_ctor_release(x_927, 1);
 x_1168 = x_927;
} else {
 lean_dec_ref(x_927);
 x_1168 = lean_box(0);
}
if (lean_is_scalar(x_1168)) {
 x_1169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1169 = x_1168;
}
lean_ctor_set(x_1169, 0, x_1166);
lean_ctor_set(x_1169, 1, x_1167);
return x_1169;
}
}
}
}
}
else
{
lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; 
lean_dec(x_32);
lean_dec(x_17);
lean_dec(x_16);
x_1176 = lean_unsigned_to_nat(1u);
x_1177 = l_Lean_Syntax_getArg(x_25, x_1176);
x_1178 = lean_unsigned_to_nat(3u);
x_1179 = l_Lean_Syntax_getArg(x_25, x_1178);
x_1180 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_1179);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_1181 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_1180, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_1181) == 0)
{
lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; 
x_1182 = lean_ctor_get(x_1181, 0);
lean_inc(x_1182);
x_1183 = lean_ctor_get(x_1181, 1);
lean_inc(x_1183);
lean_dec(x_1181);
x_1184 = l_Lean_Elab_Term_Do_mkUnless(x_25, x_1177, x_1182, x_3, x_4, x_5, x_6, x_7, x_8, x_1183);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_1185; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1185 = !lean_is_exclusive(x_1184);
if (x_1185 == 0)
{
return x_1184;
}
else
{
lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; 
x_1186 = lean_ctor_get(x_1184, 0);
x_1187 = lean_ctor_get(x_1184, 1);
lean_inc(x_1187);
lean_inc(x_1186);
lean_dec(x_1184);
x_1188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1188, 0, x_1186);
lean_ctor_set(x_1188, 1, x_1187);
return x_1188;
}
}
else
{
lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; 
x_1189 = lean_ctor_get(x_1184, 0);
lean_inc(x_1189);
x_1190 = lean_ctor_get(x_1184, 1);
lean_inc(x_1190);
lean_dec(x_1184);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1191 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_1190);
if (lean_obj_tag(x_1191) == 0)
{
lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; 
x_1192 = lean_ctor_get(x_1191, 0);
lean_inc(x_1192);
x_1193 = lean_ctor_get(x_1191, 1);
lean_inc(x_1193);
lean_dec(x_1191);
x_1194 = l_Lean_Elab_Term_Do_concat(x_1189, x_1192, x_3, x_4, x_5, x_6, x_7, x_8, x_1193);
return x_1194;
}
else
{
uint8_t x_1195; 
lean_dec(x_1189);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1195 = !lean_is_exclusive(x_1191);
if (x_1195 == 0)
{
return x_1191;
}
else
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; 
x_1196 = lean_ctor_get(x_1191, 0);
x_1197 = lean_ctor_get(x_1191, 1);
lean_inc(x_1197);
lean_inc(x_1196);
lean_dec(x_1191);
x_1198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1198, 0, x_1196);
lean_ctor_set(x_1198, 1, x_1197);
return x_1198;
}
}
}
}
else
{
uint8_t x_1199; 
lean_dec(x_1177);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1199 = !lean_is_exclusive(x_1181);
if (x_1199 == 0)
{
return x_1181;
}
else
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
x_1200 = lean_ctor_get(x_1181, 0);
x_1201 = lean_ctor_get(x_1181, 1);
lean_inc(x_1201);
lean_inc(x_1200);
lean_dec(x_1181);
x_1202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1202, 0, x_1200);
lean_ctor_set(x_1202, 1, x_1201);
return x_1202;
}
}
}
}
else
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; 
lean_dec(x_32);
lean_dec(x_17);
lean_dec(x_16);
lean_inc(x_25);
x_1203 = l___private_Lean_Elab_Do_10__mkDoIfView(x_25);
x_1204 = lean_ctor_get(x_1203, 3);
lean_inc(x_1204);
x_1205 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_1204);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_1206 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_1205, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_1206) == 0)
{
lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; 
x_1207 = lean_ctor_get(x_1206, 0);
lean_inc(x_1207);
x_1208 = lean_ctor_get(x_1206, 1);
lean_inc(x_1208);
lean_dec(x_1206);
x_1209 = lean_ctor_get(x_1203, 4);
lean_inc(x_1209);
x_1210 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_1209);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_1211 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_1210, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_1208);
if (lean_obj_tag(x_1211) == 0)
{
lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; 
x_1212 = lean_ctor_get(x_1211, 0);
lean_inc(x_1212);
x_1213 = lean_ctor_get(x_1211, 1);
lean_inc(x_1213);
lean_dec(x_1211);
x_1214 = l___private_Lean_Elab_Do_9__expandDoIf(x_25);
x_1215 = lean_ctor_get(x_1203, 1);
lean_inc(x_1215);
x_1216 = lean_ctor_get(x_1203, 2);
lean_inc(x_1216);
lean_dec(x_1203);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1217 = l_Lean_Elab_Term_Do_mkIte(x_1214, x_1215, x_1216, x_1207, x_1212, x_3, x_4, x_5, x_6, x_7, x_8, x_1213);
if (lean_obj_tag(x_1217) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_1218; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1218 = !lean_is_exclusive(x_1217);
if (x_1218 == 0)
{
return x_1217;
}
else
{
lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; 
x_1219 = lean_ctor_get(x_1217, 0);
x_1220 = lean_ctor_get(x_1217, 1);
lean_inc(x_1220);
lean_inc(x_1219);
lean_dec(x_1217);
x_1221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1221, 0, x_1219);
lean_ctor_set(x_1221, 1, x_1220);
return x_1221;
}
}
else
{
lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; 
x_1222 = lean_ctor_get(x_1217, 0);
lean_inc(x_1222);
x_1223 = lean_ctor_get(x_1217, 1);
lean_inc(x_1223);
lean_dec(x_1217);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1224 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_1223);
if (lean_obj_tag(x_1224) == 0)
{
lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; 
x_1225 = lean_ctor_get(x_1224, 0);
lean_inc(x_1225);
x_1226 = lean_ctor_get(x_1224, 1);
lean_inc(x_1226);
lean_dec(x_1224);
x_1227 = l_Lean_Elab_Term_Do_concat(x_1222, x_1225, x_3, x_4, x_5, x_6, x_7, x_8, x_1226);
return x_1227;
}
else
{
uint8_t x_1228; 
lean_dec(x_1222);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1228 = !lean_is_exclusive(x_1224);
if (x_1228 == 0)
{
return x_1224;
}
else
{
lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; 
x_1229 = lean_ctor_get(x_1224, 0);
x_1230 = lean_ctor_get(x_1224, 1);
lean_inc(x_1230);
lean_inc(x_1229);
lean_dec(x_1224);
x_1231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1231, 0, x_1229);
lean_ctor_set(x_1231, 1, x_1230);
return x_1231;
}
}
}
}
else
{
uint8_t x_1232; 
lean_dec(x_7);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1232 = !lean_is_exclusive(x_1217);
if (x_1232 == 0)
{
return x_1217;
}
else
{
lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; 
x_1233 = lean_ctor_get(x_1217, 0);
x_1234 = lean_ctor_get(x_1217, 1);
lean_inc(x_1234);
lean_inc(x_1233);
lean_dec(x_1217);
x_1235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1235, 0, x_1233);
lean_ctor_set(x_1235, 1, x_1234);
return x_1235;
}
}
}
else
{
uint8_t x_1236; 
lean_dec(x_1207);
lean_dec(x_1203);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1236 = !lean_is_exclusive(x_1211);
if (x_1236 == 0)
{
return x_1211;
}
else
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; 
x_1237 = lean_ctor_get(x_1211, 0);
x_1238 = lean_ctor_get(x_1211, 1);
lean_inc(x_1238);
lean_inc(x_1237);
lean_dec(x_1211);
x_1239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1239, 0, x_1237);
lean_ctor_set(x_1239, 1, x_1238);
return x_1239;
}
}
}
else
{
uint8_t x_1240; 
lean_dec(x_1203);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1240 = !lean_is_exclusive(x_1206);
if (x_1240 == 0)
{
return x_1206;
}
else
{
lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; 
x_1241 = lean_ctor_get(x_1206, 0);
x_1242 = lean_ctor_get(x_1206, 1);
lean_inc(x_1242);
lean_inc(x_1241);
lean_dec(x_1206);
x_1243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1243, 0, x_1241);
lean_ctor_set(x_1243, 1, x_1242);
return x_1243;
}
}
}
}
else
{
lean_object* x_1244; lean_object* x_1245; 
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
x_1244 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__22;
x_1245 = l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(x_1244, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1245;
}
}
else
{
lean_object* x_1246; lean_object* x_1247; 
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
x_1246 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__22;
x_1247 = l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(x_1246, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1247;
}
}
else
{
lean_object* x_1248; 
lean_dec(x_32);
lean_dec(x_17);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1248 = l_Lean_Elab_Term_Do_getDoReassignVars(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_1248) == 0)
{
lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; 
x_1249 = lean_ctor_get(x_1248, 0);
lean_inc(x_1249);
x_1250 = lean_ctor_get(x_1248, 1);
lean_inc(x_1250);
lean_dec(x_1248);
x_1251 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_1252 = l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2(x_2, x_1249, x_1251, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_1250);
if (lean_obj_tag(x_1252) == 0)
{
lean_object* x_1253; lean_object* x_1254; 
x_1253 = lean_ctor_get(x_1252, 1);
lean_inc(x_1253);
lean_dec(x_1252);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1254 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_1253);
if (lean_obj_tag(x_1254) == 0)
{
lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; 
x_1255 = lean_ctor_get(x_1254, 0);
lean_inc(x_1255);
x_1256 = lean_ctor_get(x_1254, 1);
lean_inc(x_1256);
lean_dec(x_1254);
x_1257 = l_Lean_Elab_Term_Do_mkReassignCore(x_1249, x_25, x_1255, x_3, x_4, x_5, x_6, x_7, x_8, x_1256);
return x_1257;
}
else
{
uint8_t x_1258; 
lean_dec(x_1249);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1258 = !lean_is_exclusive(x_1254);
if (x_1258 == 0)
{
return x_1254;
}
else
{
lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; 
x_1259 = lean_ctor_get(x_1254, 0);
x_1260 = lean_ctor_get(x_1254, 1);
lean_inc(x_1260);
lean_inc(x_1259);
lean_dec(x_1254);
x_1261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1261, 0, x_1259);
lean_ctor_set(x_1261, 1, x_1260);
return x_1261;
}
}
}
else
{
uint8_t x_1262; 
lean_dec(x_1249);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1262 = !lean_is_exclusive(x_1252);
if (x_1262 == 0)
{
return x_1252;
}
else
{
lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; 
x_1263 = lean_ctor_get(x_1252, 0);
x_1264 = lean_ctor_get(x_1252, 1);
lean_inc(x_1264);
lean_inc(x_1263);
lean_dec(x_1252);
x_1265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1265, 0, x_1263);
lean_ctor_set(x_1265, 1, x_1264);
return x_1265;
}
}
}
else
{
uint8_t x_1266; 
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1266 = !lean_is_exclusive(x_1248);
if (x_1266 == 0)
{
return x_1248;
}
else
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; 
x_1267 = lean_ctor_get(x_1248, 0);
x_1268 = lean_ctor_get(x_1248, 1);
lean_inc(x_1268);
lean_inc(x_1267);
lean_dec(x_1248);
x_1269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1269, 0, x_1267);
lean_ctor_set(x_1269, 1, x_1268);
return x_1269;
}
}
}
}
else
{
lean_object* x_1270; 
lean_dec(x_32);
lean_dec(x_17);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1270 = l_Lean_Elab_Term_Do_getDoLetArrowVars(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_1270) == 0)
{
lean_object* x_1271; lean_object* x_1272; uint8_t x_1273; 
x_1271 = lean_ctor_get(x_1270, 0);
lean_inc(x_1271);
x_1272 = lean_ctor_get(x_1270, 1);
lean_inc(x_1272);
lean_dec(x_1270);
x_1273 = !lean_is_exclusive(x_2);
if (x_1273 == 0)
{
lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; 
x_1274 = lean_ctor_get(x_2, 2);
x_1275 = lean_unsigned_to_nat(0u);
x_1276 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_1271, x_1271, x_1275, x_1274);
lean_ctor_set(x_2, 2, x_1276);
x_1277 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_1272);
if (lean_obj_tag(x_1277) == 0)
{
uint8_t x_1278; 
x_1278 = !lean_is_exclusive(x_1277);
if (x_1278 == 0)
{
lean_object* x_1279; lean_object* x_1280; 
x_1279 = lean_ctor_get(x_1277, 0);
x_1280 = l_Lean_Elab_Term_Do_mkVarDeclCore(x_1271, x_25, x_1279);
lean_ctor_set(x_1277, 0, x_1280);
return x_1277;
}
else
{
lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; 
x_1281 = lean_ctor_get(x_1277, 0);
x_1282 = lean_ctor_get(x_1277, 1);
lean_inc(x_1282);
lean_inc(x_1281);
lean_dec(x_1277);
x_1283 = l_Lean_Elab_Term_Do_mkVarDeclCore(x_1271, x_25, x_1281);
x_1284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1284, 0, x_1283);
lean_ctor_set(x_1284, 1, x_1282);
return x_1284;
}
}
else
{
uint8_t x_1285; 
lean_dec(x_1271);
lean_dec(x_25);
x_1285 = !lean_is_exclusive(x_1277);
if (x_1285 == 0)
{
return x_1277;
}
else
{
lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; 
x_1286 = lean_ctor_get(x_1277, 0);
x_1287 = lean_ctor_get(x_1277, 1);
lean_inc(x_1287);
lean_inc(x_1286);
lean_dec(x_1277);
x_1288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1288, 0, x_1286);
lean_ctor_set(x_1288, 1, x_1287);
return x_1288;
}
}
}
else
{
lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; uint8_t x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; 
x_1289 = lean_ctor_get(x_2, 0);
x_1290 = lean_ctor_get(x_2, 1);
x_1291 = lean_ctor_get(x_2, 2);
x_1292 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
lean_inc(x_1291);
lean_inc(x_1290);
lean_inc(x_1289);
lean_dec(x_2);
x_1293 = lean_unsigned_to_nat(0u);
x_1294 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_1271, x_1271, x_1293, x_1291);
x_1295 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1295, 0, x_1289);
lean_ctor_set(x_1295, 1, x_1290);
lean_ctor_set(x_1295, 2, x_1294);
lean_ctor_set_uint8(x_1295, sizeof(void*)*3, x_1292);
x_1296 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_1295, x_3, x_4, x_5, x_6, x_7, x_8, x_1272);
if (lean_obj_tag(x_1296) == 0)
{
lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; 
x_1297 = lean_ctor_get(x_1296, 0);
lean_inc(x_1297);
x_1298 = lean_ctor_get(x_1296, 1);
lean_inc(x_1298);
if (lean_is_exclusive(x_1296)) {
 lean_ctor_release(x_1296, 0);
 lean_ctor_release(x_1296, 1);
 x_1299 = x_1296;
} else {
 lean_dec_ref(x_1296);
 x_1299 = lean_box(0);
}
x_1300 = l_Lean_Elab_Term_Do_mkVarDeclCore(x_1271, x_25, x_1297);
if (lean_is_scalar(x_1299)) {
 x_1301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1301 = x_1299;
}
lean_ctor_set(x_1301, 0, x_1300);
lean_ctor_set(x_1301, 1, x_1298);
return x_1301;
}
else
{
lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; 
lean_dec(x_1271);
lean_dec(x_25);
x_1302 = lean_ctor_get(x_1296, 0);
lean_inc(x_1302);
x_1303 = lean_ctor_get(x_1296, 1);
lean_inc(x_1303);
if (lean_is_exclusive(x_1296)) {
 lean_ctor_release(x_1296, 0);
 lean_ctor_release(x_1296, 1);
 x_1304 = x_1296;
} else {
 lean_dec_ref(x_1296);
 x_1304 = lean_box(0);
}
if (lean_is_scalar(x_1304)) {
 x_1305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1305 = x_1304;
}
lean_ctor_set(x_1305, 0, x_1302);
lean_ctor_set(x_1305, 1, x_1303);
return x_1305;
}
}
}
else
{
uint8_t x_1306; 
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1306 = !lean_is_exclusive(x_1270);
if (x_1306 == 0)
{
return x_1270;
}
else
{
lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; 
x_1307 = lean_ctor_get(x_1270, 0);
x_1308 = lean_ctor_get(x_1270, 1);
lean_inc(x_1308);
lean_inc(x_1307);
lean_dec(x_1270);
x_1309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1309, 0, x_1307);
lean_ctor_set(x_1309, 1, x_1308);
return x_1309;
}
}
}
}
else
{
lean_object* x_1310; 
lean_dec(x_32);
lean_dec(x_17);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1310 = l_Lean_Elab_Term_Do_getDoLetRecVars(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_1310) == 0)
{
lean_object* x_1311; lean_object* x_1312; uint8_t x_1313; 
x_1311 = lean_ctor_get(x_1310, 0);
lean_inc(x_1311);
x_1312 = lean_ctor_get(x_1310, 1);
lean_inc(x_1312);
lean_dec(x_1310);
x_1313 = !lean_is_exclusive(x_2);
if (x_1313 == 0)
{
lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; 
x_1314 = lean_ctor_get(x_2, 2);
x_1315 = lean_unsigned_to_nat(0u);
x_1316 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_1311, x_1311, x_1315, x_1314);
lean_ctor_set(x_2, 2, x_1316);
x_1317 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_1312);
if (lean_obj_tag(x_1317) == 0)
{
uint8_t x_1318; 
x_1318 = !lean_is_exclusive(x_1317);
if (x_1318 == 0)
{
lean_object* x_1319; lean_object* x_1320; 
x_1319 = lean_ctor_get(x_1317, 0);
x_1320 = l_Lean_Elab_Term_Do_mkVarDeclCore(x_1311, x_25, x_1319);
lean_ctor_set(x_1317, 0, x_1320);
return x_1317;
}
else
{
lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; 
x_1321 = lean_ctor_get(x_1317, 0);
x_1322 = lean_ctor_get(x_1317, 1);
lean_inc(x_1322);
lean_inc(x_1321);
lean_dec(x_1317);
x_1323 = l_Lean_Elab_Term_Do_mkVarDeclCore(x_1311, x_25, x_1321);
x_1324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1324, 0, x_1323);
lean_ctor_set(x_1324, 1, x_1322);
return x_1324;
}
}
else
{
uint8_t x_1325; 
lean_dec(x_1311);
lean_dec(x_25);
x_1325 = !lean_is_exclusive(x_1317);
if (x_1325 == 0)
{
return x_1317;
}
else
{
lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; 
x_1326 = lean_ctor_get(x_1317, 0);
x_1327 = lean_ctor_get(x_1317, 1);
lean_inc(x_1327);
lean_inc(x_1326);
lean_dec(x_1317);
x_1328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1328, 0, x_1326);
lean_ctor_set(x_1328, 1, x_1327);
return x_1328;
}
}
}
else
{
lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; uint8_t x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; 
x_1329 = lean_ctor_get(x_2, 0);
x_1330 = lean_ctor_get(x_2, 1);
x_1331 = lean_ctor_get(x_2, 2);
x_1332 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
lean_inc(x_1331);
lean_inc(x_1330);
lean_inc(x_1329);
lean_dec(x_2);
x_1333 = lean_unsigned_to_nat(0u);
x_1334 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_1311, x_1311, x_1333, x_1331);
x_1335 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1335, 0, x_1329);
lean_ctor_set(x_1335, 1, x_1330);
lean_ctor_set(x_1335, 2, x_1334);
lean_ctor_set_uint8(x_1335, sizeof(void*)*3, x_1332);
x_1336 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_1335, x_3, x_4, x_5, x_6, x_7, x_8, x_1312);
if (lean_obj_tag(x_1336) == 0)
{
lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; 
x_1337 = lean_ctor_get(x_1336, 0);
lean_inc(x_1337);
x_1338 = lean_ctor_get(x_1336, 1);
lean_inc(x_1338);
if (lean_is_exclusive(x_1336)) {
 lean_ctor_release(x_1336, 0);
 lean_ctor_release(x_1336, 1);
 x_1339 = x_1336;
} else {
 lean_dec_ref(x_1336);
 x_1339 = lean_box(0);
}
x_1340 = l_Lean_Elab_Term_Do_mkVarDeclCore(x_1311, x_25, x_1337);
if (lean_is_scalar(x_1339)) {
 x_1341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1341 = x_1339;
}
lean_ctor_set(x_1341, 0, x_1340);
lean_ctor_set(x_1341, 1, x_1338);
return x_1341;
}
else
{
lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; 
lean_dec(x_1311);
lean_dec(x_25);
x_1342 = lean_ctor_get(x_1336, 0);
lean_inc(x_1342);
x_1343 = lean_ctor_get(x_1336, 1);
lean_inc(x_1343);
if (lean_is_exclusive(x_1336)) {
 lean_ctor_release(x_1336, 0);
 lean_ctor_release(x_1336, 1);
 x_1344 = x_1336;
} else {
 lean_dec_ref(x_1336);
 x_1344 = lean_box(0);
}
if (lean_is_scalar(x_1344)) {
 x_1345 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1345 = x_1344;
}
lean_ctor_set(x_1345, 0, x_1342);
lean_ctor_set(x_1345, 1, x_1343);
return x_1345;
}
}
}
else
{
uint8_t x_1346; 
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1346 = !lean_is_exclusive(x_1310);
if (x_1346 == 0)
{
return x_1310;
}
else
{
lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; 
x_1347 = lean_ctor_get(x_1310, 0);
x_1348 = lean_ctor_get(x_1310, 1);
lean_inc(x_1348);
lean_inc(x_1347);
lean_dec(x_1310);
x_1349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1349, 0, x_1347);
lean_ctor_set(x_1349, 1, x_1348);
return x_1349;
}
}
}
}
else
{
lean_object* x_1350; 
lean_dec(x_32);
lean_dec(x_17);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1350 = l_Lean_Elab_Term_Do_getDoLetVars(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_1350) == 0)
{
lean_object* x_1351; lean_object* x_1352; uint8_t x_1353; 
x_1351 = lean_ctor_get(x_1350, 0);
lean_inc(x_1351);
x_1352 = lean_ctor_get(x_1350, 1);
lean_inc(x_1352);
lean_dec(x_1350);
x_1353 = !lean_is_exclusive(x_2);
if (x_1353 == 0)
{
lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; 
x_1354 = lean_ctor_get(x_2, 2);
x_1355 = lean_unsigned_to_nat(0u);
x_1356 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_1351, x_1351, x_1355, x_1354);
lean_ctor_set(x_2, 2, x_1356);
x_1357 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_1352);
if (lean_obj_tag(x_1357) == 0)
{
uint8_t x_1358; 
x_1358 = !lean_is_exclusive(x_1357);
if (x_1358 == 0)
{
lean_object* x_1359; lean_object* x_1360; 
x_1359 = lean_ctor_get(x_1357, 0);
x_1360 = l_Lean_Elab_Term_Do_mkVarDeclCore(x_1351, x_25, x_1359);
lean_ctor_set(x_1357, 0, x_1360);
return x_1357;
}
else
{
lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; 
x_1361 = lean_ctor_get(x_1357, 0);
x_1362 = lean_ctor_get(x_1357, 1);
lean_inc(x_1362);
lean_inc(x_1361);
lean_dec(x_1357);
x_1363 = l_Lean_Elab_Term_Do_mkVarDeclCore(x_1351, x_25, x_1361);
x_1364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1364, 0, x_1363);
lean_ctor_set(x_1364, 1, x_1362);
return x_1364;
}
}
else
{
uint8_t x_1365; 
lean_dec(x_1351);
lean_dec(x_25);
x_1365 = !lean_is_exclusive(x_1357);
if (x_1365 == 0)
{
return x_1357;
}
else
{
lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; 
x_1366 = lean_ctor_get(x_1357, 0);
x_1367 = lean_ctor_get(x_1357, 1);
lean_inc(x_1367);
lean_inc(x_1366);
lean_dec(x_1357);
x_1368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1368, 0, x_1366);
lean_ctor_set(x_1368, 1, x_1367);
return x_1368;
}
}
}
else
{
lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; uint8_t x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; 
x_1369 = lean_ctor_get(x_2, 0);
x_1370 = lean_ctor_get(x_2, 1);
x_1371 = lean_ctor_get(x_2, 2);
x_1372 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
lean_inc(x_1371);
lean_inc(x_1370);
lean_inc(x_1369);
lean_dec(x_2);
x_1373 = lean_unsigned_to_nat(0u);
x_1374 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_1351, x_1351, x_1373, x_1371);
x_1375 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1375, 0, x_1369);
lean_ctor_set(x_1375, 1, x_1370);
lean_ctor_set(x_1375, 2, x_1374);
lean_ctor_set_uint8(x_1375, sizeof(void*)*3, x_1372);
x_1376 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_1375, x_3, x_4, x_5, x_6, x_7, x_8, x_1352);
if (lean_obj_tag(x_1376) == 0)
{
lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; 
x_1377 = lean_ctor_get(x_1376, 0);
lean_inc(x_1377);
x_1378 = lean_ctor_get(x_1376, 1);
lean_inc(x_1378);
if (lean_is_exclusive(x_1376)) {
 lean_ctor_release(x_1376, 0);
 lean_ctor_release(x_1376, 1);
 x_1379 = x_1376;
} else {
 lean_dec_ref(x_1376);
 x_1379 = lean_box(0);
}
x_1380 = l_Lean_Elab_Term_Do_mkVarDeclCore(x_1351, x_25, x_1377);
if (lean_is_scalar(x_1379)) {
 x_1381 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1381 = x_1379;
}
lean_ctor_set(x_1381, 0, x_1380);
lean_ctor_set(x_1381, 1, x_1378);
return x_1381;
}
else
{
lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; 
lean_dec(x_1351);
lean_dec(x_25);
x_1382 = lean_ctor_get(x_1376, 0);
lean_inc(x_1382);
x_1383 = lean_ctor_get(x_1376, 1);
lean_inc(x_1383);
if (lean_is_exclusive(x_1376)) {
 lean_ctor_release(x_1376, 0);
 lean_ctor_release(x_1376, 1);
 x_1384 = x_1376;
} else {
 lean_dec_ref(x_1376);
 x_1384 = lean_box(0);
}
if (lean_is_scalar(x_1384)) {
 x_1385 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1385 = x_1384;
}
lean_ctor_set(x_1385, 0, x_1382);
lean_ctor_set(x_1385, 1, x_1383);
return x_1385;
}
}
}
else
{
uint8_t x_1386; 
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1386 = !lean_is_exclusive(x_1350);
if (x_1386 == 0)
{
return x_1350;
}
else
{
lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; 
x_1387 = lean_ctor_get(x_1350, 0);
x_1388 = lean_ctor_get(x_1350, 1);
lean_inc(x_1388);
lean_inc(x_1387);
lean_dec(x_1350);
x_1389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1389, 0, x_1387);
lean_ctor_set(x_1389, 1, x_1388);
return x_1389;
}
}
}
}
}
}
else
{
lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_2114; lean_object* x_2115; lean_object* x_2116; lean_object* x_2117; lean_object* x_2118; lean_object* x_2119; lean_object* x_2120; lean_object* x_2121; lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; 
x_1437 = lean_ctor_get(x_7, 0);
x_1438 = lean_ctor_get(x_7, 1);
x_1439 = lean_ctor_get(x_7, 2);
x_1440 = lean_ctor_get(x_7, 3);
lean_inc(x_1440);
lean_inc(x_1439);
lean_inc(x_1438);
lean_inc(x_1437);
lean_dec(x_7);
x_1441 = l_Lean_replaceRef(x_12, x_1440);
x_1442 = l_Lean_replaceRef(x_1441, x_1440);
lean_dec(x_1441);
x_1443 = l_Lean_replaceRef(x_1442, x_1440);
lean_dec(x_1440);
lean_dec(x_1442);
lean_inc(x_1439);
lean_inc(x_1438);
x_1444 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1444, 0, x_1437);
lean_ctor_set(x_1444, 1, x_1438);
lean_ctor_set(x_1444, 2, x_1439);
lean_ctor_set(x_1444, 3, x_1443);
x_2114 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_1444, x_8, x_9);
x_2115 = lean_ctor_get(x_2114, 0);
lean_inc(x_2115);
x_2116 = lean_ctor_get(x_2114, 1);
lean_inc(x_2116);
lean_dec(x_2114);
x_2117 = lean_st_ref_get(x_8, x_2116);
x_2118 = lean_ctor_get(x_2117, 0);
lean_inc(x_2118);
x_2119 = lean_ctor_get(x_2117, 1);
lean_inc(x_2119);
lean_dec(x_2117);
x_2120 = lean_ctor_get(x_2118, 0);
lean_inc(x_2120);
lean_dec(x_2118);
x_2121 = lean_st_ref_get(x_8, x_2119);
x_2122 = lean_ctor_get(x_2121, 0);
lean_inc(x_2122);
x_2123 = lean_ctor_get(x_2121, 1);
lean_inc(x_2123);
lean_dec(x_2121);
x_2124 = lean_ctor_get(x_2122, 1);
lean_inc(x_2124);
lean_dec(x_2122);
lean_inc(x_2120);
x_2125 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_5__expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_2125, 0, x_2120);
x_2126 = x_2125;
x_2127 = lean_environment_main_module(x_2120);
lean_inc(x_1439);
lean_inc(x_1438);
x_2128 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_2128, 0, x_2126);
lean_ctor_set(x_2128, 1, x_2127);
lean_ctor_set(x_2128, 2, x_2115);
lean_ctor_set(x_2128, 3, x_1438);
lean_ctor_set(x_2128, 4, x_1439);
x_2129 = l_Lean_Elab_Term_Do_ToCodeBlock_expandLiftMethod(x_12, x_2128, x_2124);
if (lean_obj_tag(x_2129) == 0)
{
lean_object* x_2130; lean_object* x_2131; lean_object* x_2132; lean_object* x_2133; lean_object* x_2134; lean_object* x_2135; lean_object* x_2136; lean_object* x_2137; lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; lean_object* x_2141; 
x_2130 = lean_ctor_get(x_2129, 0);
lean_inc(x_2130);
x_2131 = lean_ctor_get(x_2129, 1);
lean_inc(x_2131);
lean_dec(x_2129);
x_2132 = lean_st_ref_take(x_8, x_2123);
x_2133 = lean_ctor_get(x_2132, 0);
lean_inc(x_2133);
x_2134 = lean_ctor_get(x_2132, 1);
lean_inc(x_2134);
lean_dec(x_2132);
x_2135 = lean_ctor_get(x_2133, 0);
lean_inc(x_2135);
x_2136 = lean_ctor_get(x_2133, 2);
lean_inc(x_2136);
x_2137 = lean_ctor_get(x_2133, 3);
lean_inc(x_2137);
if (lean_is_exclusive(x_2133)) {
 lean_ctor_release(x_2133, 0);
 lean_ctor_release(x_2133, 1);
 lean_ctor_release(x_2133, 2);
 lean_ctor_release(x_2133, 3);
 x_2138 = x_2133;
} else {
 lean_dec_ref(x_2133);
 x_2138 = lean_box(0);
}
if (lean_is_scalar(x_2138)) {
 x_2139 = lean_alloc_ctor(0, 4, 0);
} else {
 x_2139 = x_2138;
}
lean_ctor_set(x_2139, 0, x_2135);
lean_ctor_set(x_2139, 1, x_2131);
lean_ctor_set(x_2139, 2, x_2136);
lean_ctor_set(x_2139, 3, x_2137);
x_2140 = lean_st_ref_set(x_8, x_2139, x_2134);
x_2141 = lean_ctor_get(x_2140, 1);
lean_inc(x_2141);
lean_dec(x_2140);
x_1445 = x_2130;
x_1446 = x_2141;
goto block_2113;
}
else
{
lean_object* x_2142; 
lean_dec(x_1439);
lean_dec(x_1438);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
x_2142 = lean_ctor_get(x_2129, 0);
lean_inc(x_2142);
lean_dec(x_2129);
if (lean_obj_tag(x_2142) == 0)
{
lean_object* x_2143; lean_object* x_2144; lean_object* x_2145; lean_object* x_2146; lean_object* x_2147; lean_object* x_2148; lean_object* x_2149; lean_object* x_2150; lean_object* x_2151; 
x_2143 = lean_ctor_get(x_2142, 0);
lean_inc(x_2143);
x_2144 = lean_ctor_get(x_2142, 1);
lean_inc(x_2144);
lean_dec(x_2142);
x_2145 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2145, 0, x_2144);
x_2146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2146, 0, x_2145);
x_2147 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_2143, x_2146, x_3, x_4, x_5, x_6, x_1444, x_8, x_2123);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2143);
x_2148 = lean_ctor_get(x_2147, 0);
lean_inc(x_2148);
x_2149 = lean_ctor_get(x_2147, 1);
lean_inc(x_2149);
if (lean_is_exclusive(x_2147)) {
 lean_ctor_release(x_2147, 0);
 lean_ctor_release(x_2147, 1);
 x_2150 = x_2147;
} else {
 lean_dec_ref(x_2147);
 x_2150 = lean_box(0);
}
if (lean_is_scalar(x_2150)) {
 x_2151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2151 = x_2150;
}
lean_ctor_set(x_2151, 0, x_2148);
lean_ctor_set(x_2151, 1, x_2149);
return x_2151;
}
else
{
lean_object* x_2152; lean_object* x_2153; lean_object* x_2154; lean_object* x_2155; lean_object* x_2156; 
lean_dec(x_1444);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2152 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__3___rarg(x_2123);
x_2153 = lean_ctor_get(x_2152, 0);
lean_inc(x_2153);
x_2154 = lean_ctor_get(x_2152, 1);
lean_inc(x_2154);
if (lean_is_exclusive(x_2152)) {
 lean_ctor_release(x_2152, 0);
 lean_ctor_release(x_2152, 1);
 x_2155 = x_2152;
} else {
 lean_dec_ref(x_2152);
 x_2155 = lean_box(0);
}
if (lean_is_scalar(x_2155)) {
 x_2156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2156 = x_2155;
}
lean_ctor_set(x_2156, 0, x_2153);
lean_ctor_set(x_2156, 1, x_2154);
return x_2156;
}
}
block_2113:
{
lean_object* x_1447; lean_object* x_1448; uint8_t x_1449; 
x_1447 = lean_ctor_get(x_1445, 0);
lean_inc(x_1447);
x_1448 = lean_ctor_get(x_1445, 1);
lean_inc(x_1448);
lean_dec(x_1445);
x_1449 = l_List_isEmpty___rarg(x_1447);
if (x_1449 == 0)
{
lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; 
lean_dec(x_1439);
lean_dec(x_1438);
x_1450 = lean_box(0);
if (lean_is_scalar(x_14)) {
 x_1451 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1451 = x_14;
}
lean_ctor_set(x_1451, 0, x_1448);
lean_ctor_set(x_1451, 1, x_1450);
x_1452 = l_List_append___rarg(x_1447, x_1451);
x_1453 = l_List_append___rarg(x_1452, x_13);
x_1 = x_1453;
x_7 = x_1444;
x_9 = x_1446;
goto _start;
}
else
{
lean_object* x_1455; lean_object* x_1456; uint8_t x_1457; 
lean_dec(x_1447);
lean_dec(x_14);
lean_inc(x_1448);
x_1455 = l_Lean_Syntax_getKind(x_1448);
x_1456 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__2;
x_1457 = lean_name_eq(x_1455, x_1456);
if (x_1457 == 0)
{
lean_object* x_1458; uint8_t x_1459; 
x_1458 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__4;
x_1459 = lean_name_eq(x_1455, x_1458);
if (x_1459 == 0)
{
lean_object* x_1460; uint8_t x_1461; 
x_1460 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__6;
x_1461 = lean_name_eq(x_1455, x_1460);
if (x_1461 == 0)
{
lean_object* x_1462; uint8_t x_1463; 
x_1462 = l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__2;
x_1463 = lean_name_eq(x_1455, x_1462);
if (x_1463 == 0)
{
lean_object* x_1464; uint8_t x_1465; 
x_1464 = l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__4;
x_1465 = lean_name_eq(x_1455, x_1464);
if (x_1465 == 0)
{
lean_object* x_1466; uint8_t x_1467; 
x_1466 = l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__8;
x_1467 = lean_name_eq(x_1455, x_1466);
if (x_1467 == 0)
{
lean_object* x_1468; uint8_t x_1469; 
x_1468 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1___closed__2;
x_1469 = lean_name_eq(x_1455, x_1468);
if (x_1469 == 0)
{
lean_object* x_1470; uint8_t x_1471; 
x_1470 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__2;
x_1471 = lean_name_eq(x_1455, x_1470);
if (x_1471 == 0)
{
lean_object* x_1472; uint8_t x_1473; 
x_1472 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__4;
x_1473 = lean_name_eq(x_1455, x_1472);
if (x_1473 == 0)
{
lean_object* x_1474; uint8_t x_1475; 
lean_dec(x_1439);
lean_dec(x_1438);
x_1474 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__6;
x_1475 = lean_name_eq(x_1455, x_1474);
if (x_1475 == 0)
{
lean_object* x_1476; uint8_t x_1477; 
x_1476 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__8;
x_1477 = lean_name_eq(x_1455, x_1476);
if (x_1477 == 0)
{
lean_object* x_1478; uint8_t x_1479; 
x_1478 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__10;
x_1479 = lean_name_eq(x_1455, x_1478);
if (x_1479 == 0)
{
lean_object* x_1480; uint8_t x_1481; 
x_1480 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__12;
x_1481 = lean_name_eq(x_1455, x_1480);
if (x_1481 == 0)
{
lean_object* x_1482; uint8_t x_1483; 
x_1482 = l___private_Lean_Elab_Do_9__expandDoIf___closed__2;
x_1483 = lean_name_eq(x_1455, x_1482);
if (x_1483 == 0)
{
lean_object* x_1484; uint8_t x_1485; 
x_1484 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__2;
x_1485 = lean_name_eq(x_1455, x_1484);
if (x_1485 == 0)
{
lean_object* x_1486; uint8_t x_1487; 
x_1486 = l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__4;
x_1487 = lean_name_eq(x_1455, x_1486);
if (x_1487 == 0)
{
lean_object* x_1488; uint8_t x_1489; 
x_1488 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__14;
x_1489 = lean_name_eq(x_1455, x_1488);
lean_dec(x_1455);
if (x_1489 == 0)
{
lean_object* x_1490; uint8_t x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; 
lean_dec(x_13);
x_1490 = lean_box(0);
x_1491 = 0;
x_1492 = lean_unsigned_to_nat(0u);
x_1493 = l_Lean_Syntax_formatStxAux___main(x_1490, x_1491, x_1492, x_1448);
x_1494 = lean_box(0);
x_1495 = l_Lean_Format_pretty(x_1493, x_1494);
x_1496 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1496, 0, x_1495);
x_1497 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1497, 0, x_1496);
x_1498 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__18;
x_1499 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1499, 0, x_1498);
lean_ctor_set(x_1499, 1, x_1497);
x_1500 = l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(x_1499, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1446);
lean_dec(x_8);
lean_dec(x_1444);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1500;
}
else
{
lean_object* x_1501; lean_object* x_1502; uint8_t x_1503; 
x_1501 = lean_unsigned_to_nat(0u);
x_1502 = l_Lean_Syntax_getArg(x_1448, x_1501);
x_1503 = l_List_isEmpty___rarg(x_13);
if (x_1503 == 0)
{
lean_object* x_1504; 
lean_dec(x_1448);
x_1504 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1446);
if (lean_obj_tag(x_1504) == 0)
{
lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; 
x_1505 = lean_ctor_get(x_1504, 0);
lean_inc(x_1505);
x_1506 = lean_ctor_get(x_1504, 1);
lean_inc(x_1506);
if (lean_is_exclusive(x_1504)) {
 lean_ctor_release(x_1504, 0);
 lean_ctor_release(x_1504, 1);
 x_1507 = x_1504;
} else {
 lean_dec_ref(x_1504);
 x_1507 = lean_box(0);
}
x_1508 = l_Lean_Elab_Term_Do_mkAction(x_1502, x_1505);
if (lean_is_scalar(x_1507)) {
 x_1509 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1509 = x_1507;
}
lean_ctor_set(x_1509, 0, x_1508);
lean_ctor_set(x_1509, 1, x_1506);
return x_1509;
}
else
{
lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; 
lean_dec(x_1502);
x_1510 = lean_ctor_get(x_1504, 0);
lean_inc(x_1510);
x_1511 = lean_ctor_get(x_1504, 1);
lean_inc(x_1511);
if (lean_is_exclusive(x_1504)) {
 lean_ctor_release(x_1504, 0);
 lean_ctor_release(x_1504, 1);
 x_1512 = x_1504;
} else {
 lean_dec_ref(x_1504);
 x_1512 = lean_box(0);
}
if (lean_is_scalar(x_1512)) {
 x_1513 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1513 = x_1512;
}
lean_ctor_set(x_1513, 0, x_1510);
lean_ctor_set(x_1513, 1, x_1511);
return x_1513;
}
}
else
{
lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; uint8_t x_1534; uint8_t x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; 
lean_dec(x_13);
x_1514 = lean_st_ref_take(x_8, x_1446);
x_1515 = lean_ctor_get(x_1514, 0);
lean_inc(x_1515);
x_1516 = lean_ctor_get(x_1514, 1);
lean_inc(x_1516);
lean_dec(x_1514);
x_1517 = lean_ctor_get(x_1515, 0);
lean_inc(x_1517);
x_1518 = lean_ctor_get(x_1515, 1);
lean_inc(x_1518);
x_1519 = lean_ctor_get(x_1515, 2);
lean_inc(x_1519);
x_1520 = lean_ctor_get(x_1515, 3);
lean_inc(x_1520);
if (lean_is_exclusive(x_1515)) {
 lean_ctor_release(x_1515, 0);
 lean_ctor_release(x_1515, 1);
 lean_ctor_release(x_1515, 2);
 lean_ctor_release(x_1515, 3);
 x_1521 = x_1515;
} else {
 lean_dec_ref(x_1515);
 x_1521 = lean_box(0);
}
x_1522 = lean_unsigned_to_nat(1u);
x_1523 = lean_nat_add(x_1518, x_1522);
if (lean_is_scalar(x_1521)) {
 x_1524 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1524 = x_1521;
}
lean_ctor_set(x_1524, 0, x_1517);
lean_ctor_set(x_1524, 1, x_1523);
lean_ctor_set(x_1524, 2, x_1519);
lean_ctor_set(x_1524, 3, x_1520);
x_1525 = lean_st_ref_set(x_8, x_1524, x_1516);
x_1526 = lean_ctor_get(x_1525, 1);
lean_inc(x_1526);
lean_dec(x_1525);
x_1527 = lean_ctor_get(x_3, 0);
lean_inc(x_1527);
x_1528 = lean_ctor_get(x_3, 1);
lean_inc(x_1528);
x_1529 = lean_ctor_get(x_3, 2);
lean_inc(x_1529);
x_1530 = lean_ctor_get(x_3, 3);
lean_inc(x_1530);
x_1531 = lean_ctor_get(x_3, 4);
lean_inc(x_1531);
x_1532 = lean_ctor_get(x_3, 5);
lean_inc(x_1532);
x_1533 = lean_ctor_get(x_3, 6);
lean_inc(x_1533);
x_1534 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_1535 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 x_1536 = x_3;
} else {
 lean_dec_ref(x_3);
 x_1536 = lean_box(0);
}
if (lean_is_scalar(x_1536)) {
 x_1537 = lean_alloc_ctor(0, 8, 2);
} else {
 x_1537 = x_1536;
}
lean_ctor_set(x_1537, 0, x_1527);
lean_ctor_set(x_1537, 1, x_1528);
lean_ctor_set(x_1537, 2, x_1529);
lean_ctor_set(x_1537, 3, x_1530);
lean_ctor_set(x_1537, 4, x_1531);
lean_ctor_set(x_1537, 5, x_1532);
lean_ctor_set(x_1537, 6, x_1533);
lean_ctor_set(x_1537, 7, x_1518);
lean_ctor_set_uint8(x_1537, sizeof(void*)*8, x_1534);
lean_ctor_set_uint8(x_1537, sizeof(void*)*8 + 1, x_1535);
x_1538 = l_Lean_Elab_Term_getCurrMacroScope(x_1537, x_4, x_5, x_6, x_1444, x_8, x_1526);
x_1539 = lean_ctor_get(x_1538, 0);
lean_inc(x_1539);
x_1540 = lean_ctor_get(x_1538, 1);
lean_inc(x_1540);
lean_dec(x_1538);
x_1541 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_1540);
x_1542 = lean_ctor_get(x_1541, 0);
lean_inc(x_1542);
x_1543 = lean_ctor_get(x_1541, 1);
lean_inc(x_1543);
lean_dec(x_1541);
x_1544 = l_Lean_Meta_mkArrow___rarg___closed__2;
x_1545 = l_Lean_addMacroScope(x_1542, x_1544, x_1539);
x_1546 = lean_box(0);
x_1547 = l_Lean_SourceInfo_inhabited___closed__1;
x_1548 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__2;
x_1549 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1549, 0, x_1547);
lean_ctor_set(x_1549, 1, x_1548);
lean_ctor_set(x_1549, 2, x_1545);
lean_ctor_set(x_1549, 3, x_1546);
x_1550 = l_Array_empty___closed__1;
x_1551 = lean_array_push(x_1550, x_1549);
x_1552 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
lean_inc(x_1551);
x_1553 = lean_array_push(x_1551, x_1552);
x_1554 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4;
x_1555 = lean_array_push(x_1553, x_1554);
x_1556 = lean_array_push(x_1555, x_1502);
x_1557 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
x_1558 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1558, 0, x_1557);
lean_ctor_set(x_1558, 1, x_1556);
x_1559 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_1560 = lean_array_push(x_1559, x_1558);
x_1561 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1561, 0, x_1460);
lean_ctor_set(x_1561, 1, x_1560);
x_1562 = lean_array_push(x_1550, x_1561);
x_1563 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_1564 = lean_array_push(x_1562, x_1563);
x_1565 = l_Lean_nullKind___closed__2;
x_1566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1566, 0, x_1565);
lean_ctor_set(x_1566, 1, x_1564);
x_1567 = lean_array_push(x_1550, x_1566);
x_1568 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1568, 0, x_1565);
lean_ctor_set(x_1568, 1, x_1551);
x_1569 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__20;
x_1570 = lean_array_push(x_1569, x_1568);
x_1571 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1571, 0, x_1482);
lean_ctor_set(x_1571, 1, x_1570);
x_1572 = lean_array_push(x_1550, x_1571);
x_1573 = lean_array_push(x_1572, x_1552);
x_1574 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1574, 0, x_1565);
lean_ctor_set(x_1574, 1, x_1573);
x_1575 = lean_array_push(x_1567, x_1574);
x_1576 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1576, 0, x_1565);
lean_ctor_set(x_1576, 1, x_1575);
x_1577 = lean_array_push(x_1550, x_1576);
x_1578 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4;
x_1579 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1579, 0, x_1578);
lean_ctor_set(x_1579, 1, x_1577);
x_1580 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2;
x_1581 = lean_array_push(x_1580, x_1579);
x_1582 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2;
x_1583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1583, 0, x_1582);
lean_ctor_set(x_1583, 1, x_1581);
x_1584 = l_Lean_Syntax_getArg(x_1583, x_1522);
lean_dec(x_1583);
x_1585 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_1584);
x_1586 = l_List_map___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__1(x_1448, x_1585);
lean_dec(x_1448);
x_1 = x_1586;
x_3 = x_1537;
x_7 = x_1444;
x_9 = x_1543;
goto _start;
}
}
}
else
{
lean_object* x_1588; 
lean_dec(x_1455);
x_1588 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1446);
if (lean_obj_tag(x_1588) == 0)
{
lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; 
x_1589 = lean_ctor_get(x_1588, 0);
lean_inc(x_1589);
x_1590 = lean_ctor_get(x_1588, 1);
lean_inc(x_1590);
if (lean_is_exclusive(x_1588)) {
 lean_ctor_release(x_1588, 0);
 lean_ctor_release(x_1588, 1);
 x_1591 = x_1588;
} else {
 lean_dec_ref(x_1588);
 x_1591 = lean_box(0);
}
x_1592 = l_Lean_Elab_Term_Do_mkAction(x_1448, x_1589);
if (lean_is_scalar(x_1591)) {
 x_1593 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1593 = x_1591;
}
lean_ctor_set(x_1593, 0, x_1592);
lean_ctor_set(x_1593, 1, x_1590);
return x_1593;
}
else
{
lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; 
lean_dec(x_1448);
x_1594 = lean_ctor_get(x_1588, 0);
lean_inc(x_1594);
x_1595 = lean_ctor_get(x_1588, 1);
lean_inc(x_1595);
if (lean_is_exclusive(x_1588)) {
 lean_ctor_release(x_1588, 0);
 lean_ctor_release(x_1588, 1);
 x_1596 = x_1588;
} else {
 lean_dec_ref(x_1588);
 x_1596 = lean_box(0);
}
if (lean_is_scalar(x_1596)) {
 x_1597 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1597 = x_1596;
}
lean_ctor_set(x_1597, 0, x_1594);
lean_ctor_set(x_1597, 1, x_1595);
return x_1597;
}
}
}
else
{
lean_object* x_1598; 
lean_dec(x_1455);
x_1598 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1446);
if (lean_obj_tag(x_1598) == 0)
{
lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; 
x_1599 = lean_ctor_get(x_1598, 0);
lean_inc(x_1599);
x_1600 = lean_ctor_get(x_1598, 1);
lean_inc(x_1600);
if (lean_is_exclusive(x_1598)) {
 lean_ctor_release(x_1598, 0);
 lean_ctor_release(x_1598, 1);
 x_1601 = x_1598;
} else {
 lean_dec_ref(x_1598);
 x_1601 = lean_box(0);
}
x_1602 = l_Lean_Elab_Term_Do_mkAction(x_1448, x_1599);
if (lean_is_scalar(x_1601)) {
 x_1603 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1603 = x_1601;
}
lean_ctor_set(x_1603, 0, x_1602);
lean_ctor_set(x_1603, 1, x_1600);
return x_1603;
}
else
{
lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; 
lean_dec(x_1448);
x_1604 = lean_ctor_get(x_1598, 0);
lean_inc(x_1604);
x_1605 = lean_ctor_get(x_1598, 1);
lean_inc(x_1605);
if (lean_is_exclusive(x_1598)) {
 lean_ctor_release(x_1598, 0);
 lean_ctor_release(x_1598, 1);
 x_1606 = x_1598;
} else {
 lean_dec_ref(x_1598);
 x_1606 = lean_box(0);
}
if (lean_is_scalar(x_1606)) {
 x_1607 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1607 = x_1606;
}
lean_ctor_set(x_1607, 0, x_1604);
lean_ctor_set(x_1607, 1, x_1605);
return x_1607;
}
}
}
else
{
lean_object* x_1608; 
lean_dec(x_1455);
x_1608 = l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS(x_13, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1446);
lean_dec(x_13);
if (lean_obj_tag(x_1608) == 0)
{
lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; uint8_t x_1613; 
x_1609 = lean_ctor_get(x_1608, 1);
lean_inc(x_1609);
if (lean_is_exclusive(x_1608)) {
 lean_ctor_release(x_1608, 0);
 lean_ctor_release(x_1608, 1);
 x_1610 = x_1608;
} else {
 lean_dec_ref(x_1608);
 x_1610 = lean_box(0);
}
x_1611 = lean_unsigned_to_nat(1u);
x_1612 = l_Lean_Syntax_getArg(x_1448, x_1611);
x_1613 = l_Lean_Syntax_isNone(x_1612);
if (x_1613 == 0)
{
lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; 
lean_dec(x_1444);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1614 = lean_unsigned_to_nat(0u);
x_1615 = l_Lean_Syntax_getArg(x_1612, x_1614);
lean_dec(x_1612);
x_1616 = l_Lean_Elab_Term_Do_mkReturn(x_1448, x_1615);
if (lean_is_scalar(x_1610)) {
 x_1617 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1617 = x_1610;
}
lean_ctor_set(x_1617, 0, x_1616);
lean_ctor_set(x_1617, 1, x_1609);
return x_1617;
}
else
{
lean_object* x_1618; 
lean_dec(x_1612);
lean_dec(x_1610);
x_1618 = l_Lean_Elab_Term_Do_ToCodeBlock_mkReturnUnit(x_1448, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1609);
lean_dec(x_8);
lean_dec(x_1444);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1618;
}
}
else
{
lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; 
lean_dec(x_1448);
lean_dec(x_1444);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1619 = lean_ctor_get(x_1608, 0);
lean_inc(x_1619);
x_1620 = lean_ctor_get(x_1608, 1);
lean_inc(x_1620);
if (lean_is_exclusive(x_1608)) {
 lean_ctor_release(x_1608, 0);
 lean_ctor_release(x_1608, 1);
 x_1621 = x_1608;
} else {
 lean_dec_ref(x_1608);
 x_1621 = lean_box(0);
}
if (lean_is_scalar(x_1621)) {
 x_1622 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1622 = x_1621;
}
lean_ctor_set(x_1622, 0, x_1619);
lean_ctor_set(x_1622, 1, x_1620);
return x_1622;
}
}
}
else
{
lean_object* x_1623; 
lean_dec(x_1455);
x_1623 = l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor(x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1446);
if (lean_obj_tag(x_1623) == 0)
{
lean_object* x_1624; lean_object* x_1625; 
x_1624 = lean_ctor_get(x_1623, 1);
lean_inc(x_1624);
lean_dec(x_1623);
x_1625 = l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS(x_13, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1624);
lean_dec(x_8);
lean_dec(x_1444);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_13);
if (lean_obj_tag(x_1625) == 0)
{
lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; 
x_1626 = lean_ctor_get(x_1625, 1);
lean_inc(x_1626);
if (lean_is_exclusive(x_1625)) {
 lean_ctor_release(x_1625, 0);
 lean_ctor_release(x_1625, 1);
 x_1627 = x_1625;
} else {
 lean_dec_ref(x_1625);
 x_1627 = lean_box(0);
}
x_1628 = l_Lean_Elab_Term_Do_mkContinue(x_1448);
if (lean_is_scalar(x_1627)) {
 x_1629 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1629 = x_1627;
}
lean_ctor_set(x_1629, 0, x_1628);
lean_ctor_set(x_1629, 1, x_1626);
return x_1629;
}
else
{
lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; 
lean_dec(x_1448);
x_1630 = lean_ctor_get(x_1625, 0);
lean_inc(x_1630);
x_1631 = lean_ctor_get(x_1625, 1);
lean_inc(x_1631);
if (lean_is_exclusive(x_1625)) {
 lean_ctor_release(x_1625, 0);
 lean_ctor_release(x_1625, 1);
 x_1632 = x_1625;
} else {
 lean_dec_ref(x_1625);
 x_1632 = lean_box(0);
}
if (lean_is_scalar(x_1632)) {
 x_1633 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1633 = x_1632;
}
lean_ctor_set(x_1633, 0, x_1630);
lean_ctor_set(x_1633, 1, x_1631);
return x_1633;
}
}
else
{
lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; 
lean_dec(x_1448);
lean_dec(x_1444);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1634 = lean_ctor_get(x_1623, 0);
lean_inc(x_1634);
x_1635 = lean_ctor_get(x_1623, 1);
lean_inc(x_1635);
if (lean_is_exclusive(x_1623)) {
 lean_ctor_release(x_1623, 0);
 lean_ctor_release(x_1623, 1);
 x_1636 = x_1623;
} else {
 lean_dec_ref(x_1623);
 x_1636 = lean_box(0);
}
if (lean_is_scalar(x_1636)) {
 x_1637 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1637 = x_1636;
}
lean_ctor_set(x_1637, 0, x_1634);
lean_ctor_set(x_1637, 1, x_1635);
return x_1637;
}
}
}
else
{
lean_object* x_1638; 
lean_dec(x_1455);
x_1638 = l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor(x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1446);
if (lean_obj_tag(x_1638) == 0)
{
lean_object* x_1639; lean_object* x_1640; 
x_1639 = lean_ctor_get(x_1638, 1);
lean_inc(x_1639);
lean_dec(x_1638);
x_1640 = l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS(x_13, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1639);
lean_dec(x_8);
lean_dec(x_1444);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_13);
if (lean_obj_tag(x_1640) == 0)
{
lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; 
x_1641 = lean_ctor_get(x_1640, 1);
lean_inc(x_1641);
if (lean_is_exclusive(x_1640)) {
 lean_ctor_release(x_1640, 0);
 lean_ctor_release(x_1640, 1);
 x_1642 = x_1640;
} else {
 lean_dec_ref(x_1640);
 x_1642 = lean_box(0);
}
x_1643 = l_Lean_Elab_Term_Do_mkBreak(x_1448);
if (lean_is_scalar(x_1642)) {
 x_1644 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1644 = x_1642;
}
lean_ctor_set(x_1644, 0, x_1643);
lean_ctor_set(x_1644, 1, x_1641);
return x_1644;
}
else
{
lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; 
lean_dec(x_1448);
x_1645 = lean_ctor_get(x_1640, 0);
lean_inc(x_1645);
x_1646 = lean_ctor_get(x_1640, 1);
lean_inc(x_1646);
if (lean_is_exclusive(x_1640)) {
 lean_ctor_release(x_1640, 0);
 lean_ctor_release(x_1640, 1);
 x_1647 = x_1640;
} else {
 lean_dec_ref(x_1640);
 x_1647 = lean_box(0);
}
if (lean_is_scalar(x_1647)) {
 x_1648 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1648 = x_1647;
}
lean_ctor_set(x_1648, 0, x_1645);
lean_ctor_set(x_1648, 1, x_1646);
return x_1648;
}
}
else
{
lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; 
lean_dec(x_1448);
lean_dec(x_1444);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1649 = lean_ctor_get(x_1638, 0);
lean_inc(x_1649);
x_1650 = lean_ctor_get(x_1638, 1);
lean_inc(x_1650);
if (lean_is_exclusive(x_1638)) {
 lean_ctor_release(x_1638, 0);
 lean_ctor_release(x_1638, 1);
 x_1651 = x_1638;
} else {
 lean_dec_ref(x_1638);
 x_1651 = lean_box(0);
}
if (lean_is_scalar(x_1651)) {
 x_1652 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1652 = x_1651;
}
lean_ctor_set(x_1652, 0, x_1649);
lean_ctor_set(x_1652, 1, x_1650);
return x_1652;
}
}
}
else
{
lean_object* x_1653; lean_object* x_1654; 
lean_dec(x_1455);
lean_dec(x_1448);
lean_dec(x_13);
x_1653 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__22;
x_1654 = l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(x_1653, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1446);
lean_dec(x_8);
lean_dec(x_1444);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1654;
}
}
else
{
lean_object* x_1655; lean_object* x_1656; 
lean_dec(x_1455);
lean_dec(x_1448);
lean_dec(x_13);
x_1655 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__22;
x_1656 = l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(x_1655, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1446);
lean_dec(x_8);
lean_dec(x_1444);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1656;
}
}
else
{
lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; uint8_t x_1939; 
lean_dec(x_1455);
x_1657 = lean_unsigned_to_nat(1u);
x_1658 = l_Lean_Syntax_getArg(x_1448, x_1657);
x_1659 = lean_unsigned_to_nat(3u);
x_1660 = l_Lean_Syntax_getArg(x_1448, x_1659);
x_1661 = lean_unsigned_to_nat(5u);
x_1662 = l_Lean_Syntax_getArg(x_1448, x_1661);
x_1663 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_1662);
x_1939 = l_Lean_Syntax_isIdent(x_1658);
if (x_1939 == 0)
{
lean_object* x_1940; 
x_1940 = l_Array_empty___closed__1;
x_1664 = x_1940;
goto block_1938;
}
else
{
lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; 
x_1941 = l_Lean_Syntax_getId(x_1658);
x_1942 = l_Lean_mkOptionalNode___closed__2;
x_1943 = lean_array_push(x_1942, x_1941);
x_1664 = x_1943;
goto block_1938;
}
block_1938:
{
lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; uint8_t x_1684; uint8_t x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; uint8_t x_1693; lean_object* x_1694; lean_object* x_1695; 
x_1665 = lean_st_ref_take(x_8, x_1446);
x_1666 = lean_ctor_get(x_1665, 0);
lean_inc(x_1666);
x_1667 = lean_ctor_get(x_1665, 1);
lean_inc(x_1667);
lean_dec(x_1665);
x_1668 = lean_ctor_get(x_1666, 0);
lean_inc(x_1668);
x_1669 = lean_ctor_get(x_1666, 1);
lean_inc(x_1669);
x_1670 = lean_ctor_get(x_1666, 2);
lean_inc(x_1670);
x_1671 = lean_ctor_get(x_1666, 3);
lean_inc(x_1671);
if (lean_is_exclusive(x_1666)) {
 lean_ctor_release(x_1666, 0);
 lean_ctor_release(x_1666, 1);
 lean_ctor_release(x_1666, 2);
 lean_ctor_release(x_1666, 3);
 x_1672 = x_1666;
} else {
 lean_dec_ref(x_1666);
 x_1672 = lean_box(0);
}
x_1673 = lean_nat_add(x_1669, x_1657);
if (lean_is_scalar(x_1672)) {
 x_1674 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1674 = x_1672;
}
lean_ctor_set(x_1674, 0, x_1668);
lean_ctor_set(x_1674, 1, x_1673);
lean_ctor_set(x_1674, 2, x_1670);
lean_ctor_set(x_1674, 3, x_1671);
x_1675 = lean_st_ref_set(x_8, x_1674, x_1667);
x_1676 = lean_ctor_get(x_1675, 1);
lean_inc(x_1676);
lean_dec(x_1675);
x_1677 = lean_ctor_get(x_3, 0);
lean_inc(x_1677);
x_1678 = lean_ctor_get(x_3, 1);
lean_inc(x_1678);
x_1679 = lean_ctor_get(x_3, 2);
lean_inc(x_1679);
x_1680 = lean_ctor_get(x_3, 3);
lean_inc(x_1680);
x_1681 = lean_ctor_get(x_3, 4);
lean_inc(x_1681);
x_1682 = lean_ctor_get(x_3, 5);
lean_inc(x_1682);
x_1683 = lean_ctor_get(x_3, 6);
lean_inc(x_1683);
x_1684 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_1685 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 x_1686 = x_3;
} else {
 lean_dec_ref(x_3);
 x_1686 = lean_box(0);
}
if (lean_is_scalar(x_1686)) {
 x_1687 = lean_alloc_ctor(0, 8, 2);
} else {
 x_1687 = x_1686;
}
lean_ctor_set(x_1687, 0, x_1677);
lean_ctor_set(x_1687, 1, x_1678);
lean_ctor_set(x_1687, 2, x_1679);
lean_ctor_set(x_1687, 3, x_1680);
lean_ctor_set(x_1687, 4, x_1681);
lean_ctor_set(x_1687, 5, x_1682);
lean_ctor_set(x_1687, 6, x_1683);
lean_ctor_set(x_1687, 7, x_1669);
lean_ctor_set_uint8(x_1687, sizeof(void*)*8, x_1684);
lean_ctor_set_uint8(x_1687, sizeof(void*)*8 + 1, x_1685);
x_1688 = lean_ctor_get(x_2, 0);
lean_inc(x_1688);
x_1689 = lean_ctor_get(x_2, 1);
lean_inc(x_1689);
x_1690 = lean_ctor_get(x_2, 2);
lean_inc(x_1690);
x_1691 = lean_unsigned_to_nat(0u);
x_1692 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_1664, x_1664, x_1691, x_1690);
lean_dec(x_1664);
x_1693 = 1;
x_1694 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_1694, 0, x_1688);
lean_ctor_set(x_1694, 1, x_1689);
lean_ctor_set(x_1694, 2, x_1692);
lean_ctor_set_uint8(x_1694, sizeof(void*)*3, x_1693);
lean_inc(x_8);
lean_inc(x_1444);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1687);
x_1695 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_1663, x_1694, x_1687, x_4, x_5, x_6, x_1444, x_8, x_1676);
if (lean_obj_tag(x_1695) == 0)
{
lean_object* x_1696; lean_object* x_1697; lean_object* x_1698; 
x_1696 = lean_ctor_get(x_1695, 0);
lean_inc(x_1696);
x_1697 = lean_ctor_get(x_1695, 1);
lean_inc(x_1697);
lean_dec(x_1695);
lean_inc(x_1444);
lean_inc(x_2);
x_1698 = l_Lean_Elab_Term_Do_ToCodeBlock_toForInTerm(x_1658, x_1696, x_2, x_1687, x_4, x_5, x_6, x_1444, x_8, x_1697);
if (lean_obj_tag(x_1698) == 0)
{
lean_object* x_1699; lean_object* x_1700; uint8_t x_1701; lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; lean_object* x_1925; lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; 
x_1699 = lean_ctor_get(x_1698, 0);
lean_inc(x_1699);
x_1700 = lean_ctor_get(x_1698, 1);
lean_inc(x_1700);
lean_dec(x_1698);
x_1701 = lean_ctor_get_uint8(x_1699, sizeof(void*)*2);
x_1702 = lean_ctor_get(x_1699, 0);
lean_inc(x_1702);
x_1703 = lean_ctor_get(x_1699, 1);
lean_inc(x_1703);
lean_dec(x_1699);
x_1899 = x_1702;
x_1900 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__2(x_1448, x_1691, x_1899);
x_1901 = x_1900;
x_1902 = l_Lean_Elab_Term_getCurrMacroScope(x_1687, x_4, x_5, x_6, x_1444, x_8, x_1700);
x_1903 = lean_ctor_get(x_1902, 0);
lean_inc(x_1903);
x_1904 = lean_ctor_get(x_1902, 1);
lean_inc(x_1904);
lean_dec(x_1902);
x_1905 = lean_st_ref_get(x_8, x_1904);
x_1906 = lean_ctor_get(x_1905, 0);
lean_inc(x_1906);
x_1907 = lean_ctor_get(x_1905, 1);
lean_inc(x_1907);
lean_dec(x_1905);
x_1908 = lean_ctor_get(x_1906, 0);
lean_inc(x_1908);
lean_dec(x_1906);
x_1909 = lean_st_ref_get(x_8, x_1907);
x_1910 = lean_ctor_get(x_1909, 0);
lean_inc(x_1910);
x_1911 = lean_ctor_get(x_1909, 1);
lean_inc(x_1911);
lean_dec(x_1909);
x_1912 = lean_ctor_get(x_1910, 1);
lean_inc(x_1912);
lean_dec(x_1910);
lean_inc(x_1908);
x_1913 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_5__expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_1913, 0, x_1908);
x_1914 = x_1913;
x_1915 = lean_environment_main_module(x_1908);
x_1916 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1916, 0, x_1914);
lean_ctor_set(x_1916, 1, x_1915);
lean_ctor_set(x_1916, 2, x_1903);
lean_ctor_set(x_1916, 3, x_1438);
lean_ctor_set(x_1916, 4, x_1439);
x_1917 = l___private_Lean_Elab_Do_12__mkTuple(x_1448, x_1901, x_1916, x_1912);
lean_dec(x_1901);
lean_dec(x_1448);
x_1918 = lean_ctor_get(x_1917, 0);
lean_inc(x_1918);
x_1919 = lean_ctor_get(x_1917, 1);
lean_inc(x_1919);
lean_dec(x_1917);
x_1920 = lean_st_ref_take(x_8, x_1911);
x_1921 = lean_ctor_get(x_1920, 0);
lean_inc(x_1921);
x_1922 = lean_ctor_get(x_1920, 1);
lean_inc(x_1922);
lean_dec(x_1920);
x_1923 = lean_ctor_get(x_1921, 0);
lean_inc(x_1923);
x_1924 = lean_ctor_get(x_1921, 2);
lean_inc(x_1924);
x_1925 = lean_ctor_get(x_1921, 3);
lean_inc(x_1925);
if (lean_is_exclusive(x_1921)) {
 lean_ctor_release(x_1921, 0);
 lean_ctor_release(x_1921, 1);
 lean_ctor_release(x_1921, 2);
 lean_ctor_release(x_1921, 3);
 x_1926 = x_1921;
} else {
 lean_dec_ref(x_1921);
 x_1926 = lean_box(0);
}
if (lean_is_scalar(x_1926)) {
 x_1927 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1927 = x_1926;
}
lean_ctor_set(x_1927, 0, x_1923);
lean_ctor_set(x_1927, 1, x_1919);
lean_ctor_set(x_1927, 2, x_1924);
lean_ctor_set(x_1927, 3, x_1925);
x_1928 = lean_st_ref_set(x_8, x_1927, x_1922);
x_1929 = lean_ctor_get(x_1928, 1);
lean_inc(x_1929);
lean_dec(x_1928);
x_1704 = x_1918;
x_1705 = x_1929;
goto block_1898;
block_1898:
{
lean_object* x_1706; lean_object* x_1707; 
if (x_1701 == 0)
{
lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; 
x_1713 = l_Lean_Elab_Term_getCurrMacroScope(x_1687, x_4, x_5, x_6, x_1444, x_8, x_1705);
x_1714 = lean_ctor_get(x_1713, 0);
lean_inc(x_1714);
x_1715 = lean_ctor_get(x_1713, 1);
lean_inc(x_1715);
lean_dec(x_1713);
x_1716 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_1715);
x_1717 = lean_ctor_get(x_1716, 0);
lean_inc(x_1717);
x_1718 = lean_ctor_get(x_1716, 1);
lean_inc(x_1718);
lean_dec(x_1716);
x_1719 = l_Array_empty___closed__1;
x_1720 = lean_array_push(x_1719, x_1660);
x_1721 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__23;
x_1722 = lean_array_push(x_1720, x_1721);
x_1723 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__27;
x_1724 = l_Lean_addMacroScope(x_1717, x_1723, x_1714);
x_1725 = lean_box(0);
x_1726 = l_Lean_SourceInfo_inhabited___closed__1;
x_1727 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__26;
x_1728 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1728, 0, x_1726);
lean_ctor_set(x_1728, 1, x_1727);
lean_ctor_set(x_1728, 2, x_1724);
lean_ctor_set(x_1728, 3, x_1725);
x_1729 = lean_array_push(x_1722, x_1728);
x_1730 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__13;
x_1731 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1731, 0, x_1730);
lean_ctor_set(x_1731, 1, x_1729);
x_1732 = lean_array_push(x_1719, x_1731);
lean_inc(x_1704);
x_1733 = lean_array_push(x_1719, x_1704);
x_1734 = lean_array_push(x_1719, x_1658);
x_1735 = lean_array_push(x_1734, x_1704);
x_1736 = l_Lean_nullKind___closed__2;
x_1737 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1737, 0, x_1736);
lean_ctor_set(x_1737, 1, x_1735);
x_1738 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
x_1739 = lean_array_push(x_1738, x_1737);
x_1740 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_1741 = lean_array_push(x_1739, x_1740);
x_1742 = lean_array_push(x_1741, x_1703);
x_1743 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
x_1744 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1744, 0, x_1743);
lean_ctor_set(x_1744, 1, x_1742);
lean_inc(x_1733);
x_1745 = lean_array_push(x_1733, x_1744);
x_1746 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1746, 0, x_1736);
lean_ctor_set(x_1746, 1, x_1745);
x_1747 = lean_array_push(x_1732, x_1746);
x_1748 = l_Lean_mkAppStx___closed__8;
x_1749 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1749, 0, x_1748);
lean_ctor_set(x_1749, 1, x_1747);
x_1750 = l_Lean_Elab_Term_getCurrMacroScope(x_1687, x_4, x_5, x_6, x_1444, x_8, x_1718);
x_1751 = lean_ctor_get(x_1750, 0);
lean_inc(x_1751);
x_1752 = lean_ctor_get(x_1750, 1);
lean_inc(x_1752);
lean_dec(x_1750);
x_1753 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_1752);
x_1754 = lean_ctor_get(x_1753, 0);
lean_inc(x_1754);
x_1755 = lean_ctor_get(x_1753, 1);
lean_inc(x_1755);
lean_dec(x_1753);
x_1756 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__30;
x_1757 = l_Lean_addMacroScope(x_1754, x_1756, x_1751);
x_1758 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__29;
x_1759 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1759, 0, x_1726);
lean_ctor_set(x_1759, 1, x_1758);
lean_ctor_set(x_1759, 2, x_1757);
lean_ctor_set(x_1759, 3, x_1725);
lean_inc(x_1759);
x_1760 = lean_array_push(x_1719, x_1759);
x_1761 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_1762 = lean_array_push(x_1760, x_1761);
x_1763 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4;
x_1764 = lean_array_push(x_1762, x_1763);
x_1765 = lean_array_push(x_1764, x_1749);
x_1766 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
x_1767 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1767, 0, x_1766);
lean_ctor_set(x_1767, 1, x_1765);
x_1768 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_1769 = lean_array_push(x_1768, x_1767);
x_1770 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1770, 0, x_1460);
lean_ctor_set(x_1770, 1, x_1769);
x_1771 = lean_array_push(x_1719, x_1770);
x_1772 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_1773 = lean_array_push(x_1771, x_1772);
x_1774 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1774, 0, x_1736);
lean_ctor_set(x_1774, 1, x_1773);
x_1775 = lean_array_push(x_1719, x_1774);
x_1776 = lean_array_push(x_1733, x_1761);
x_1777 = lean_array_push(x_1776, x_1761);
x_1778 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_1779 = lean_array_push(x_1777, x_1778);
x_1780 = lean_array_push(x_1779, x_1759);
x_1781 = l_Lean_Elab_Term_elabLetDeclCore___closed__2;
x_1782 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1782, 0, x_1781);
lean_ctor_set(x_1782, 1, x_1780);
x_1783 = lean_array_push(x_1719, x_1782);
x_1784 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1784, 0, x_1462);
lean_ctor_set(x_1784, 1, x_1783);
x_1785 = lean_array_push(x_1719, x_1784);
x_1786 = lean_array_push(x_1785, x_1761);
x_1787 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1787, 0, x_1736);
lean_ctor_set(x_1787, 1, x_1786);
x_1788 = lean_array_push(x_1775, x_1787);
x_1789 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1789, 0, x_1736);
lean_ctor_set(x_1789, 1, x_1788);
x_1790 = lean_array_push(x_1719, x_1789);
x_1791 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4;
x_1792 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1792, 0, x_1791);
lean_ctor_set(x_1792, 1, x_1790);
x_1793 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2;
x_1794 = lean_array_push(x_1793, x_1792);
x_1795 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2;
x_1796 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1796, 0, x_1795);
lean_ctor_set(x_1796, 1, x_1794);
x_1706 = x_1796;
x_1707 = x_1755;
goto block_1712;
}
else
{
lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; lean_object* x_1814; lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; lean_object* x_1820; lean_object* x_1821; lean_object* x_1822; lean_object* x_1823; lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; lean_object* x_1849; lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; lean_object* x_1861; lean_object* x_1862; lean_object* x_1863; lean_object* x_1864; lean_object* x_1865; lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; lean_object* x_1878; lean_object* x_1879; lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; lean_object* x_1896; lean_object* x_1897; 
x_1797 = l_Lean_Elab_Term_getCurrMacroScope(x_1687, x_4, x_5, x_6, x_1444, x_8, x_1705);
x_1798 = lean_ctor_get(x_1797, 0);
lean_inc(x_1798);
x_1799 = lean_ctor_get(x_1797, 1);
lean_inc(x_1799);
lean_dec(x_1797);
x_1800 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_1799);
x_1801 = lean_ctor_get(x_1800, 0);
lean_inc(x_1801);
x_1802 = lean_ctor_get(x_1800, 1);
lean_inc(x_1802);
lean_dec(x_1800);
x_1803 = l_Array_empty___closed__1;
x_1804 = lean_array_push(x_1803, x_1660);
x_1805 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__23;
x_1806 = lean_array_push(x_1804, x_1805);
x_1807 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__34;
x_1808 = l_Lean_addMacroScope(x_1801, x_1807, x_1798);
x_1809 = lean_box(0);
x_1810 = l_Lean_SourceInfo_inhabited___closed__1;
x_1811 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__33;
x_1812 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1812, 0, x_1810);
lean_ctor_set(x_1812, 1, x_1811);
lean_ctor_set(x_1812, 2, x_1808);
lean_ctor_set(x_1812, 3, x_1809);
x_1813 = lean_array_push(x_1806, x_1812);
x_1814 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__13;
x_1815 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1815, 0, x_1814);
lean_ctor_set(x_1815, 1, x_1813);
x_1816 = lean_array_push(x_1803, x_1815);
lean_inc(x_1704);
x_1817 = lean_array_push(x_1803, x_1704);
x_1818 = lean_array_push(x_1803, x_1658);
x_1819 = lean_array_push(x_1818, x_1704);
x_1820 = l_Lean_nullKind___closed__2;
x_1821 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1821, 0, x_1820);
lean_ctor_set(x_1821, 1, x_1819);
x_1822 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
x_1823 = lean_array_push(x_1822, x_1821);
x_1824 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_1825 = lean_array_push(x_1823, x_1824);
x_1826 = lean_array_push(x_1825, x_1703);
x_1827 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
x_1828 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1828, 0, x_1827);
lean_ctor_set(x_1828, 1, x_1826);
lean_inc(x_1817);
x_1829 = lean_array_push(x_1817, x_1828);
x_1830 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1830, 0, x_1820);
lean_ctor_set(x_1830, 1, x_1829);
x_1831 = lean_array_push(x_1816, x_1830);
x_1832 = l_Lean_mkAppStx___closed__8;
x_1833 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1833, 0, x_1832);
lean_ctor_set(x_1833, 1, x_1831);
x_1834 = l_Lean_Elab_Term_getCurrMacroScope(x_1687, x_4, x_5, x_6, x_1444, x_8, x_1802);
x_1835 = lean_ctor_get(x_1834, 0);
lean_inc(x_1835);
x_1836 = lean_ctor_get(x_1834, 1);
lean_inc(x_1836);
lean_dec(x_1834);
x_1837 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_1836);
x_1838 = lean_ctor_get(x_1837, 0);
lean_inc(x_1838);
x_1839 = lean_ctor_get(x_1837, 1);
lean_inc(x_1839);
lean_dec(x_1837);
x_1840 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__30;
x_1841 = l_Lean_addMacroScope(x_1838, x_1840, x_1835);
x_1842 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__29;
x_1843 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1843, 0, x_1810);
lean_ctor_set(x_1843, 1, x_1842);
lean_ctor_set(x_1843, 2, x_1841);
lean_ctor_set(x_1843, 3, x_1809);
x_1844 = lean_array_push(x_1803, x_1843);
x_1845 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
lean_inc(x_1844);
x_1846 = lean_array_push(x_1844, x_1845);
x_1847 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4;
x_1848 = lean_array_push(x_1846, x_1847);
x_1849 = lean_array_push(x_1848, x_1833);
x_1850 = l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2;
x_1851 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1851, 0, x_1850);
lean_ctor_set(x_1851, 1, x_1849);
x_1852 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_1853 = lean_array_push(x_1852, x_1851);
x_1854 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1854, 0, x_1460);
lean_ctor_set(x_1854, 1, x_1853);
x_1855 = lean_array_push(x_1803, x_1854);
x_1856 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__18;
x_1857 = lean_array_push(x_1855, x_1856);
x_1858 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1858, 0, x_1820);
lean_ctor_set(x_1858, 1, x_1857);
x_1859 = lean_array_push(x_1803, x_1858);
x_1860 = lean_array_push(x_1817, x_1845);
x_1861 = lean_array_push(x_1860, x_1845);
x_1862 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_1863 = lean_array_push(x_1861, x_1862);
x_1864 = lean_array_push(x_1844, x_1805);
x_1865 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__38;
lean_inc(x_1864);
x_1866 = lean_array_push(x_1864, x_1865);
x_1867 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1867, 0, x_1814);
lean_ctor_set(x_1867, 1, x_1866);
x_1868 = lean_array_push(x_1863, x_1867);
x_1869 = l_Lean_Elab_Term_elabLetDeclCore___closed__2;
x_1870 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1870, 0, x_1869);
lean_ctor_set(x_1870, 1, x_1868);
x_1871 = lean_array_push(x_1803, x_1870);
x_1872 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1872, 0, x_1462);
lean_ctor_set(x_1872, 1, x_1871);
x_1873 = lean_array_push(x_1803, x_1872);
x_1874 = lean_array_push(x_1873, x_1856);
x_1875 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1875, 0, x_1820);
lean_ctor_set(x_1875, 1, x_1874);
x_1876 = lean_array_push(x_1859, x_1875);
x_1877 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__42;
x_1878 = lean_array_push(x_1864, x_1877);
x_1879 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1879, 0, x_1814);
lean_ctor_set(x_1879, 1, x_1878);
x_1880 = lean_array_push(x_1803, x_1879);
x_1881 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1881, 0, x_1820);
lean_ctor_set(x_1881, 1, x_1880);
x_1882 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__20;
x_1883 = lean_array_push(x_1882, x_1881);
x_1884 = l___private_Lean_Elab_Do_9__expandDoIf___closed__2;
x_1885 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1885, 0, x_1884);
lean_ctor_set(x_1885, 1, x_1883);
x_1886 = lean_array_push(x_1803, x_1885);
x_1887 = lean_array_push(x_1886, x_1845);
x_1888 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1888, 0, x_1820);
lean_ctor_set(x_1888, 1, x_1887);
x_1889 = lean_array_push(x_1876, x_1888);
x_1890 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1890, 0, x_1820);
lean_ctor_set(x_1890, 1, x_1889);
x_1891 = lean_array_push(x_1803, x_1890);
x_1892 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4;
x_1893 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1893, 0, x_1892);
lean_ctor_set(x_1893, 1, x_1891);
x_1894 = l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2;
x_1895 = lean_array_push(x_1894, x_1893);
x_1896 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2;
x_1897 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1897, 0, x_1896);
lean_ctor_set(x_1897, 1, x_1895);
x_1706 = x_1897;
x_1707 = x_1839;
goto block_1712;
}
block_1712:
{
lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; 
x_1708 = l_Lean_Syntax_getArg(x_1706, x_1657);
lean_dec(x_1706);
x_1709 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_1708);
x_1710 = l_List_append___rarg(x_1709, x_13);
x_1 = x_1710;
x_3 = x_1687;
x_7 = x_1444;
x_9 = x_1707;
goto _start;
}
}
}
else
{
lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; 
lean_dec(x_1687);
lean_dec(x_1660);
lean_dec(x_1658);
lean_dec(x_1448);
lean_dec(x_1444);
lean_dec(x_1439);
lean_dec(x_1438);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1930 = lean_ctor_get(x_1698, 0);
lean_inc(x_1930);
x_1931 = lean_ctor_get(x_1698, 1);
lean_inc(x_1931);
if (lean_is_exclusive(x_1698)) {
 lean_ctor_release(x_1698, 0);
 lean_ctor_release(x_1698, 1);
 x_1932 = x_1698;
} else {
 lean_dec_ref(x_1698);
 x_1932 = lean_box(0);
}
if (lean_is_scalar(x_1932)) {
 x_1933 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1933 = x_1932;
}
lean_ctor_set(x_1933, 0, x_1930);
lean_ctor_set(x_1933, 1, x_1931);
return x_1933;
}
}
else
{
lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; 
lean_dec(x_1687);
lean_dec(x_1660);
lean_dec(x_1658);
lean_dec(x_1448);
lean_dec(x_1444);
lean_dec(x_1439);
lean_dec(x_1438);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1934 = lean_ctor_get(x_1695, 0);
lean_inc(x_1934);
x_1935 = lean_ctor_get(x_1695, 1);
lean_inc(x_1935);
if (lean_is_exclusive(x_1695)) {
 lean_ctor_release(x_1695, 0);
 lean_ctor_release(x_1695, 1);
 x_1936 = x_1695;
} else {
 lean_dec_ref(x_1695);
 x_1936 = lean_box(0);
}
if (lean_is_scalar(x_1936)) {
 x_1937 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1937 = x_1936;
}
lean_ctor_set(x_1937, 0, x_1934);
lean_ctor_set(x_1937, 1, x_1935);
return x_1937;
}
}
}
}
else
{
lean_object* x_1944; lean_object* x_1945; lean_object* x_1946; lean_object* x_1947; lean_object* x_1948; lean_object* x_1949; 
lean_dec(x_1455);
lean_dec(x_1439);
lean_dec(x_1438);
x_1944 = lean_unsigned_to_nat(1u);
x_1945 = l_Lean_Syntax_getArg(x_1448, x_1944);
x_1946 = lean_unsigned_to_nat(3u);
x_1947 = l_Lean_Syntax_getArg(x_1448, x_1946);
x_1948 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_1947);
lean_inc(x_8);
lean_inc(x_1444);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_1949 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_1948, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1446);
if (lean_obj_tag(x_1949) == 0)
{
lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; 
x_1950 = lean_ctor_get(x_1949, 0);
lean_inc(x_1950);
x_1951 = lean_ctor_get(x_1949, 1);
lean_inc(x_1951);
lean_dec(x_1949);
x_1952 = l_Lean_Elab_Term_Do_mkUnless(x_1448, x_1945, x_1950, x_3, x_4, x_5, x_6, x_1444, x_8, x_1951);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; 
lean_dec(x_1444);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1953 = lean_ctor_get(x_1952, 0);
lean_inc(x_1953);
x_1954 = lean_ctor_get(x_1952, 1);
lean_inc(x_1954);
if (lean_is_exclusive(x_1952)) {
 lean_ctor_release(x_1952, 0);
 lean_ctor_release(x_1952, 1);
 x_1955 = x_1952;
} else {
 lean_dec_ref(x_1952);
 x_1955 = lean_box(0);
}
if (lean_is_scalar(x_1955)) {
 x_1956 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1956 = x_1955;
}
lean_ctor_set(x_1956, 0, x_1953);
lean_ctor_set(x_1956, 1, x_1954);
return x_1956;
}
else
{
lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; 
x_1957 = lean_ctor_get(x_1952, 0);
lean_inc(x_1957);
x_1958 = lean_ctor_get(x_1952, 1);
lean_inc(x_1958);
lean_dec(x_1952);
lean_inc(x_8);
lean_inc(x_1444);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1959 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1958);
if (lean_obj_tag(x_1959) == 0)
{
lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; 
x_1960 = lean_ctor_get(x_1959, 0);
lean_inc(x_1960);
x_1961 = lean_ctor_get(x_1959, 1);
lean_inc(x_1961);
lean_dec(x_1959);
x_1962 = l_Lean_Elab_Term_Do_concat(x_1957, x_1960, x_3, x_4, x_5, x_6, x_1444, x_8, x_1961);
return x_1962;
}
else
{
lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; lean_object* x_1966; 
lean_dec(x_1957);
lean_dec(x_1444);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1963 = lean_ctor_get(x_1959, 0);
lean_inc(x_1963);
x_1964 = lean_ctor_get(x_1959, 1);
lean_inc(x_1964);
if (lean_is_exclusive(x_1959)) {
 lean_ctor_release(x_1959, 0);
 lean_ctor_release(x_1959, 1);
 x_1965 = x_1959;
} else {
 lean_dec_ref(x_1959);
 x_1965 = lean_box(0);
}
if (lean_is_scalar(x_1965)) {
 x_1966 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1966 = x_1965;
}
lean_ctor_set(x_1966, 0, x_1963);
lean_ctor_set(x_1966, 1, x_1964);
return x_1966;
}
}
}
else
{
lean_object* x_1967; lean_object* x_1968; lean_object* x_1969; lean_object* x_1970; 
lean_dec(x_1945);
lean_dec(x_1448);
lean_dec(x_1444);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1967 = lean_ctor_get(x_1949, 0);
lean_inc(x_1967);
x_1968 = lean_ctor_get(x_1949, 1);
lean_inc(x_1968);
if (lean_is_exclusive(x_1949)) {
 lean_ctor_release(x_1949, 0);
 lean_ctor_release(x_1949, 1);
 x_1969 = x_1949;
} else {
 lean_dec_ref(x_1949);
 x_1969 = lean_box(0);
}
if (lean_is_scalar(x_1969)) {
 x_1970 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1970 = x_1969;
}
lean_ctor_set(x_1970, 0, x_1967);
lean_ctor_set(x_1970, 1, x_1968);
return x_1970;
}
}
}
else
{
lean_object* x_1971; lean_object* x_1972; lean_object* x_1973; lean_object* x_1974; 
lean_dec(x_1455);
lean_dec(x_1439);
lean_dec(x_1438);
lean_inc(x_1448);
x_1971 = l___private_Lean_Elab_Do_10__mkDoIfView(x_1448);
x_1972 = lean_ctor_get(x_1971, 3);
lean_inc(x_1972);
x_1973 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_1972);
lean_inc(x_8);
lean_inc(x_1444);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_1974 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_1973, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1446);
if (lean_obj_tag(x_1974) == 0)
{
lean_object* x_1975; lean_object* x_1976; lean_object* x_1977; lean_object* x_1978; lean_object* x_1979; 
x_1975 = lean_ctor_get(x_1974, 0);
lean_inc(x_1975);
x_1976 = lean_ctor_get(x_1974, 1);
lean_inc(x_1976);
lean_dec(x_1974);
x_1977 = lean_ctor_get(x_1971, 4);
lean_inc(x_1977);
x_1978 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_1977);
lean_inc(x_8);
lean_inc(x_1444);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_1979 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_1978, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1976);
if (lean_obj_tag(x_1979) == 0)
{
lean_object* x_1980; lean_object* x_1981; lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; 
x_1980 = lean_ctor_get(x_1979, 0);
lean_inc(x_1980);
x_1981 = lean_ctor_get(x_1979, 1);
lean_inc(x_1981);
lean_dec(x_1979);
x_1982 = l___private_Lean_Elab_Do_9__expandDoIf(x_1448);
x_1983 = lean_ctor_get(x_1971, 1);
lean_inc(x_1983);
x_1984 = lean_ctor_get(x_1971, 2);
lean_inc(x_1984);
lean_dec(x_1971);
lean_inc(x_8);
lean_inc(x_1444);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1985 = l_Lean_Elab_Term_Do_mkIte(x_1982, x_1983, x_1984, x_1975, x_1980, x_3, x_4, x_5, x_6, x_1444, x_8, x_1981);
if (lean_obj_tag(x_1985) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; lean_object* x_1989; 
lean_dec(x_1444);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1986 = lean_ctor_get(x_1985, 0);
lean_inc(x_1986);
x_1987 = lean_ctor_get(x_1985, 1);
lean_inc(x_1987);
if (lean_is_exclusive(x_1985)) {
 lean_ctor_release(x_1985, 0);
 lean_ctor_release(x_1985, 1);
 x_1988 = x_1985;
} else {
 lean_dec_ref(x_1985);
 x_1988 = lean_box(0);
}
if (lean_is_scalar(x_1988)) {
 x_1989 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1989 = x_1988;
}
lean_ctor_set(x_1989, 0, x_1986);
lean_ctor_set(x_1989, 1, x_1987);
return x_1989;
}
else
{
lean_object* x_1990; lean_object* x_1991; lean_object* x_1992; 
x_1990 = lean_ctor_get(x_1985, 0);
lean_inc(x_1990);
x_1991 = lean_ctor_get(x_1985, 1);
lean_inc(x_1991);
lean_dec(x_1985);
lean_inc(x_8);
lean_inc(x_1444);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1992 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1991);
if (lean_obj_tag(x_1992) == 0)
{
lean_object* x_1993; lean_object* x_1994; lean_object* x_1995; 
x_1993 = lean_ctor_get(x_1992, 0);
lean_inc(x_1993);
x_1994 = lean_ctor_get(x_1992, 1);
lean_inc(x_1994);
lean_dec(x_1992);
x_1995 = l_Lean_Elab_Term_Do_concat(x_1990, x_1993, x_3, x_4, x_5, x_6, x_1444, x_8, x_1994);
return x_1995;
}
else
{
lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; 
lean_dec(x_1990);
lean_dec(x_1444);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1996 = lean_ctor_get(x_1992, 0);
lean_inc(x_1996);
x_1997 = lean_ctor_get(x_1992, 1);
lean_inc(x_1997);
if (lean_is_exclusive(x_1992)) {
 lean_ctor_release(x_1992, 0);
 lean_ctor_release(x_1992, 1);
 x_1998 = x_1992;
} else {
 lean_dec_ref(x_1992);
 x_1998 = lean_box(0);
}
if (lean_is_scalar(x_1998)) {
 x_1999 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1999 = x_1998;
}
lean_ctor_set(x_1999, 0, x_1996);
lean_ctor_set(x_1999, 1, x_1997);
return x_1999;
}
}
}
else
{
lean_object* x_2000; lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; 
lean_dec(x_1444);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2000 = lean_ctor_get(x_1985, 0);
lean_inc(x_2000);
x_2001 = lean_ctor_get(x_1985, 1);
lean_inc(x_2001);
if (lean_is_exclusive(x_1985)) {
 lean_ctor_release(x_1985, 0);
 lean_ctor_release(x_1985, 1);
 x_2002 = x_1985;
} else {
 lean_dec_ref(x_1985);
 x_2002 = lean_box(0);
}
if (lean_is_scalar(x_2002)) {
 x_2003 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2003 = x_2002;
}
lean_ctor_set(x_2003, 0, x_2000);
lean_ctor_set(x_2003, 1, x_2001);
return x_2003;
}
}
else
{
lean_object* x_2004; lean_object* x_2005; lean_object* x_2006; lean_object* x_2007; 
lean_dec(x_1975);
lean_dec(x_1971);
lean_dec(x_1448);
lean_dec(x_1444);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2004 = lean_ctor_get(x_1979, 0);
lean_inc(x_2004);
x_2005 = lean_ctor_get(x_1979, 1);
lean_inc(x_2005);
if (lean_is_exclusive(x_1979)) {
 lean_ctor_release(x_1979, 0);
 lean_ctor_release(x_1979, 1);
 x_2006 = x_1979;
} else {
 lean_dec_ref(x_1979);
 x_2006 = lean_box(0);
}
if (lean_is_scalar(x_2006)) {
 x_2007 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2007 = x_2006;
}
lean_ctor_set(x_2007, 0, x_2004);
lean_ctor_set(x_2007, 1, x_2005);
return x_2007;
}
}
else
{
lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; lean_object* x_2011; 
lean_dec(x_1971);
lean_dec(x_1448);
lean_dec(x_1444);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2008 = lean_ctor_get(x_1974, 0);
lean_inc(x_2008);
x_2009 = lean_ctor_get(x_1974, 1);
lean_inc(x_2009);
if (lean_is_exclusive(x_1974)) {
 lean_ctor_release(x_1974, 0);
 lean_ctor_release(x_1974, 1);
 x_2010 = x_1974;
} else {
 lean_dec_ref(x_1974);
 x_2010 = lean_box(0);
}
if (lean_is_scalar(x_2010)) {
 x_2011 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2011 = x_2010;
}
lean_ctor_set(x_2011, 0, x_2008);
lean_ctor_set(x_2011, 1, x_2009);
return x_2011;
}
}
}
else
{
lean_object* x_2012; lean_object* x_2013; 
lean_dec(x_1455);
lean_dec(x_1448);
lean_dec(x_1439);
lean_dec(x_1438);
lean_dec(x_13);
x_2012 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__22;
x_2013 = l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(x_2012, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1446);
lean_dec(x_8);
lean_dec(x_1444);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_2013;
}
}
else
{
lean_object* x_2014; lean_object* x_2015; 
lean_dec(x_1455);
lean_dec(x_1448);
lean_dec(x_1439);
lean_dec(x_1438);
lean_dec(x_13);
x_2014 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__22;
x_2015 = l_Lean_throwError___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__1___rarg(x_2014, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_1446);
lean_dec(x_8);
lean_dec(x_1444);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_2015;
}
}
else
{
lean_object* x_2016; 
lean_dec(x_1455);
lean_dec(x_1439);
lean_dec(x_1438);
lean_inc(x_8);
lean_inc(x_1444);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2016 = l_Lean_Elab_Term_Do_getDoReassignVars(x_1448, x_3, x_4, x_5, x_6, x_1444, x_8, x_1446);
if (lean_obj_tag(x_2016) == 0)
{
lean_object* x_2017; lean_object* x_2018; lean_object* x_2019; lean_object* x_2020; 
x_2017 = lean_ctor_get(x_2016, 0);
lean_inc(x_2017);
x_2018 = lean_ctor_get(x_2016, 1);
lean_inc(x_2018);
lean_dec(x_2016);
x_2019 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_2020 = l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2(x_2, x_2017, x_2019, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_2018);
if (lean_obj_tag(x_2020) == 0)
{
lean_object* x_2021; lean_object* x_2022; 
x_2021 = lean_ctor_get(x_2020, 1);
lean_inc(x_2021);
lean_dec(x_2020);
lean_inc(x_8);
lean_inc(x_1444);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2022 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_2, x_3, x_4, x_5, x_6, x_1444, x_8, x_2021);
if (lean_obj_tag(x_2022) == 0)
{
lean_object* x_2023; lean_object* x_2024; lean_object* x_2025; 
x_2023 = lean_ctor_get(x_2022, 0);
lean_inc(x_2023);
x_2024 = lean_ctor_get(x_2022, 1);
lean_inc(x_2024);
lean_dec(x_2022);
x_2025 = l_Lean_Elab_Term_Do_mkReassignCore(x_2017, x_1448, x_2023, x_3, x_4, x_5, x_6, x_1444, x_8, x_2024);
return x_2025;
}
else
{
lean_object* x_2026; lean_object* x_2027; lean_object* x_2028; lean_object* x_2029; 
lean_dec(x_2017);
lean_dec(x_1448);
lean_dec(x_1444);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2026 = lean_ctor_get(x_2022, 0);
lean_inc(x_2026);
x_2027 = lean_ctor_get(x_2022, 1);
lean_inc(x_2027);
if (lean_is_exclusive(x_2022)) {
 lean_ctor_release(x_2022, 0);
 lean_ctor_release(x_2022, 1);
 x_2028 = x_2022;
} else {
 lean_dec_ref(x_2022);
 x_2028 = lean_box(0);
}
if (lean_is_scalar(x_2028)) {
 x_2029 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2029 = x_2028;
}
lean_ctor_set(x_2029, 0, x_2026);
lean_ctor_set(x_2029, 1, x_2027);
return x_2029;
}
}
else
{
lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; lean_object* x_2033; 
lean_dec(x_2017);
lean_dec(x_1448);
lean_dec(x_1444);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2030 = lean_ctor_get(x_2020, 0);
lean_inc(x_2030);
x_2031 = lean_ctor_get(x_2020, 1);
lean_inc(x_2031);
if (lean_is_exclusive(x_2020)) {
 lean_ctor_release(x_2020, 0);
 lean_ctor_release(x_2020, 1);
 x_2032 = x_2020;
} else {
 lean_dec_ref(x_2020);
 x_2032 = lean_box(0);
}
if (lean_is_scalar(x_2032)) {
 x_2033 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2033 = x_2032;
}
lean_ctor_set(x_2033, 0, x_2030);
lean_ctor_set(x_2033, 1, x_2031);
return x_2033;
}
}
else
{
lean_object* x_2034; lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; 
lean_dec(x_1448);
lean_dec(x_1444);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2034 = lean_ctor_get(x_2016, 0);
lean_inc(x_2034);
x_2035 = lean_ctor_get(x_2016, 1);
lean_inc(x_2035);
if (lean_is_exclusive(x_2016)) {
 lean_ctor_release(x_2016, 0);
 lean_ctor_release(x_2016, 1);
 x_2036 = x_2016;
} else {
 lean_dec_ref(x_2016);
 x_2036 = lean_box(0);
}
if (lean_is_scalar(x_2036)) {
 x_2037 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2037 = x_2036;
}
lean_ctor_set(x_2037, 0, x_2034);
lean_ctor_set(x_2037, 1, x_2035);
return x_2037;
}
}
}
else
{
lean_object* x_2038; 
lean_dec(x_1455);
lean_dec(x_1439);
lean_dec(x_1438);
lean_inc(x_8);
lean_inc(x_1444);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2038 = l_Lean_Elab_Term_Do_getDoLetArrowVars(x_1448, x_3, x_4, x_5, x_6, x_1444, x_8, x_1446);
if (lean_obj_tag(x_2038) == 0)
{
lean_object* x_2039; lean_object* x_2040; lean_object* x_2041; lean_object* x_2042; lean_object* x_2043; uint8_t x_2044; lean_object* x_2045; lean_object* x_2046; lean_object* x_2047; lean_object* x_2048; lean_object* x_2049; 
x_2039 = lean_ctor_get(x_2038, 0);
lean_inc(x_2039);
x_2040 = lean_ctor_get(x_2038, 1);
lean_inc(x_2040);
lean_dec(x_2038);
x_2041 = lean_ctor_get(x_2, 0);
lean_inc(x_2041);
x_2042 = lean_ctor_get(x_2, 1);
lean_inc(x_2042);
x_2043 = lean_ctor_get(x_2, 2);
lean_inc(x_2043);
x_2044 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_2045 = x_2;
} else {
 lean_dec_ref(x_2);
 x_2045 = lean_box(0);
}
x_2046 = lean_unsigned_to_nat(0u);
x_2047 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_2039, x_2039, x_2046, x_2043);
if (lean_is_scalar(x_2045)) {
 x_2048 = lean_alloc_ctor(0, 3, 1);
} else {
 x_2048 = x_2045;
}
lean_ctor_set(x_2048, 0, x_2041);
lean_ctor_set(x_2048, 1, x_2042);
lean_ctor_set(x_2048, 2, x_2047);
lean_ctor_set_uint8(x_2048, sizeof(void*)*3, x_2044);
x_2049 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_2048, x_3, x_4, x_5, x_6, x_1444, x_8, x_2040);
if (lean_obj_tag(x_2049) == 0)
{
lean_object* x_2050; lean_object* x_2051; lean_object* x_2052; lean_object* x_2053; lean_object* x_2054; 
x_2050 = lean_ctor_get(x_2049, 0);
lean_inc(x_2050);
x_2051 = lean_ctor_get(x_2049, 1);
lean_inc(x_2051);
if (lean_is_exclusive(x_2049)) {
 lean_ctor_release(x_2049, 0);
 lean_ctor_release(x_2049, 1);
 x_2052 = x_2049;
} else {
 lean_dec_ref(x_2049);
 x_2052 = lean_box(0);
}
x_2053 = l_Lean_Elab_Term_Do_mkVarDeclCore(x_2039, x_1448, x_2050);
if (lean_is_scalar(x_2052)) {
 x_2054 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2054 = x_2052;
}
lean_ctor_set(x_2054, 0, x_2053);
lean_ctor_set(x_2054, 1, x_2051);
return x_2054;
}
else
{
lean_object* x_2055; lean_object* x_2056; lean_object* x_2057; lean_object* x_2058; 
lean_dec(x_2039);
lean_dec(x_1448);
x_2055 = lean_ctor_get(x_2049, 0);
lean_inc(x_2055);
x_2056 = lean_ctor_get(x_2049, 1);
lean_inc(x_2056);
if (lean_is_exclusive(x_2049)) {
 lean_ctor_release(x_2049, 0);
 lean_ctor_release(x_2049, 1);
 x_2057 = x_2049;
} else {
 lean_dec_ref(x_2049);
 x_2057 = lean_box(0);
}
if (lean_is_scalar(x_2057)) {
 x_2058 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2058 = x_2057;
}
lean_ctor_set(x_2058, 0, x_2055);
lean_ctor_set(x_2058, 1, x_2056);
return x_2058;
}
}
else
{
lean_object* x_2059; lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; 
lean_dec(x_1448);
lean_dec(x_1444);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2059 = lean_ctor_get(x_2038, 0);
lean_inc(x_2059);
x_2060 = lean_ctor_get(x_2038, 1);
lean_inc(x_2060);
if (lean_is_exclusive(x_2038)) {
 lean_ctor_release(x_2038, 0);
 lean_ctor_release(x_2038, 1);
 x_2061 = x_2038;
} else {
 lean_dec_ref(x_2038);
 x_2061 = lean_box(0);
}
if (lean_is_scalar(x_2061)) {
 x_2062 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2062 = x_2061;
}
lean_ctor_set(x_2062, 0, x_2059);
lean_ctor_set(x_2062, 1, x_2060);
return x_2062;
}
}
}
else
{
lean_object* x_2063; 
lean_dec(x_1455);
lean_dec(x_1439);
lean_dec(x_1438);
lean_inc(x_8);
lean_inc(x_1444);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2063 = l_Lean_Elab_Term_Do_getDoLetRecVars(x_1448, x_3, x_4, x_5, x_6, x_1444, x_8, x_1446);
if (lean_obj_tag(x_2063) == 0)
{
lean_object* x_2064; lean_object* x_2065; lean_object* x_2066; lean_object* x_2067; lean_object* x_2068; uint8_t x_2069; lean_object* x_2070; lean_object* x_2071; lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; 
x_2064 = lean_ctor_get(x_2063, 0);
lean_inc(x_2064);
x_2065 = lean_ctor_get(x_2063, 1);
lean_inc(x_2065);
lean_dec(x_2063);
x_2066 = lean_ctor_get(x_2, 0);
lean_inc(x_2066);
x_2067 = lean_ctor_get(x_2, 1);
lean_inc(x_2067);
x_2068 = lean_ctor_get(x_2, 2);
lean_inc(x_2068);
x_2069 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_2070 = x_2;
} else {
 lean_dec_ref(x_2);
 x_2070 = lean_box(0);
}
x_2071 = lean_unsigned_to_nat(0u);
x_2072 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_2064, x_2064, x_2071, x_2068);
if (lean_is_scalar(x_2070)) {
 x_2073 = lean_alloc_ctor(0, 3, 1);
} else {
 x_2073 = x_2070;
}
lean_ctor_set(x_2073, 0, x_2066);
lean_ctor_set(x_2073, 1, x_2067);
lean_ctor_set(x_2073, 2, x_2072);
lean_ctor_set_uint8(x_2073, sizeof(void*)*3, x_2069);
x_2074 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_2073, x_3, x_4, x_5, x_6, x_1444, x_8, x_2065);
if (lean_obj_tag(x_2074) == 0)
{
lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; lean_object* x_2079; 
x_2075 = lean_ctor_get(x_2074, 0);
lean_inc(x_2075);
x_2076 = lean_ctor_get(x_2074, 1);
lean_inc(x_2076);
if (lean_is_exclusive(x_2074)) {
 lean_ctor_release(x_2074, 0);
 lean_ctor_release(x_2074, 1);
 x_2077 = x_2074;
} else {
 lean_dec_ref(x_2074);
 x_2077 = lean_box(0);
}
x_2078 = l_Lean_Elab_Term_Do_mkVarDeclCore(x_2064, x_1448, x_2075);
if (lean_is_scalar(x_2077)) {
 x_2079 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2079 = x_2077;
}
lean_ctor_set(x_2079, 0, x_2078);
lean_ctor_set(x_2079, 1, x_2076);
return x_2079;
}
else
{
lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; lean_object* x_2083; 
lean_dec(x_2064);
lean_dec(x_1448);
x_2080 = lean_ctor_get(x_2074, 0);
lean_inc(x_2080);
x_2081 = lean_ctor_get(x_2074, 1);
lean_inc(x_2081);
if (lean_is_exclusive(x_2074)) {
 lean_ctor_release(x_2074, 0);
 lean_ctor_release(x_2074, 1);
 x_2082 = x_2074;
} else {
 lean_dec_ref(x_2074);
 x_2082 = lean_box(0);
}
if (lean_is_scalar(x_2082)) {
 x_2083 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2083 = x_2082;
}
lean_ctor_set(x_2083, 0, x_2080);
lean_ctor_set(x_2083, 1, x_2081);
return x_2083;
}
}
else
{
lean_object* x_2084; lean_object* x_2085; lean_object* x_2086; lean_object* x_2087; 
lean_dec(x_1448);
lean_dec(x_1444);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2084 = lean_ctor_get(x_2063, 0);
lean_inc(x_2084);
x_2085 = lean_ctor_get(x_2063, 1);
lean_inc(x_2085);
if (lean_is_exclusive(x_2063)) {
 lean_ctor_release(x_2063, 0);
 lean_ctor_release(x_2063, 1);
 x_2086 = x_2063;
} else {
 lean_dec_ref(x_2063);
 x_2086 = lean_box(0);
}
if (lean_is_scalar(x_2086)) {
 x_2087 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2087 = x_2086;
}
lean_ctor_set(x_2087, 0, x_2084);
lean_ctor_set(x_2087, 1, x_2085);
return x_2087;
}
}
}
else
{
lean_object* x_2088; 
lean_dec(x_1455);
lean_dec(x_1439);
lean_dec(x_1438);
lean_inc(x_8);
lean_inc(x_1444);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2088 = l_Lean_Elab_Term_Do_getDoLetVars(x_1448, x_3, x_4, x_5, x_6, x_1444, x_8, x_1446);
if (lean_obj_tag(x_2088) == 0)
{
lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; uint8_t x_2094; lean_object* x_2095; lean_object* x_2096; lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; 
x_2089 = lean_ctor_get(x_2088, 0);
lean_inc(x_2089);
x_2090 = lean_ctor_get(x_2088, 1);
lean_inc(x_2090);
lean_dec(x_2088);
x_2091 = lean_ctor_get(x_2, 0);
lean_inc(x_2091);
x_2092 = lean_ctor_get(x_2, 1);
lean_inc(x_2092);
x_2093 = lean_ctor_get(x_2, 2);
lean_inc(x_2093);
x_2094 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_2095 = x_2;
} else {
 lean_dec_ref(x_2);
 x_2095 = lean_box(0);
}
x_2096 = lean_unsigned_to_nat(0u);
x_2097 = l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_insertVars___spec__1(x_2089, x_2089, x_2096, x_2093);
if (lean_is_scalar(x_2095)) {
 x_2098 = lean_alloc_ctor(0, 3, 1);
} else {
 x_2098 = x_2095;
}
lean_ctor_set(x_2098, 0, x_2091);
lean_ctor_set(x_2098, 1, x_2092);
lean_ctor_set(x_2098, 2, x_2097);
lean_ctor_set_uint8(x_2098, sizeof(void*)*3, x_2094);
x_2099 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_13, x_2098, x_3, x_4, x_5, x_6, x_1444, x_8, x_2090);
if (lean_obj_tag(x_2099) == 0)
{
lean_object* x_2100; lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; lean_object* x_2104; 
x_2100 = lean_ctor_get(x_2099, 0);
lean_inc(x_2100);
x_2101 = lean_ctor_get(x_2099, 1);
lean_inc(x_2101);
if (lean_is_exclusive(x_2099)) {
 lean_ctor_release(x_2099, 0);
 lean_ctor_release(x_2099, 1);
 x_2102 = x_2099;
} else {
 lean_dec_ref(x_2099);
 x_2102 = lean_box(0);
}
x_2103 = l_Lean_Elab_Term_Do_mkVarDeclCore(x_2089, x_1448, x_2100);
if (lean_is_scalar(x_2102)) {
 x_2104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2104 = x_2102;
}
lean_ctor_set(x_2104, 0, x_2103);
lean_ctor_set(x_2104, 1, x_2101);
return x_2104;
}
else
{
lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; 
lean_dec(x_2089);
lean_dec(x_1448);
x_2105 = lean_ctor_get(x_2099, 0);
lean_inc(x_2105);
x_2106 = lean_ctor_get(x_2099, 1);
lean_inc(x_2106);
if (lean_is_exclusive(x_2099)) {
 lean_ctor_release(x_2099, 0);
 lean_ctor_release(x_2099, 1);
 x_2107 = x_2099;
} else {
 lean_dec_ref(x_2099);
 x_2107 = lean_box(0);
}
if (lean_is_scalar(x_2107)) {
 x_2108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2108 = x_2107;
}
lean_ctor_set(x_2108, 0, x_2105);
lean_ctor_set(x_2108, 1, x_2106);
return x_2108;
}
}
else
{
lean_object* x_2109; lean_object* x_2110; lean_object* x_2111; lean_object* x_2112; 
lean_dec(x_1448);
lean_dec(x_1444);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2109 = lean_ctor_get(x_2088, 0);
lean_inc(x_2109);
x_2110 = lean_ctor_get(x_2088, 1);
lean_inc(x_2110);
if (lean_is_exclusive(x_2088)) {
 lean_ctor_release(x_2088, 0);
 lean_ctor_release(x_2088, 1);
 x_2111 = x_2088;
} else {
 lean_dec_ref(x_2088);
 x_2111 = lean_box(0);
}
if (lean_is_scalar(x_2111)) {
 x_2112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2112 = x_2111;
}
lean_ctor_set(x_2112, 0, x_2109);
lean_ctor_set(x_2112, 1, x_2110);
return x_2112;
}
}
}
}
}
}
}
}
lean_object* l_List_map___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_Do_ToCodeBlock_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l___private_Lean_Elab_Do_7__getDoSeqElems(x_11);
x_13 = l_Lean_NameSet_empty;
x_14 = 0;
x_15 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_14);
x_16 = l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main(x_12, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
lean_object* _init_l___private_Lean_Elab_Do_16__mkMonadAlias___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_FirstTokens_toStr___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Do_16__mkMonadAlias___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Do_16__mkMonadAlias___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Do_16__mkMonadAlias___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("m");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Do_16__mkMonadAlias___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Do_16__mkMonadAlias___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Do_16__mkMonadAlias___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Do_16__mkMonadAlias___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_Do_16__mkMonadAlias___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_Do_16__mkMonadAlias___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Do_16__mkMonadAlias___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Do_16__mkMonadAlias(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Elab_Do_16__mkMonadAlias___closed__6;
x_16 = l_Lean_addMacroScope(x_13, x_15, x_10);
x_17 = lean_box(0);
x_18 = l_Lean_SourceInfo_inhabited___closed__1;
x_19 = l___private_Lean_Elab_Do_16__mkMonadAlias___closed__5;
x_20 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_17);
x_21 = l___private_Lean_Elab_Do_16__mkMonadAlias___closed__2;
x_22 = lean_array_push(x_21, x_20);
x_23 = l___regBuiltin_Lean_Elab_Term_elabSyntheticHole___closed__2;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_25 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_24);
x_30 = l_Lean_Elab_Term_elabTerm(x_24, x_28, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Expr_mvarId_x21(x_31);
lean_dec(x_31);
x_34 = l_Lean_Meta_assignExprMVar___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(x_33, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_24);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_30, 0);
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_30);
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
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_25);
if (x_43 == 0)
{
return x_25;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_25, 0);
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_25);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Elab_Term_Do_elabDo___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_checkTraceOption(x_9, x_1);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Do_elabDo___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(x_2, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_8, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 3);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_12);
lean_inc(x_10);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Std_PersistentArray_push___rarg(x_21, x_23);
lean_ctor_set(x_16, 0, x_24);
x_25 = lean_st_ref_set(x_8, x_15, x_17);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
x_33 = lean_ctor_get(x_16, 0);
lean_inc(x_33);
lean_dec(x_16);
x_34 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_12);
lean_inc(x_10);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_10);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Std_PersistentArray_push___rarg(x_33, x_35);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_32);
lean_ctor_set(x_15, 3, x_37);
x_38 = lean_st_ref_set(x_8, x_15, x_17);
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
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_43 = lean_ctor_get(x_15, 0);
x_44 = lean_ctor_get(x_15, 1);
x_45 = lean_ctor_get(x_15, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_15);
x_46 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
x_47 = lean_ctor_get(x_16, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_48 = x_16;
} else {
 lean_dec_ref(x_16);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_12);
lean_inc(x_10);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_10);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Std_PersistentArray_push___rarg(x_47, x_50);
if (lean_is_scalar(x_48)) {
 x_52 = lean_alloc_ctor(0, 1, 1);
} else {
 x_52 = x_48;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_46);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_43);
lean_ctor_set(x_53, 1, x_44);
lean_ctor_set(x_53, 2, x_45);
lean_ctor_set(x_53, 3, x_52);
x_54 = lean_st_ref_set(x_8, x_53, x_17);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
}
lean_object* l_Lean_MonadTracer_trace___at_Lean_Elab_Term_Do_elabDo___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*1);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
lean_inc(x_1);
x_21 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Elab_Term_Do_elabDo___spec__2(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_box(0);
x_32 = lean_apply_1(x_2, x_31);
x_33 = l_Lean_addTrace___at_Lean_Elab_Term_Do_elabDo___spec__3(x_1, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
return x_33;
}
}
}
}
lean_object* l_Lean_Elab_Term_Do_elabDo___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_Do_elabDo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_6__regTraceClasses___closed__1;
x_2 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_Do_elabDo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_2);
x_10 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_12 = l___private_Lean_Elab_Do_3__extractBind(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_15);
x_16 = l___private_Lean_Elab_Do_16__mkMonadAlias(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_17);
lean_inc(x_1);
x_19 = l_Lean_Elab_Term_Do_ToCodeBlock_run(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_54 = lean_ctor_get(x_20, 0);
lean_inc(x_54);
lean_dec(x_20);
x_55 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_21);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_st_ref_get(x_8, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_st_ref_get(x_8, x_60);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_7, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_7, 2);
lean_inc(x_67);
lean_inc(x_61);
x_68 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_5__expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_68, 0, x_61);
x_69 = x_68;
x_70 = lean_environment_main_module(x_61);
x_71 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_56);
lean_ctor_set(x_71, 3, x_66);
lean_ctor_set(x_71, 4, x_67);
x_72 = l_Array_empty___closed__1;
x_73 = lean_box(0);
x_74 = l_Lean_Elab_Term_Do_ToTerm_run(x_54, x_17, x_72, x_73, x_71, x_65);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_st_ref_take(x_8, x_64);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_78, 1);
lean_dec(x_81);
lean_ctor_set(x_78, 1, x_76);
x_82 = lean_st_ref_set(x_8, x_78, x_79);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_22 = x_75;
x_23 = x_83;
goto block_53;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_78, 0);
x_85 = lean_ctor_get(x_78, 2);
x_86 = lean_ctor_get(x_78, 3);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_78);
x_87 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_76);
lean_ctor_set(x_87, 2, x_85);
lean_ctor_set(x_87, 3, x_86);
x_88 = lean_st_ref_set(x_8, x_87, x_79);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_22 = x_75;
x_23 = x_89;
goto block_53;
}
}
else
{
lean_object* x_90; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_1);
x_90 = lean_ctor_get(x_74, 0);
lean_inc(x_90);
lean_dec(x_74);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_91, x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_64);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_91);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
return x_95;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_95);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
lean_object* x_100; uint8_t x_101; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_100 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__2___rarg(x_64);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
return x_100;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_100);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
block_53:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_inc(x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Do_elabDo___lambda__1___boxed), 2, 1);
lean_closure_set(x_24, 0, x_22);
x_25 = l_Lean_Elab_Term_Do_elabDo___closed__1;
x_26 = l_Lean_MonadTracer_trace___at_Lean_Elab_Term_Do_elabDo___spec__1(x_25, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_dec(x_13);
x_29 = l_Lean_mkApp(x_15, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_box(0);
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_3, 6);
lean_inc(x_22);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_22);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_3, 6, x_35);
x_36 = 1;
x_37 = l_Lean_Elab_Term_elabTermEnsuringType(x_22, x_30, x_36, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_3, 0);
x_39 = lean_ctor_get(x_3, 1);
x_40 = lean_ctor_get(x_3, 2);
x_41 = lean_ctor_get(x_3, 3);
x_42 = lean_ctor_get(x_3, 4);
x_43 = lean_ctor_get(x_3, 5);
x_44 = lean_ctor_get(x_3, 6);
x_45 = lean_ctor_get(x_3, 7);
x_46 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_47 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_3);
lean_inc(x_22);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_22);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
x_50 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_50, 0, x_38);
lean_ctor_set(x_50, 1, x_39);
lean_ctor_set(x_50, 2, x_40);
lean_ctor_set(x_50, 3, x_41);
lean_ctor_set(x_50, 4, x_42);
lean_ctor_set(x_50, 5, x_43);
lean_ctor_set(x_50, 6, x_49);
lean_ctor_set(x_50, 7, x_45);
lean_ctor_set_uint8(x_50, sizeof(void*)*8, x_46);
lean_ctor_set_uint8(x_50, sizeof(void*)*8 + 1, x_47);
x_51 = 1;
x_52 = l_Lean_Elab_Term_elabTermEnsuringType(x_22, x_30, x_51, x_31, x_50, x_4, x_5, x_6, x_7, x_8, x_27);
return x_52;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_19);
if (x_105 == 0)
{
return x_19;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_19, 0);
x_107 = lean_ctor_get(x_19, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_19);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_16);
if (x_109 == 0)
{
return x_16;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_16, 0);
x_111 = lean_ctor_get(x_16, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_16);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_12);
if (x_113 == 0)
{
return x_12;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_12, 0);
x_115 = lean_ctor_get(x_12, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_12);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_10);
if (x_117 == 0)
{
return x_10;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_10, 0);
x_119 = lean_ctor_get(x_10, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_10);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Elab_Term_Do_elabDo___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Elab_Term_Do_elabDo___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Do_elabDo___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at_Lean_Elab_Term_Do_elabDo___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_MonadTracer_trace___at_Lean_Elab_Term_Do_elabDo___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MonadTracer_trace___at_Lean_Elab_Term_Do_elabDo___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_Do_elabDo___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_Do_elabDo___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_Do_elabDo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Do_elabDo), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_Do_elabDo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_Do_elabDo___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Do_17__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_Do_elabDo___closed__1;
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
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_Binders(lean_object*);
lean_object* initialize_Lean_Elab_Quotation(lean_object*);
lean_object* initialize_Lean_Elab_Match(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Do(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Quotation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Match(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabLiftMethod___closed__1 = _init_l_Lean_Elab_Term_elabLiftMethod___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabLiftMethod___closed__1);
l_Lean_Elab_Term_elabLiftMethod___closed__2 = _init_l_Lean_Elab_Term_elabLiftMethod___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabLiftMethod___closed__2);
l_Lean_Elab_Term_elabLiftMethod___closed__3 = _init_l_Lean_Elab_Term_elabLiftMethod___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabLiftMethod___closed__3);
l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__1);
l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__2);
l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabLiftMethod___closed__3);
res = l___regBuiltin_Lean_Elab_Term_elabLiftMethod(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__1 = _init_l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__1);
l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2 = _init_l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__2);
l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__3 = _init_l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__3);
l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4 = _init_l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__4);
l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__5 = _init_l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__5);
l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__6 = _init_l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Do_1__hasLiftMethod___main___closed__6);
l___private_Lean_Elab_Do_2__mkIdBindFor___closed__1 = _init_l___private_Lean_Elab_Do_2__mkIdBindFor___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Do_2__mkIdBindFor___closed__1);
l___private_Lean_Elab_Do_2__mkIdBindFor___closed__2 = _init_l___private_Lean_Elab_Do_2__mkIdBindFor___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Do_2__mkIdBindFor___closed__2);
l___private_Lean_Elab_Do_2__mkIdBindFor___closed__3 = _init_l___private_Lean_Elab_Do_2__mkIdBindFor___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Do_2__mkIdBindFor___closed__3);
l___private_Lean_Elab_Do_2__mkIdBindFor___closed__4 = _init_l___private_Lean_Elab_Do_2__mkIdBindFor___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Do_2__mkIdBindFor___closed__4);
l___private_Lean_Elab_Do_3__extractBind___closed__1 = _init_l___private_Lean_Elab_Do_3__extractBind___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Do_3__extractBind___closed__1);
l___private_Lean_Elab_Do_3__extractBind___closed__2 = _init_l___private_Lean_Elab_Do_3__extractBind___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Do_3__extractBind___closed__2);
l___private_Lean_Elab_Do_3__extractBind___closed__3 = _init_l___private_Lean_Elab_Do_3__extractBind___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Do_3__extractBind___closed__3);
l_Lean_Elab_Term_Do_Code_inhabited___closed__1 = _init_l_Lean_Elab_Term_Do_Code_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_Code_inhabited___closed__1);
l_Lean_Elab_Term_Do_Code_inhabited = _init_l_Lean_Elab_Term_Do_Code_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_Do_Code_inhabited);
l_Lean_Elab_Term_Do_Alt_inhabited___closed__1 = _init_l_Lean_Elab_Term_Do_Alt_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_Alt_inhabited___closed__1);
l_Lean_Elab_Term_Do_Alt_inhabited = _init_l_Lean_Elab_Term_Do_Alt_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_Do_Alt_inhabited);
l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___closed__1 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___closed__1();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___closed__1);
l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___closed__2 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___closed__2();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___closed__2);
l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___closed__3 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___closed__3();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_Do_toMessageDataAux___main___spec__3___closed__3);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__1 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__1);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__2 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__2);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__3 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__3);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__4 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__4);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__5 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__5);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__6 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__6);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__7 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__7);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__8 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__8);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__9 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__9);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__10 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__10);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__11 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__11);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__12 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__12);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__13 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__13);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__14 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__14);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__15 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__15);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__16 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__16();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__16);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__17 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__17();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__17);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__18 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__18();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__18);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__19 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__19();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__19);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__20 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__20();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__20);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__21 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__21();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__21);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__22 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__22();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__22);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__23 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__23();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__23);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__24 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__24();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__24);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__25 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__25();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__25);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__26 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__26();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__26);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__27 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__27();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__27);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__28 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__28();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__28);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__29 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__29();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__29);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__30 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__30();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__30);
l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__31 = _init_l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__31();
lean_mark_persistent(l_Lean_Elab_Term_Do_toMessageDataAux___main___closed__31);
l_Lean_Elab_Term_Do_mkFreshJP___closed__1 = _init_l_Lean_Elab_Term_Do_mkFreshJP___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_mkFreshJP___closed__1);
l_Lean_Elab_Term_Do_mkFreshJP___closed__2 = _init_l_Lean_Elab_Term_Do_mkFreshJP___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Do_mkFreshJP___closed__2);
l_Lean_Elab_Term_Do_mkFreshJP___closed__3 = _init_l_Lean_Elab_Term_Do_mkFreshJP___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Do_mkFreshJP___closed__3);
l_Lean_Elab_Term_Do_mkFreshJP___closed__4 = _init_l_Lean_Elab_Term_Do_mkFreshJP___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Do_mkFreshJP___closed__4);
l_Lean_Elab_Term_Do_mkJmp___closed__1 = _init_l_Lean_Elab_Term_Do_mkJmp___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_mkJmp___closed__1);
l_Lean_Elab_Term_Do_mkJmp___closed__2 = _init_l_Lean_Elab_Term_Do_mkJmp___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Do_mkJmp___closed__2);
l_Lean_Elab_Term_Do_mkJmp___closed__3 = _init_l_Lean_Elab_Term_Do_mkJmp___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Do_mkJmp___closed__3);
l_Lean_Elab_Term_Do_mkJmp___closed__4 = _init_l_Lean_Elab_Term_Do_mkJmp___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Do_mkJmp___closed__4);
l_Lean_Elab_Term_Do_mkJmp___closed__5 = _init_l_Lean_Elab_Term_Do_mkJmp___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Do_mkJmp___closed__5);
l_Lean_Elab_Term_Do_mkUnless___closed__1 = _init_l_Lean_Elab_Term_Do_mkUnless___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_mkUnless___closed__1);
l_Lean_Elab_Term_Do_mkUnless___closed__2 = _init_l_Lean_Elab_Term_Do_mkUnless___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Do_mkUnless___closed__2);
l_Lean_Elab_Term_Do_mkUnless___closed__3 = _init_l_Lean_Elab_Term_Do_mkUnless___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Do_mkUnless___closed__3);
l_Lean_Elab_Term_Do_mkUnless___closed__4 = _init_l_Lean_Elab_Term_Do_mkUnless___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Do_mkUnless___closed__4);
l_Lean_Elab_Term_Do_mkUnless___closed__5 = _init_l_Lean_Elab_Term_Do_mkUnless___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Do_mkUnless___closed__5);
l_Lean_Elab_Term_Do_mkUnless___closed__6 = _init_l_Lean_Elab_Term_Do_mkUnless___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_Do_mkUnless___closed__6);
l_Lean_Elab_Term_Do_mkUnless___closed__7 = _init_l_Lean_Elab_Term_Do_mkUnless___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_Do_mkUnless___closed__7);
l_Lean_Elab_Term_Do_mkUnless___closed__8 = _init_l_Lean_Elab_Term_Do_mkUnless___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_Do_mkUnless___closed__8);
l_Lean_Elab_Term_Do_getLetDeclVars___closed__1 = _init_l_Lean_Elab_Term_Do_getLetDeclVars___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_getLetDeclVars___closed__1);
l_Lean_Elab_Term_Do_getLetDeclVars___closed__2 = _init_l_Lean_Elab_Term_Do_getLetDeclVars___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Do_getLetDeclVars___closed__2);
l_Lean_Elab_Term_Do_getLetDeclVars___closed__3 = _init_l_Lean_Elab_Term_Do_getLetDeclVars___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Do_getLetDeclVars___closed__3);
l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__1 = _init_l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__1);
l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2 = _init_l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__2);
l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__3 = _init_l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__3);
l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__4 = _init_l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__4);
l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__5 = _init_l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__5);
l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__6 = _init_l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__6);
l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__7 = _init_l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_Do_getDoLetArrowVars___closed__7);
l_Lean_Elab_Term_Do_getDoReassignVars___closed__1 = _init_l_Lean_Elab_Term_Do_getDoReassignVars___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_getDoReassignVars___closed__1);
l_Lean_Elab_Term_Do_getDoReassignVars___closed__2 = _init_l_Lean_Elab_Term_Do_getDoReassignVars___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Do_getDoReassignVars___closed__2);
l_Lean_Elab_Term_Do_getDoReassignVars___closed__3 = _init_l_Lean_Elab_Term_Do_getDoReassignVars___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Do_getDoReassignVars___closed__3);
l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1___closed__1 = _init_l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1___closed__1);
l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1___closed__2 = _init_l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_9__expandDoIf___spec__1___closed__2);
l___private_Lean_Elab_Do_9__expandDoIf___closed__1 = _init_l___private_Lean_Elab_Do_9__expandDoIf___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Do_9__expandDoIf___closed__1);
l___private_Lean_Elab_Do_9__expandDoIf___closed__2 = _init_l___private_Lean_Elab_Do_9__expandDoIf___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Do_9__expandDoIf___closed__2);
l___private_Lean_Elab_Do_9__expandDoIf___closed__3 = _init_l___private_Lean_Elab_Do_9__expandDoIf___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Do_9__expandDoIf___closed__3);
l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_12__mkTuple___spec__1___closed__1 = _init_l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_12__mkTuple___spec__1___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Lean_Elab_Do_12__mkTuple___spec__1___closed__1);
l___private_Lean_Elab_Do_13__mkForInYield___closed__1 = _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Do_13__mkForInYield___closed__1);
l___private_Lean_Elab_Do_13__mkForInYield___closed__2 = _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Do_13__mkForInYield___closed__2);
l___private_Lean_Elab_Do_13__mkForInYield___closed__3 = _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Do_13__mkForInYield___closed__3);
l___private_Lean_Elab_Do_13__mkForInYield___closed__4 = _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Do_13__mkForInYield___closed__4);
l___private_Lean_Elab_Do_13__mkForInYield___closed__5 = _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Do_13__mkForInYield___closed__5);
l___private_Lean_Elab_Do_13__mkForInYield___closed__6 = _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Do_13__mkForInYield___closed__6);
l___private_Lean_Elab_Do_13__mkForInYield___closed__7 = _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Do_13__mkForInYield___closed__7);
l___private_Lean_Elab_Do_13__mkForInYield___closed__8 = _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Do_13__mkForInYield___closed__8);
l___private_Lean_Elab_Do_13__mkForInYield___closed__9 = _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Do_13__mkForInYield___closed__9);
l___private_Lean_Elab_Do_13__mkForInYield___closed__10 = _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Do_13__mkForInYield___closed__10);
l___private_Lean_Elab_Do_13__mkForInYield___closed__11 = _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Do_13__mkForInYield___closed__11);
l___private_Lean_Elab_Do_13__mkForInYield___closed__12 = _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Do_13__mkForInYield___closed__12);
l___private_Lean_Elab_Do_13__mkForInYield___closed__13 = _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Do_13__mkForInYield___closed__13);
l___private_Lean_Elab_Do_13__mkForInYield___closed__14 = _init_l___private_Lean_Elab_Do_13__mkForInYield___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Do_13__mkForInYield___closed__14);
l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__1 = _init_l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__1);
l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__2 = _init_l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__2);
l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__3 = _init_l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__3);
l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__4 = _init_l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__4);
l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__5 = _init_l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__5);
l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__6 = _init_l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__6);
l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__7 = _init_l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__7);
l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__8 = _init_l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_returnToTermCore___closed__8);
l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__1 = _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__1);
l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__2 = _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__2);
l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__3 = _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__3);
l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__4 = _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__4);
l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__5 = _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__5);
l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__6 = _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__6);
l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__7 = _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__7);
l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__8 = _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__8);
l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__9 = _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__9);
l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__10 = _init_l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_continueToTermCore___closed__10);
l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__1 = _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__1);
l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__2 = _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__2);
l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__3 = _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__3);
l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__4 = _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__4);
l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__5 = _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__5);
l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__6 = _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__6);
l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__7 = _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__7);
l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__8 = _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__8);
l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__9 = _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__9);
l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__10 = _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__10);
l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__11 = _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__11);
l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__12 = _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__12);
l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__13 = _init_l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_breakToTermCore___closed__13);
l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__1 = _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__1);
l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__2 = _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__2);
l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__3 = _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__3);
l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__4 = _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__4);
l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__5 = _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__5);
l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__6 = _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__6);
l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__7 = _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__7);
l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__8 = _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__8);
l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__9 = _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__9);
l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__10 = _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__10);
l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__11 = _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__11);
l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__12 = _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__12);
l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__13 = _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__13);
l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__14 = _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__14);
l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__15 = _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__15);
l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__16 = _init_l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__16();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_actionToTermCore___closed__16);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__1 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__1);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__2 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__2);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__3 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__3);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__4 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__4);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__5 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__5);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__6 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__6);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__7 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__7);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__8 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__8);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__9 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__9);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__10 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__10);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__11 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__11);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__12 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__12);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__13 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__13);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__14 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__14);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__15 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__15);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__16 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__16();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__16);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__17 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__17();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__17);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__18 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__18();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__18);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__19 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__19();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__19);
l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__20 = _init_l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__20();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_declToTermCore___closed__20);
l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__1 = _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__1);
l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__2 = _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__2);
l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__3 = _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__3);
l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__4 = _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__4);
l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__5 = _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__5);
l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__6 = _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__6);
l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__7 = _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__7);
l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__8 = _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__8);
l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__9 = _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__9);
l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__10 = _init_l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_reassignToTermCore___closed__10);
l_Lean_Elab_Term_Do_ToTerm_mkIte___closed__1 = _init_l_Lean_Elab_Term_Do_ToTerm_mkIte___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_mkIte___closed__1);
l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___closed__1 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___closed__1);
l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___closed__2 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___closed__2);
l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___closed__3 = _init_l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Term_Do_ToTerm_mkJoinPointCore___spec__1___closed__3);
l_Lean_Elab_Term_Do_ToTerm_toTerm___main___closed__1 = _init_l_Lean_Elab_Term_Do_ToTerm_toTerm___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToTerm_toTerm___main___closed__1);
l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__1 = _init_l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__1();
lean_mark_persistent(l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__1);
l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__2 = _init_l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__2();
lean_mark_persistent(l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__2);
l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__3 = _init_l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__3();
lean_mark_persistent(l_Array_forMAux___main___at_Lean_Elab_Term_Do_ToCodeBlock_checkReassignable___spec__2___closed__3);
l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___closed__1 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___closed__1);
l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___closed__2 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___closed__2);
l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___closed__3 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_ensureInsideFor___closed__3);
l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___closed__1 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___closed__1);
l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___closed__2 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___closed__2);
l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___closed__3 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_ensureEOS___closed__3);
l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__1 = _init_l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__1);
l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2 = _init_l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__2);
l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__3 = _init_l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__3);
l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4 = _init_l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Do_15__expandLiftMethodAux___main___closed__4);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__1 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__1);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__2 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__2);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__3 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__3);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__4 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__4);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__5 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__5);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__6 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__6);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__7 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__7);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__8 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__8);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__9 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__9);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__10 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__10);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__11 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__11);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__12 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__12);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__13 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__13);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__14 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__14);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__15 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__15);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__16 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__16();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__16);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__17 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__17();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__17);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__18 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__18();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__18);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__19 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__19();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__19);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__20 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__20();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__20);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__21 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__21();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__21);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__22 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__22();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__22);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__23 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__23();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__23);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__24 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__24();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__24);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__25 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__25();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__25);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__26 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__26();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__26);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__27 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__27();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__27);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__28 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__28();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__28);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__29 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__29();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__29);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__30 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__30();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__30);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__31 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__31();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__31);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__32 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__32();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__32);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__33 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__33();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__33);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__34 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__34();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__34);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__35 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__35();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__35);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__36 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__36();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__36);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__37 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__37();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__37);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__38 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__38();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__38);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__39 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__39();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__39);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__40 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__40();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__40);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__41 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__41();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__41);
l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__42 = _init_l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__42();
lean_mark_persistent(l_Lean_Elab_Term_Do_ToCodeBlock_doSeqToCode___main___closed__42);
l___private_Lean_Elab_Do_16__mkMonadAlias___closed__1 = _init_l___private_Lean_Elab_Do_16__mkMonadAlias___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Do_16__mkMonadAlias___closed__1);
l___private_Lean_Elab_Do_16__mkMonadAlias___closed__2 = _init_l___private_Lean_Elab_Do_16__mkMonadAlias___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Do_16__mkMonadAlias___closed__2);
l___private_Lean_Elab_Do_16__mkMonadAlias___closed__3 = _init_l___private_Lean_Elab_Do_16__mkMonadAlias___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Do_16__mkMonadAlias___closed__3);
l___private_Lean_Elab_Do_16__mkMonadAlias___closed__4 = _init_l___private_Lean_Elab_Do_16__mkMonadAlias___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Do_16__mkMonadAlias___closed__4);
l___private_Lean_Elab_Do_16__mkMonadAlias___closed__5 = _init_l___private_Lean_Elab_Do_16__mkMonadAlias___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Do_16__mkMonadAlias___closed__5);
l___private_Lean_Elab_Do_16__mkMonadAlias___closed__6 = _init_l___private_Lean_Elab_Do_16__mkMonadAlias___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Do_16__mkMonadAlias___closed__6);
l_Lean_Elab_Term_Do_elabDo___closed__1 = _init_l_Lean_Elab_Term_Do_elabDo___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Do_elabDo___closed__1);
l___regBuiltin_Lean_Elab_Term_Do_elabDo___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Do_elabDo___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Do_elabDo___closed__1);
res = l___regBuiltin_Lean_Elab_Term_Do_elabDo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Do_17__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
