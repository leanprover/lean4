// Lean compiler output
// Module: Lean.Meta.Tactic.Induction
// Imports: Init Lean.Meta.RecursorInfo Lean.Meta.SynthInstance Lean.Meta.Tactic.Util Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Clear Lean.Meta.Tactic.FVarSubst
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
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity(lean_object*);
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_7__regTraceClasses(lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__7;
lean_object* l_Lean_Meta_introN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__4;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___boxed(lean_object**);
lean_object* l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstanceImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__2;
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_Lean_Level_Inhabited;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___lambda__1___boxed(lean_object**);
lean_object* l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_induction___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_assignExprMVar___at_Lean_Meta_getLevel___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___boxed(lean_object**);
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__2;
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_12__forallTelescopeReducingAuxAux___main___rarg___closed__2;
lean_object* l_List_elem___main___at_Lean_Meta_induction___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__6;
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_induction___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2;
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_inferType___at_Lean_mkAuxDefinitionFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__5;
extern lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7;
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___boxed(lean_object**);
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnf___at___private_Lean_Meta_Basic_14__isClassExpensive_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__3;
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8;
lean_object* l_Lean_whnfUntil___at_Lean_Meta_induction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__8;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
lean_object* l_Lean_MetavarContext_localDeclDependsOn(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__4;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_whnfForall___at___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__9;
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InductionSubgoal_inhabited___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__7;
lean_object* l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
uint8_t l_List_elem___main___at_Lean_Meta_induction___spec__5(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__6;
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__7;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__3;
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___boxed(lean_object**);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
lean_object* l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__5;
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1;
lean_object* l_Lean_whnfUntil___at_Lean_Meta_induction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
extern lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1;
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6;
uint8_t l_Lean_Level_isZero(lean_object*);
extern lean_object* l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_synthInstance_x3f___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3;
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_8__isClassQuick_x3f___main___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3;
lean_object* l_Lean_getLocalDecl___at_Lean_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InductionSubgoal_inhabited;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_8__isClassQuick_x3f___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_getMCtx___at_Lean_getMVarDecl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_12__forallTelescopeReducingAuxAux___main___rarg___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstanceImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
return x_11;
}
case 10:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_1 = x_12;
goto _start;
}
default: 
{
lean_object* x_14; 
x_14 = lean_box(0);
x_2 = x_14;
goto block_7;
}
}
block_7:
{
uint8_t x_3; 
lean_dec(x_2);
x_3 = l_Lean_Expr_isHeadBetaTarget(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Expr_headBeta(x_1);
x_1 = x_5;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_1);
return x_2;
}
}
lean_object* l_Lean_whnfForall___at___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_whnf___at___private_Lean_Meta_Basic_14__isClassExpensive_x3f___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Expr_isForall(x_9);
if (x_10 == 0)
{
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
else
{
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = l_Lean_Expr_isForall(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("induction");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed recursor");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to generate type class instance parameter");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_inferType___at_Lean_mkAuxDefinitionFor___spec__1(x_4, x_5, x_6, x_7, x_8, x_9);
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
x_16 = l_Lean_whnfForall___at___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___spec__1(x_14, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 7)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Meta_synthInstanceImp(x_19, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_mkApp(x_4, x_21);
x_3 = x_12;
x_4 = x_23;
x_9 = x_22;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_4);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_27 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8;
x_28 = lean_box(0);
x_29 = l_Lean_Meta_throwTacticEx___rarg(x_26, x_1, x_27, x_28, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_17);
lean_dec(x_4);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_dec(x_16);
x_35 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_36 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_37 = lean_box(0);
x_38 = l_Lean_Meta_throwTacticEx___rarg(x_35, x_1, x_36, x_37, x_5, x_6, x_7, x_8, x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
else
{
uint8_t x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_13);
if (x_43 == 0)
{
return x_13;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_13, 0);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_3, 1);
x_48 = lean_ctor_get(x_11, 0);
x_49 = lean_array_get_size(x_2);
x_50 = lean_nat_dec_lt(x_48, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_4);
x_51 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_52 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_53 = lean_box(0);
x_54 = l_Lean_Meta_throwTacticEx___rarg(x_51, x_1, x_52, x_53, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_array_fget(x_2, x_48);
x_56 = l_Lean_mkApp(x_4, x_55);
x_3 = x_47;
x_4 = x_56;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* _init_l_Lean_Meta_InductionSubgoal_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_InductionSubgoal_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_InductionSubgoal_inhabited___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_whnfForall___at___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 7)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_expr_instantiate1(x_13, x_3);
lean_dec(x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_ctor_get(x_10, 2);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_expr_instantiate1(x_16, x_3);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_21 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_22 = lean_box(0);
x_23 = l_Lean_Meta_throwTacticEx___rarg(x_20, x_1, x_21, x_22, x_4, x_5, x_6, x_7, x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
return x_9;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_9);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
x_12 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
x_13 = lean_nat_add(x_3, x_10);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = l_Lean_Name_inhabited;
x_16 = lean_array_get(x_15, x_1, x_12);
x_17 = lean_nat_sub(x_12, x_3);
lean_dec(x_12);
x_18 = lean_nat_sub(x_17, x_10);
lean_dec(x_17);
x_19 = lean_array_get(x_15, x_4, x_18);
lean_dec(x_18);
x_20 = l_Lean_mkFVar(x_19);
x_21 = l_Lean_Meta_FVarSubst_insert(x_7, x_16, x_20);
x_6 = x_11;
x_7 = x_21;
goto _start;
}
else
{
lean_dec(x_12);
x_6 = x_11;
goto _start;
}
}
else
{
lean_dec(x_6);
return x_7;
}
}
}
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
x_12 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
x_13 = lean_nat_add(x_3, x_10);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = l_Lean_Name_inhabited;
x_16 = lean_array_get(x_15, x_1, x_12);
x_17 = lean_nat_sub(x_12, x_3);
lean_dec(x_12);
x_18 = lean_nat_sub(x_17, x_10);
lean_dec(x_17);
x_19 = lean_array_get(x_15, x_4, x_18);
lean_dec(x_18);
x_20 = l_Lean_mkFVar(x_19);
x_21 = l_Lean_Meta_FVarSubst_insert(x_7, x_16, x_20);
x_6 = x_11;
x_7 = x_21;
goto _start;
}
else
{
lean_dec(x_12);
x_6 = x_11;
goto _start;
}
}
else
{
lean_dec(x_6);
return x_7;
}
}
}
lean_object* l_Lean_synthInstance_x3f___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_synthInstanceImp_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_array_fget(x_3, x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
x_20 = l_Lean_mkApp(x_18, x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_21 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_19, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set(x_5, 1, x_22);
lean_ctor_set(x_5, 0, x_20);
x_4 = x_16;
x_10 = x_23;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_20);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
lean_inc(x_14);
x_31 = l_Lean_mkApp(x_29, x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_32 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_30, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_14);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_33);
x_4 = x_16;
x_5 = x_35;
x_10 = x_34;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_39 = x_32;
} else {
 lean_dec_ref(x_32);
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
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_21 = l_Lean_whnfForall___at___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___spec__1(x_13, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Expr_isForall(x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
if (x_14 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_12);
x_25 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_26 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_27 = lean_box(0);
x_28 = l_Lean_Meta_throwTacticEx___rarg(x_25, x_1, x_26, x_27, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
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
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_assignExprMVar___at_Lean_Meta_getLevel___spec__3(x_1, x_12, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_15);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_15);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_3, 3);
x_39 = lean_nat_dec_lt(x_10, x_38);
if (x_39 == 0)
{
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
if (x_14 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_15);
lean_dec(x_12);
x_40 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_41 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_42 = lean_box(0);
x_43 = l_Lean_Meta_throwTacticEx___rarg(x_40, x_1, x_41, x_42, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_assignExprMVar___at_Lean_Meta_getLevel___spec__3(x_1, x_12, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
lean_ctor_set(x_48, 0, x_15);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_15);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = l_Lean_Meta_RecursorInfo_firstIndexPos(x_3);
x_54 = lean_nat_dec_eq(x_10, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_inc(x_1);
x_55 = l_Lean_Meta_getMVarTag(x_1, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_194; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_194 = lean_nat_dec_le(x_8, x_11);
if (x_194 == 0)
{
x_58 = x_57;
goto block_193;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_dec(x_56);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_195 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_196 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_197 = lean_box(0);
x_198 = l_Lean_Meta_throwTacticEx___rarg(x_195, x_1, x_196, x_197, x_16, x_17, x_18, x_19, x_57);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_199 = !lean_is_exclusive(x_198);
if (x_199 == 0)
{
return x_198;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_198, 0);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_198);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
block_193:
{
if (lean_obj_tag(x_22) == 7)
{
lean_object* x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; lean_object* x_63; uint8_t x_143; uint8_t x_144; 
x_59 = lean_ctor_get(x_22, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_22, 1);
lean_inc(x_60);
x_61 = lean_ctor_get_uint64(x_22, sizeof(void*)*3);
x_62 = l_Lean_Expr_headBeta(x_60);
x_143 = (uint8_t)((x_61 << 24) >> 61);
x_144 = l_Lean_BinderInfo_isInstImplicit(x_143);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_box(0);
x_63 = x_145;
goto block_142;
}
else
{
uint8_t x_146; 
x_146 = l_Array_isEmpty___rarg(x_2);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_box(0);
x_63 = x_147;
goto block_142;
}
else
{
lean_object* x_148; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_62);
x_148 = l_Lean_Meta_synthInstanceImp_x3f(x_62, x_16, x_17, x_18, x_19, x_58);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = l_Lean_Name_append___main(x_56, x_59);
lean_dec(x_56);
x_152 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_62, x_151, x_16, x_17, x_18, x_19, x_150);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
lean_inc(x_153);
x_155 = l_Lean_mkApp(x_12, x_153);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_156 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_22, x_153, x_16, x_17, x_18, x_19, x_154);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_unsigned_to_nat(1u);
x_160 = lean_nat_add(x_10, x_159);
lean_dec(x_10);
x_161 = lean_nat_add(x_11, x_159);
lean_dec(x_11);
x_162 = l_Lean_Expr_mvarId_x21(x_153);
lean_dec(x_153);
x_163 = lean_box(0);
x_164 = l_Array_empty___closed__1;
x_165 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_165, 2, x_163);
x_166 = lean_array_push(x_15, x_165);
x_10 = x_160;
x_11 = x_161;
x_12 = x_155;
x_13 = x_157;
x_15 = x_166;
x_20 = x_158;
goto _start;
}
else
{
uint8_t x_168; 
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_168 = !lean_is_exclusive(x_156);
if (x_168 == 0)
{
return x_156;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_156, 0);
x_170 = lean_ctor_get(x_156, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_156);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_56);
x_172 = lean_ctor_get(x_148, 1);
lean_inc(x_172);
lean_dec(x_148);
x_173 = lean_ctor_get(x_149, 0);
lean_inc(x_173);
lean_dec(x_149);
lean_inc(x_173);
x_174 = l_Lean_mkApp(x_12, x_173);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_175 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_22, x_173, x_16, x_17, x_18, x_19, x_172);
lean_dec(x_173);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_unsigned_to_nat(1u);
x_179 = lean_nat_add(x_10, x_178);
lean_dec(x_10);
x_180 = lean_nat_add(x_11, x_178);
lean_dec(x_11);
x_10 = x_179;
x_11 = x_180;
x_12 = x_174;
x_13 = x_176;
x_20 = x_177;
goto _start;
}
else
{
uint8_t x_182; 
lean_dec(x_174);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_175);
if (x_182 == 0)
{
return x_175;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_175, 0);
x_184 = lean_ctor_get(x_175, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_175);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_148);
if (x_186 == 0)
{
return x_148;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_148, 0);
x_188 = lean_ctor_get(x_148, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_148);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
}
block_142:
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_63);
lean_inc(x_62);
x_64 = l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_62);
x_65 = lean_nat_dec_lt(x_64, x_6);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_66 = lean_nat_sub(x_64, x_6);
lean_dec(x_64);
x_67 = lean_array_get_size(x_4);
x_68 = lean_array_get_size(x_7);
x_69 = lean_nat_sub(x_67, x_68);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_sub(x_69, x_70);
lean_dec(x_69);
x_124 = lean_array_get_size(x_2);
x_125 = lean_nat_dec_lt(x_11, x_124);
lean_dec(x_124);
x_126 = l_Lean_Name_append___main(x_56, x_59);
lean_dec(x_56);
x_127 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_62, x_126, x_16, x_17, x_18, x_19, x_58);
if (x_125 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_box(0);
x_72 = x_130;
x_73 = x_128;
x_74 = x_129;
goto block_123;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_127, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_dec(x_127);
x_133 = lean_array_fget(x_2, x_11);
x_72 = x_133;
x_73 = x_131;
x_74 = x_132;
goto block_123;
}
block_123:
{
lean_object* x_75; lean_object* x_76; 
lean_inc(x_73);
x_75 = l_Lean_mkApp(x_12, x_73);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_76 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_22, x_73, x_16, x_17, x_18, x_19, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Expr_mvarId_x21(x_73);
lean_dec(x_73);
x_80 = l_Lean_Expr_fvarId_x21(x_5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_81 = l_Lean_Meta_tryClear(x_79, x_80, x_16, x_17, x_18, x_19, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_85 = l_Lean_Meta_introN(x_82, x_66, x_72, x_84, x_16, x_17, x_18, x_19, x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_box(0);
x_91 = 0;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_92 = l_Lean_Meta_introN(x_89, x_71, x_90, x_91, x_16, x_17, x_18, x_19, x_87);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
lean_inc(x_9);
lean_inc(x_67);
x_97 = l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(x_4, x_7, x_68, x_95, x_67, x_67, x_9);
lean_dec(x_67);
lean_dec(x_95);
lean_dec(x_68);
x_98 = x_88;
x_99 = lean_unsigned_to_nat(0u);
x_100 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_99, x_98);
x_101 = x_100;
x_102 = lean_nat_add(x_10, x_70);
lean_dec(x_10);
x_103 = lean_nat_add(x_11, x_70);
lean_dec(x_11);
x_104 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_104, 0, x_96);
lean_ctor_set(x_104, 1, x_101);
lean_ctor_set(x_104, 2, x_97);
x_105 = lean_array_push(x_15, x_104);
x_10 = x_102;
x_11 = x_103;
x_12 = x_75;
x_13 = x_77;
x_15 = x_105;
x_20 = x_94;
goto _start;
}
else
{
uint8_t x_107; 
lean_dec(x_88);
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_92);
if (x_107 == 0)
{
return x_92;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_92, 0);
x_109 = lean_ctor_get(x_92, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_92);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_85);
if (x_111 == 0)
{
return x_85;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_85, 0);
x_113 = lean_ctor_get(x_85, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_85);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_81);
if (x_115 == 0)
{
return x_81;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_81, 0);
x_117 = lean_ctor_get(x_81, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_81);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_76);
if (x_119 == 0)
{
return x_76;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_76, 0);
x_121 = lean_ctor_get(x_76, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_76);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_134 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_135 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_136 = lean_box(0);
x_137 = l_Lean_Meta_throwTacticEx___rarg(x_134, x_1, x_135, x_136, x_16, x_17, x_18, x_19, x_58);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
return x_137;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_137);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_56);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_190 = l___private_Lean_Meta_Basic_8__isClassQuick_x3f___main___closed__1;
x_191 = l_unreachable_x21___rarg(x_190);
x_192 = lean_apply_5(x_191, x_16, x_17, x_18, x_19, x_58);
return x_192;
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_203 = !lean_is_exclusive(x_55);
if (x_203 == 0)
{
return x_55;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_55, 0);
x_205 = lean_ctor_get(x_55, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_55);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_12);
lean_ctor_set(x_207, 1, x_22);
x_208 = lean_unsigned_to_nat(0u);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_209 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4(x_1, x_7, x_7, x_208, x_207, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
lean_dec(x_210);
lean_inc(x_5);
x_214 = l_Lean_mkApp(x_212, x_5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_215 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_213, x_5, x_16, x_17, x_18, x_19, x_211);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_unsigned_to_nat(1u);
x_219 = lean_nat_add(x_10, x_218);
lean_dec(x_10);
x_220 = lean_array_get_size(x_7);
x_221 = lean_nat_add(x_219, x_220);
lean_dec(x_220);
lean_dec(x_219);
x_222 = 1;
x_10 = x_221;
x_12 = x_214;
x_13 = x_216;
x_14 = x_222;
x_20 = x_217;
goto _start;
}
else
{
uint8_t x_224; 
lean_dec(x_214);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_224 = !lean_is_exclusive(x_215);
if (x_224 == 0)
{
return x_215;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_215, 0);
x_226 = lean_ctor_get(x_215, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_215);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_228 = !lean_is_exclusive(x_209);
if (x_228 == 0)
{
return x_209;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_209, 0);
x_230 = lean_ctor_get(x_209, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_209);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
}
}
}
else
{
uint8_t x_232; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_232 = !lean_is_exclusive(x_21);
if (x_232 == 0)
{
return x_21;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_21, 0);
x_234 = lean_ctor_get(x_21, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_21);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
}
}
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_14);
lean_dec(x_14);
x_22 = l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_21, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
x_21 = l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_21;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_14);
lean_dec(x_14);
x_22 = l___private_Lean_Meta_Tactic_Induction_4__finalizeAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_21, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_1);
x_14 = l_Lean_Meta_getMVarType(x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_inferType___at_Lean_mkAuxDefinitionFor___spec__1(x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_3, 7);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_List_lengthAux___main___rarg(x_21, x_22);
x_24 = lean_ctor_get(x_3, 5);
x_25 = l_List_lengthAux___main___rarg(x_24, x_22);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_25, x_26);
lean_dec(x_25);
x_28 = 0;
x_29 = l_Array_empty___closed__1;
x_30 = l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(x_1, x_2, x_3, x_4, x_5, x_17, x_6, x_23, x_7, x_27, x_22, x_8, x_19, x_28, x_29, x_9, x_10, x_11, x_12, x_20);
lean_dec(x_23);
lean_dec(x_17);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected major premise type ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = l_Lean_indentExpr(x_8);
x_10 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3;
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_13 = lean_box(0);
x_14 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_11, x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_induction___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1;
x_9 = l_unreachable_x21___rarg(x_8);
x_10 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = l_Lean_getLocalDecl___at_Lean_getFVarLocalDecl___spec__1(x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_LocalDecl_value_x3f(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_17; 
lean_free_object(x_12);
lean_dec(x_2);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_2 = x_17;
x_7 = x_15;
goto _start;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = l_Lean_LocalDecl_value_x3f(x_19);
lean_dec(x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_2);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_2 = x_23;
x_7 = x_20;
goto _start;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
case 2:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_8__isClassQuick_x3f___main___spec__1(x_29, x_3, x_4, x_5, x_6, x_7);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
lean_ctor_set(x_30, 0, x_2);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
x_2 = x_37;
x_7 = x_36;
goto _start;
}
}
case 4:
{
lean_object* x_39; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_39 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = l_Lean_Expr_isAppOf(x_41, x_1);
if (x_43 == 0)
{
lean_object* x_44; 
lean_free_object(x_39);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_44 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_41, x_3, x_4, x_5, x_6, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_44, 0);
lean_dec(x_47);
lean_ctor_set(x_44, 0, x_41);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_41);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
lean_dec(x_45);
x_2 = x_51;
x_7 = x_50;
goto _start;
}
}
else
{
uint8_t x_53; 
lean_dec(x_41);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_44);
if (x_53 == 0)
{
return x_44;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_44, 0);
x_55 = lean_ctor_get(x_44, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_44);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_39;
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_39, 0);
x_58 = lean_ctor_get(x_39, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_39);
x_59 = l_Lean_Expr_isAppOf(x_57, x_1);
if (x_59 == 0)
{
lean_object* x_60; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_57);
x_60 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_57, x_3, x_4, x_5, x_6, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_dec(x_60);
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
lean_dec(x_61);
x_2 = x_66;
x_7 = x_65;
goto _start;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_57);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = lean_ctor_get(x_60, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_60, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_70 = x_60;
} else {
 lean_dec_ref(x_60);
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
else
{
lean_object* x_72; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_57);
lean_ctor_set(x_72, 1, x_58);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_39);
if (x_73 == 0)
{
return x_39;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_39, 0);
x_75 = lean_ctor_get(x_39, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_39);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
case 5:
{
lean_object* x_77; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_77 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
x_81 = l_Lean_Expr_isAppOf(x_79, x_1);
if (x_81 == 0)
{
lean_object* x_82; 
lean_free_object(x_77);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_79);
x_82 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_79, x_3, x_4, x_5, x_6, x_80);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_82, 0);
lean_dec(x_85);
lean_ctor_set(x_82, 0, x_79);
return x_82;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_79);
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_dec(x_82);
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
lean_dec(x_83);
x_2 = x_89;
x_7 = x_88;
goto _start;
}
}
else
{
uint8_t x_91; 
lean_dec(x_79);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_91 = !lean_is_exclusive(x_82);
if (x_91 == 0)
{
return x_82;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_82, 0);
x_93 = lean_ctor_get(x_82, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_82);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_77;
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_77, 0);
x_96 = lean_ctor_get(x_77, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_77);
x_97 = l_Lean_Expr_isAppOf(x_95, x_1);
if (x_97 == 0)
{
lean_object* x_98; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_95);
x_98 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_95, x_3, x_4, x_5, x_6, x_96);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_95);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_95);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_dec(x_98);
x_104 = lean_ctor_get(x_99, 0);
lean_inc(x_104);
lean_dec(x_99);
x_2 = x_104;
x_7 = x_103;
goto _start;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_106 = lean_ctor_get(x_98, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_98, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_108 = x_98;
} else {
 lean_dec_ref(x_98);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
lean_object* x_110; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_95);
lean_ctor_set(x_110, 1, x_96);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_111 = !lean_is_exclusive(x_77);
if (x_111 == 0)
{
return x_77;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_77, 0);
x_113 = lean_ctor_get(x_77, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_77);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
case 8:
{
lean_object* x_115; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_115 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = l_Lean_Expr_isAppOf(x_117, x_1);
if (x_119 == 0)
{
lean_object* x_120; 
lean_free_object(x_115);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_117);
x_120 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_117, x_3, x_4, x_5, x_6, x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_122 = !lean_is_exclusive(x_120);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_120, 0);
lean_dec(x_123);
lean_ctor_set(x_120, 0, x_117);
return x_120;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
lean_dec(x_120);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_117);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_117);
x_126 = lean_ctor_get(x_120, 1);
lean_inc(x_126);
lean_dec(x_120);
x_127 = lean_ctor_get(x_121, 0);
lean_inc(x_127);
lean_dec(x_121);
x_2 = x_127;
x_7 = x_126;
goto _start;
}
}
else
{
uint8_t x_129; 
lean_dec(x_117);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_129 = !lean_is_exclusive(x_120);
if (x_129 == 0)
{
return x_120;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_120, 0);
x_131 = lean_ctor_get(x_120, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_120);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_115;
}
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_115, 0);
x_134 = lean_ctor_get(x_115, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_115);
x_135 = l_Lean_Expr_isAppOf(x_133, x_1);
if (x_135 == 0)
{
lean_object* x_136; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_133);
x_136 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_133, x_3, x_4, x_5, x_6, x_134);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_139 = x_136;
} else {
 lean_dec_ref(x_136);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_133);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_133);
x_141 = lean_ctor_get(x_136, 1);
lean_inc(x_141);
lean_dec(x_136);
x_142 = lean_ctor_get(x_137, 0);
lean_inc(x_142);
lean_dec(x_137);
x_2 = x_142;
x_7 = x_141;
goto _start;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_144 = lean_ctor_get(x_136, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_136, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_146 = x_136;
} else {
 lean_dec_ref(x_136);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_133);
lean_ctor_set(x_148, 1, x_134);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_149 = !lean_is_exclusive(x_115);
if (x_149 == 0)
{
return x_115;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_115, 0);
x_151 = lean_ctor_get(x_115, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_115);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
case 10:
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_2, 1);
lean_inc(x_153);
lean_dec(x_2);
x_2 = x_153;
goto _start;
}
case 11:
{
lean_object* x_155; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_155 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_155) == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = lean_ctor_get(x_155, 1);
x_159 = l_Lean_Expr_isAppOf(x_157, x_1);
if (x_159 == 0)
{
lean_object* x_160; 
lean_free_object(x_155);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_157);
x_160 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_157, x_3, x_4, x_5, x_6, x_158);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
uint8_t x_162; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_162 = !lean_is_exclusive(x_160);
if (x_162 == 0)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_160, 0);
lean_dec(x_163);
lean_ctor_set(x_160, 0, x_157);
return x_160;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
lean_dec(x_160);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_157);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_157);
x_166 = lean_ctor_get(x_160, 1);
lean_inc(x_166);
lean_dec(x_160);
x_167 = lean_ctor_get(x_161, 0);
lean_inc(x_167);
lean_dec(x_161);
x_2 = x_167;
x_7 = x_166;
goto _start;
}
}
else
{
uint8_t x_169; 
lean_dec(x_157);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_169 = !lean_is_exclusive(x_160);
if (x_169 == 0)
{
return x_160;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_160, 0);
x_171 = lean_ctor_get(x_160, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_160);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_155;
}
}
else
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_173 = lean_ctor_get(x_155, 0);
x_174 = lean_ctor_get(x_155, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_155);
x_175 = l_Lean_Expr_isAppOf(x_173, x_1);
if (x_175 == 0)
{
lean_object* x_176; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_173);
x_176 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_173, x_3, x_4, x_5, x_6, x_174);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_179 = x_176;
} else {
 lean_dec_ref(x_176);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_173);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_173);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_dec(x_176);
x_182 = lean_ctor_get(x_177, 0);
lean_inc(x_182);
lean_dec(x_177);
x_2 = x_182;
x_7 = x_181;
goto _start;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_173);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_184 = lean_ctor_get(x_176, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_176, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_186 = x_176;
} else {
 lean_dec_ref(x_176);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
else
{
lean_object* x_188; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_173);
lean_ctor_set(x_188, 1, x_174);
return x_188;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_189 = !lean_is_exclusive(x_155);
if (x_189 == 0)
{
return x_155;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_155, 0);
x_191 = lean_ctor_get(x_155, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_155);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
case 12:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_2);
x_193 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1;
x_194 = l_unreachable_x21___rarg(x_193);
x_195 = lean_apply_5(x_194, x_3, x_4, x_5, x_6, x_7);
return x_195;
}
default: 
{
lean_object* x_196; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_2);
lean_ctor_set(x_196, 1, x_7);
return x_196;
}
}
}
}
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_whnfUntil___at_Lean_Meta_induction___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_induction___spec__3(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Expr_isAppOf(x_10, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
x_12 = lean_box(0);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = l_Lean_Expr_isAppOf(x_14, x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* _init_l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise type is ill-formed");
return x_1;
}
}
lean_object* _init_l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_5, 1);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_array_get_size(x_4);
x_19 = lean_nat_dec_le(x_18, x_17);
lean_dec(x_18);
if (x_19 == 0)
{
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_3);
x_22 = l_Lean_indentExpr(x_21);
x_23 = l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3;
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_box(0);
x_26 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_24, x_25, x_6, x_7, x_8, x_9, x_10);
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
}
}
uint8_t l_List_elem___main___at_Lean_Meta_induction___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_nat_dec_eq(x_1, x_4);
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
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is an index in major premise, but it depends on index occurring at position #");
return x_1;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is an index in major premise, but it occurs in previous arguments");
return x_1;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is an index in major premise, but it occurs more than once");
return x_1;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_10, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_60; uint8_t x_80; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_10, x_18);
lean_dec(x_10);
x_20 = lean_nat_sub(x_9, x_19);
x_21 = lean_nat_sub(x_20, x_18);
lean_dec(x_20);
x_22 = l_Lean_Expr_Inhabited;
x_23 = lean_array_get(x_22, x_4, x_21);
x_80 = lean_nat_dec_eq(x_21, x_7);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = lean_expr_eqv(x_23, x_8);
if (x_81 == 0)
{
x_60 = x_15;
goto block_79;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_5);
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_8);
x_83 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_84 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9;
x_86 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_87, 0, x_3);
x_88 = l_Lean_indentExpr(x_87);
x_89 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_box(0);
x_91 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_89, x_90, x_11, x_12, x_13, x_14, x_15);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
return x_91;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_91);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
x_60 = x_15;
goto block_79;
}
block_59:
{
uint8_t x_25; 
x_25 = lean_nat_dec_lt(x_7, x_21);
if (x_25 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
x_10 = x_19;
x_15 = x_24;
goto _start;
}
else
{
uint8_t x_27; 
x_27 = l_List_elem___main___at_Lean_Meta_induction___spec__5(x_21, x_6);
if (x_27 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
x_10 = x_19;
x_15 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
x_29 = l_Lean_Expr_isFVar(x_23);
if (x_29 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
x_10 = x_19;
x_15 = x_24;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_Expr_fvarId_x21(x_8);
x_32 = l_Lean_getLocalDecl___at_Lean_getFVarLocalDecl___spec__1(x_31, x_11, x_12, x_13, x_14, x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Expr_fvarId_x21(x_23);
lean_dec(x_23);
lean_inc(x_5);
x_36 = l_Lean_MetavarContext_localDeclDependsOn(x_5, x_33, x_35);
lean_dec(x_35);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_dec(x_21);
x_10 = x_19;
x_15 = x_34;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_3);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_8);
x_40 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3;
x_43 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_nat_add(x_21, x_18);
lean_dec(x_21);
x_45 = l_Nat_repr(x_44);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_box(0);
x_50 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_48, x_49, x_11, x_12, x_13, x_14, x_34);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_32);
if (x_55 == 0)
{
return x_32;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_32, 0);
x_57 = lean_ctor_get(x_32, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_32);
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
block_79:
{
uint8_t x_61; 
x_61 = lean_nat_dec_lt(x_21, x_7);
if (x_61 == 0)
{
x_24 = x_60;
goto block_59;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = l_Lean_Expr_fvarId_x21(x_8);
lean_inc(x_23);
lean_inc(x_5);
x_63 = l_Lean_MetavarContext_exprDependsOn(x_5, x_23, x_62);
lean_dec(x_62);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
x_24 = x_60;
goto block_59;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_5);
x_65 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_65, 0, x_8);
x_66 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_67 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6;
x_69 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_3);
x_71 = l_Lean_indentExpr(x_70);
x_72 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_box(0);
x_74 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_72, x_73, x_11, x_12, x_13, x_14, x_60);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
return x_74;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_74);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_15);
return x_97;
}
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise type index ");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" is not variable ");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_8);
x_15 = lean_nat_dec_lt(x_7, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = x_8;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_55; 
x_18 = lean_array_fget(x_8, x_7);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_fset(x_8, x_7, x_19);
x_21 = x_18;
x_22 = lean_array_get_size(x_4);
x_55 = lean_nat_dec_le(x_22, x_21);
if (x_55 == 0)
{
x_23 = x_13;
goto block_54;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_3);
x_57 = l_Lean_indentExpr(x_56);
x_58 = l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3;
x_59 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_box(0);
x_61 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_59, x_60, x_9, x_10, x_11, x_12, x_13);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
return x_61;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_61);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
block_54:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_39; 
x_24 = l_Lean_Expr_Inhabited;
x_25 = lean_array_get(x_24, x_4, x_21);
x_39 = l_Lean_Expr_isFVar(x_25);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_25);
x_41 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__3;
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_44 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_3);
x_46 = l_Lean_indentExpr(x_45);
x_47 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_box(0);
x_49 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_47, x_48, x_9, x_10, x_11, x_12, x_23);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
return x_49;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
x_26 = x_23;
goto block_38;
}
block_38:
{
lean_object* x_27; 
lean_inc(x_22);
lean_inc(x_25);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_21, x_25, x_22, x_22, x_9, x_10, x_11, x_12, x_26);
lean_dec(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_7, x_29);
x_31 = x_25;
x_32 = lean_array_fset(x_20, x_7, x_31);
lean_dec(x_7);
x_7 = x_30;
x_8 = x_32;
x_13 = x_28;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
x_10 = l_Lean_Name_inhabited;
x_11 = lean_array_get(x_10, x_2, x_4);
x_12 = l_Lean_mkFVar(x_11);
x_13 = l_Lean_Meta_FVarSubst_insert(x_5, x_9, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_4 = x_15;
x_5 = x_13;
goto _start;
}
}
}
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_dec(x_17);
lean_inc(x_3);
x_18 = lean_array_push(x_16, x_3);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_5, 1, x_20);
lean_ctor_set(x_5, 0, x_18);
x_6 = x_15;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
lean_dec(x_5);
lean_inc(x_3);
x_24 = lean_array_push(x_23, x_3);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_5 = x_27;
x_6 = x_22;
goto _start;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_6, 1);
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_array_get_size(x_4);
x_35 = lean_nat_dec_le(x_34, x_33);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = l_Lean_Level_Inhabited;
x_37 = lean_array_get(x_36, x_4, x_33);
x_38 = lean_array_push(x_31, x_37);
lean_ctor_set(x_5, 0, x_38);
x_6 = x_30;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_free_object(x_5);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_3);
x_40 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_41 = lean_box(0);
x_42 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_40, x_41, x_7, x_8, x_9, x_10, x_11);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_47 = lean_ctor_get(x_6, 1);
x_48 = lean_ctor_get(x_5, 0);
x_49 = lean_ctor_get(x_5, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_5);
x_50 = lean_ctor_get(x_13, 0);
x_51 = lean_array_get_size(x_4);
x_52 = lean_nat_dec_le(x_51, x_50);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = l_Lean_Level_Inhabited;
x_54 = lean_array_get(x_53, x_4, x_50);
x_55 = lean_array_push(x_48, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_49);
x_5 = x_56;
x_6 = x_47;
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_3);
x_58 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_59 = lean_box(0);
x_60 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_58, x_59, x_7, x_8, x_9, x_10, x_11);
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
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise is not of the form (C ...)");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("recursor '");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' can only eliminate into Prop");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
switch (lean_obj_tag(x_14)) {
case 4:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_List_redLength___main___rarg(x_22);
x_24 = lean_mk_empty_array_with_capacity(x_23);
lean_dec(x_23);
x_25 = l_List_toArrayAux___main___rarg(x_22, x_24);
x_26 = lean_ctor_get(x_4, 2);
x_27 = l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
lean_inc(x_13);
lean_inc(x_8);
lean_inc(x_3);
x_28 = l_List_foldlM___main___at_Lean_Meta_induction___spec__9(x_3, x_8, x_13, x_25, x_27, x_26, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = l_Lean_Level_isZero(x_13);
lean_dec(x_13);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_33);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_35 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_35, 0, x_1);
x_36 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__6;
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__9;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_box(0);
x_41 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_39, x_40, x_17, x_18, x_19, x_20, x_32);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_3);
x_46 = l_Array_toList___rarg(x_33);
lean_dec(x_33);
x_47 = l_Lean_mkConst(x_1, x_46);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_8);
x_48 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_8, x_15, x_5, x_47, x_17, x_18, x_19, x_20, x_32);
lean_dec(x_15);
if (lean_obj_tag(x_48) == 0)
{
if (x_6 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_10);
x_51 = l_Lean_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_10, x_12, x_17, x_18, x_19, x_20, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_mkApp(x_49, x_52);
x_55 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_54, x_17, x_18, x_19, x_20, x_53);
lean_dec(x_10);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_49);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_56 = !lean_is_exclusive(x_51);
if (x_56 == 0)
{
return x_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_51, 0);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_51);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_48, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
lean_dec(x_48);
x_62 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_11);
x_63 = lean_array_push(x_62, x_11);
x_64 = l_Lean_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_63, x_12, x_17, x_18, x_19, x_20, x_61);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_10);
x_67 = l_Lean_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_10, x_65, x_17, x_18, x_19, x_20, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_mkApp(x_60, x_68);
x_71 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_70, x_17, x_18, x_19, x_20, x_69);
lean_dec(x_10);
return x_71;
}
else
{
uint8_t x_72; 
lean_dec(x_60);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_72 = !lean_is_exclusive(x_67);
if (x_72 == 0)
{
return x_67;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_67, 0);
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_67);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_60);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_76 = !lean_is_exclusive(x_64);
if (x_76 == 0)
{
return x_64;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_64, 0);
x_78 = lean_ctor_get(x_64, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_64);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_80 = !lean_is_exclusive(x_48);
if (x_80 == 0)
{
return x_48;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_48, 0);
x_82 = lean_ctor_get(x_48, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_48);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_13);
lean_dec(x_3);
x_84 = lean_ctor_get(x_28, 1);
lean_inc(x_84);
lean_dec(x_28);
x_85 = lean_ctor_get(x_29, 0);
lean_inc(x_85);
lean_dec(x_29);
x_86 = l_Array_toList___rarg(x_85);
lean_dec(x_85);
x_87 = l_Lean_mkConst(x_1, x_86);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_8);
x_88 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_8, x_15, x_5, x_87, x_17, x_18, x_19, x_20, x_84);
lean_dec(x_15);
if (lean_obj_tag(x_88) == 0)
{
if (x_6 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
lean_inc(x_10);
x_91 = l_Lean_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_10, x_12, x_17, x_18, x_19, x_20, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_mkApp(x_89, x_92);
x_95 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_94, x_17, x_18, x_19, x_20, x_93);
lean_dec(x_10);
return x_95;
}
else
{
uint8_t x_96; 
lean_dec(x_89);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_96 = !lean_is_exclusive(x_91);
if (x_96 == 0)
{
return x_91;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_91, 0);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_91);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_88, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_88, 1);
lean_inc(x_101);
lean_dec(x_88);
x_102 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_11);
x_103 = lean_array_push(x_102, x_11);
x_104 = l_Lean_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_103, x_12, x_17, x_18, x_19, x_20, x_101);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_10);
x_107 = l_Lean_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_10, x_105, x_17, x_18, x_19, x_20, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_mkApp(x_100, x_108);
x_111 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_110, x_17, x_18, x_19, x_20, x_109);
lean_dec(x_10);
return x_111;
}
else
{
uint8_t x_112; 
lean_dec(x_100);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_112 = !lean_is_exclusive(x_107);
if (x_112 == 0)
{
return x_107;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_107, 0);
x_114 = lean_ctor_get(x_107, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_107);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_100);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_116 = !lean_is_exclusive(x_104);
if (x_116 == 0)
{
return x_104;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_104, 0);
x_118 = lean_ctor_get(x_104, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_104);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_120 = !lean_is_exclusive(x_88);
if (x_120 == 0)
{
return x_88;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_88, 0);
x_122 = lean_ctor_get(x_88, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_88);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_28);
if (x_124 == 0)
{
return x_28;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_28, 0);
x_126 = lean_ctor_get(x_28, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_28);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
case 5:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_14, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_14, 1);
lean_inc(x_129);
lean_dec(x_14);
x_130 = lean_array_set(x_15, x_16, x_129);
x_131 = lean_unsigned_to_nat(1u);
x_132 = lean_nat_sub(x_16, x_131);
lean_dec(x_16);
x_14 = x_128;
x_15 = x_130;
x_16 = x_132;
goto _start;
}
default: 
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_134 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__3;
x_135 = lean_box(0);
x_136 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_134, x_135, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
return x_136;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_20 = l_Lean_Meta_getLevel(x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_getLocalDecl___at_Lean_getFVarLocalDecl___spec__1(x_1, x_15, x_16, x_17, x_18, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_LocalDecl_type(x_24);
lean_dec(x_24);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_26);
x_27 = l_Lean_whnfUntil___at_Lean_Meta_induction___spec__1(x_26, x_2, x_15, x_16, x_17, x_18, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(x_3, x_26, x_15, x_16, x_17, x_18, x_29);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_26);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Expr_getAppNumArgsAux___main(x_32, x_33);
x_35 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_34);
x_36 = lean_mk_array(x_34, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_34, x_37);
lean_dec(x_34);
x_39 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_3, x_11, x_12, x_13, x_14, x_21, x_32, x_36, x_38, x_15, x_16, x_17, x_18, x_31);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_27);
if (x_40 == 0)
{
return x_27;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_27, 0);
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_27);
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
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
return x_23;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_23, 0);
x_46 = lean_ctor_get(x_23, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_23);
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
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_20);
if (x_48 == 0)
{
return x_20;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_20, 0);
x_50 = lean_ctor_get(x_20, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_20);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after revert&intro");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__4;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not support dependent elimination, but conclusion depends on major premise");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_11);
x_19 = lean_ctor_get(x_8, 5);
lean_inc(x_19);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_20 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_7, x_10, x_12, x_19, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_getMCtx___at_Lean_getMVarDecl___spec__1___rarg(x_15, x_16, x_17, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_8, 6);
lean_inc(x_25);
x_26 = l_List_redLength___main___rarg(x_25);
x_27 = lean_mk_empty_array_with_capacity(x_26);
lean_dec(x_26);
lean_inc(x_25);
x_28 = l_List_toArrayAux___main___rarg(x_25, x_27);
x_29 = x_28;
x_30 = lean_unsigned_to_nat(0u);
lean_inc(x_23);
lean_inc(x_7);
lean_inc(x_1);
x_31 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_7);
lean_closure_set(x_31, 2, x_10);
lean_closure_set(x_31, 3, x_12);
lean_closure_set(x_31, 4, x_23);
lean_closure_set(x_31, 5, x_25);
lean_closure_set(x_31, 6, x_30);
lean_closure_set(x_31, 7, x_29);
x_32 = x_31;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_33 = lean_apply_5(x_32, x_14, x_15, x_16, x_17, x_24);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_1);
x_36 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_39 == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = l_Lean_MetavarContext_exprDependsOn(x_23, x_37, x_2);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
x_40 = x_38;
goto block_123;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_34);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_126 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_126, 0, x_3);
x_127 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__6;
x_128 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_129 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8;
x_130 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_box(0);
x_132 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_130, x_131, x_14, x_15, x_16, x_17, x_38);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
return x_132;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_132, 0);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_132);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_23);
x_40 = x_38;
goto block_123;
}
block_123:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
lean_inc(x_34);
x_41 = x_34;
x_42 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_30, x_41);
x_43 = x_42;
x_44 = lean_array_push(x_43, x_2);
x_45 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_46 = l_Lean_Meta_revert(x_1, x_44, x_45, x_14, x_15, x_16, x_17, x_40);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_array_get_size(x_34);
x_52 = lean_box(0);
x_53 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_54 = l_Lean_Meta_introN(x_50, x_51, x_52, x_53, x_14, x_15, x_16, x_17, x_48);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_59 = l_Lean_Meta_intro1(x_58, x_53, x_14, x_15, x_16, x_17, x_56);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_86; lean_object* x_87; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
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
x_64 = lean_box(0);
x_65 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_34, x_57, x_34, x_30, x_64);
lean_dec(x_34);
x_95 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_96 = lean_ctor_get(x_95, 2);
lean_inc(x_96);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_97 = lean_apply_5(x_96, x_14, x_15, x_16, x_17, x_61);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_98, sizeof(void*)*1);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_86 = x_53;
x_87 = x_100;
goto block_94;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
lean_dec(x_97);
x_102 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_103 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_102, x_14, x_15, x_16, x_17, x_101);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_unbox(x_104);
lean_dec(x_104);
x_86 = x_106;
x_87 = x_105;
goto block_94;
}
}
else
{
uint8_t x_107; 
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_57);
lean_dec(x_49);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_107 = !lean_is_exclusive(x_97);
if (x_107 == 0)
{
return x_97;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_97, 0);
x_109 = lean_ctor_get(x_97, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_97);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
block_85:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = x_57;
x_68 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_30, x_67);
x_69 = x_68;
lean_inc(x_62);
x_70 = l_Lean_mkFVar(x_62);
lean_inc(x_63);
x_71 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_71, 0, x_63);
x_72 = lean_box(x_39);
lean_inc(x_63);
x_73 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___lambda__1___boxed), 19, 13);
lean_closure_set(x_73, 0, x_62);
lean_closure_set(x_73, 1, x_9);
lean_closure_set(x_73, 2, x_63);
lean_closure_set(x_73, 3, x_3);
lean_closure_set(x_73, 4, x_4);
lean_closure_set(x_73, 5, x_7);
lean_closure_set(x_73, 6, x_8);
lean_closure_set(x_73, 7, x_19);
lean_closure_set(x_73, 8, x_72);
lean_closure_set(x_73, 9, x_49);
lean_closure_set(x_73, 10, x_65);
lean_closure_set(x_73, 11, x_69);
lean_closure_set(x_73, 12, x_70);
x_74 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_74, 0, x_71);
lean_closure_set(x_74, 1, x_73);
x_75 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_63, x_14, x_15, x_16, x_17, x_66);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 4);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(x_78, x_79, x_74, x_14, x_15, x_16, x_17, x_77);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_74);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_81 = !lean_is_exclusive(x_75);
if (x_81 == 0)
{
return x_75;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_75, 0);
x_83 = lean_ctor_get(x_75, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_75);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
block_94:
{
if (x_86 == 0)
{
x_66 = x_87;
goto block_85;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_inc(x_63);
x_88 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_88, 0, x_63);
x_89 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5;
x_90 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_92 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_91, x_90, x_14, x_15, x_16, x_17, x_87);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_66 = x_93;
goto block_85;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_57);
lean_dec(x_49);
lean_dec(x_34);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_111 = !lean_is_exclusive(x_59);
if (x_111 == 0)
{
return x_59;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_59, 0);
x_113 = lean_ctor_get(x_59, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_59);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_49);
lean_dec(x_34);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_115 = !lean_is_exclusive(x_54);
if (x_115 == 0)
{
return x_54;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_54, 0);
x_117 = lean_ctor_get(x_54, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_54);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_34);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_119 = !lean_is_exclusive(x_46);
if (x_119 == 0)
{
return x_46;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_46, 0);
x_121 = lean_ctor_get(x_46, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_46);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_34);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_36);
if (x_137 == 0)
{
return x_36;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_36, 0);
x_139 = lean_ctor_get(x_36, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_36);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_33);
if (x_141 == 0)
{
return x_33;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_33, 0);
x_143 = lean_ctor_get(x_33, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_33);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = !lean_is_exclusive(x_20);
if (x_145 == 0)
{
return x_20;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_20, 0);
x_147 = lean_ctor_get(x_20, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_20);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
case 1:
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_13);
lean_dec(x_11);
x_149 = lean_ctor_get(x_8, 5);
lean_inc(x_149);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_150 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_7, x_10, x_12, x_149, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_152 = l_Lean_getMCtx___at_Lean_getMVarDecl___spec__1___rarg(x_15, x_16, x_17, x_151);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_ctor_get(x_8, 6);
lean_inc(x_155);
x_156 = l_List_redLength___main___rarg(x_155);
x_157 = lean_mk_empty_array_with_capacity(x_156);
lean_dec(x_156);
lean_inc(x_155);
x_158 = l_List_toArrayAux___main___rarg(x_155, x_157);
x_159 = x_158;
x_160 = lean_unsigned_to_nat(0u);
lean_inc(x_153);
lean_inc(x_7);
lean_inc(x_1);
x_161 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_161, 0, x_1);
lean_closure_set(x_161, 1, x_7);
lean_closure_set(x_161, 2, x_10);
lean_closure_set(x_161, 3, x_12);
lean_closure_set(x_161, 4, x_153);
lean_closure_set(x_161, 5, x_155);
lean_closure_set(x_161, 6, x_160);
lean_closure_set(x_161, 7, x_159);
x_162 = x_161;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_163 = lean_apply_5(x_162, x_14, x_15, x_16, x_17, x_154);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
lean_inc(x_1);
x_166 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_165);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_169 == 0)
{
lean_object* x_254; uint8_t x_255; 
x_254 = l_Lean_MetavarContext_exprDependsOn(x_153, x_167, x_2);
x_255 = lean_unbox(x_254);
lean_dec(x_254);
if (x_255 == 0)
{
x_170 = x_168;
goto block_253;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
lean_dec(x_164);
lean_dec(x_149);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_256 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_256, 0, x_3);
x_257 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__6;
x_258 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_256);
x_259 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8;
x_260 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
x_261 = lean_box(0);
x_262 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_260, x_261, x_14, x_15, x_16, x_17, x_168);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_263 = !lean_is_exclusive(x_262);
if (x_263 == 0)
{
return x_262;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_262, 0);
x_265 = lean_ctor_get(x_262, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_262);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
else
{
lean_dec(x_167);
lean_dec(x_153);
x_170 = x_168;
goto block_253;
}
block_253:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; 
lean_inc(x_164);
x_171 = x_164;
x_172 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_160, x_171);
x_173 = x_172;
x_174 = lean_array_push(x_173, x_2);
x_175 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_176 = l_Lean_Meta_revert(x_1, x_174, x_175, x_14, x_15, x_16, x_17, x_170);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_ctor_get(x_177, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
lean_dec(x_177);
x_181 = lean_array_get_size(x_164);
x_182 = lean_box(0);
x_183 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_184 = l_Lean_Meta_introN(x_180, x_181, x_182, x_183, x_14, x_15, x_16, x_17, x_178);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_ctor_get(x_185, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
lean_dec(x_185);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_189 = l_Lean_Meta_intro1(x_188, x_183, x_14, x_15, x_16, x_17, x_186);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_216; lean_object* x_217; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
lean_dec(x_190);
x_194 = lean_box(0);
x_195 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_164, x_187, x_164, x_160, x_194);
lean_dec(x_164);
x_225 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_226 = lean_ctor_get(x_225, 2);
lean_inc(x_226);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_227 = lean_apply_5(x_226, x_14, x_15, x_16, x_17, x_191);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; uint8_t x_229; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get_uint8(x_228, sizeof(void*)*1);
lean_dec(x_228);
if (x_229 == 0)
{
lean_object* x_230; 
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
lean_dec(x_227);
x_216 = x_183;
x_217 = x_230;
goto block_224;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_231 = lean_ctor_get(x_227, 1);
lean_inc(x_231);
lean_dec(x_227);
x_232 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_233 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_232, x_14, x_15, x_16, x_17, x_231);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_unbox(x_234);
lean_dec(x_234);
x_216 = x_236;
x_217 = x_235;
goto block_224;
}
}
else
{
uint8_t x_237; 
lean_dec(x_195);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_187);
lean_dec(x_179);
lean_dec(x_149);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_237 = !lean_is_exclusive(x_227);
if (x_237 == 0)
{
return x_227;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_227, 0);
x_239 = lean_ctor_get(x_227, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_227);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
block_215:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_197 = x_187;
x_198 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_160, x_197);
x_199 = x_198;
lean_inc(x_192);
x_200 = l_Lean_mkFVar(x_192);
lean_inc(x_193);
x_201 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_201, 0, x_193);
x_202 = lean_box(x_169);
lean_inc(x_193);
x_203 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___lambda__1___boxed), 19, 13);
lean_closure_set(x_203, 0, x_192);
lean_closure_set(x_203, 1, x_9);
lean_closure_set(x_203, 2, x_193);
lean_closure_set(x_203, 3, x_3);
lean_closure_set(x_203, 4, x_4);
lean_closure_set(x_203, 5, x_7);
lean_closure_set(x_203, 6, x_8);
lean_closure_set(x_203, 7, x_149);
lean_closure_set(x_203, 8, x_202);
lean_closure_set(x_203, 9, x_179);
lean_closure_set(x_203, 10, x_195);
lean_closure_set(x_203, 11, x_199);
lean_closure_set(x_203, 12, x_200);
x_204 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_204, 0, x_201);
lean_closure_set(x_204, 1, x_203);
x_205 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_193, x_14, x_15, x_16, x_17, x_196);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_206, 4);
lean_inc(x_209);
lean_dec(x_206);
x_210 = l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(x_208, x_209, x_204, x_14, x_15, x_16, x_17, x_207);
return x_210;
}
else
{
uint8_t x_211; 
lean_dec(x_204);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_211 = !lean_is_exclusive(x_205);
if (x_211 == 0)
{
return x_205;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_205, 0);
x_213 = lean_ctor_get(x_205, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_205);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
block_224:
{
if (x_216 == 0)
{
x_196 = x_217;
goto block_215;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_inc(x_193);
x_218 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_218, 0, x_193);
x_219 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5;
x_220 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_218);
x_221 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_222 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_221, x_220, x_14, x_15, x_16, x_17, x_217);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_196 = x_223;
goto block_215;
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_187);
lean_dec(x_179);
lean_dec(x_164);
lean_dec(x_149);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_241 = !lean_is_exclusive(x_189);
if (x_241 == 0)
{
return x_189;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_189, 0);
x_243 = lean_ctor_get(x_189, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_189);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
else
{
uint8_t x_245; 
lean_dec(x_179);
lean_dec(x_164);
lean_dec(x_149);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_245 = !lean_is_exclusive(x_184);
if (x_245 == 0)
{
return x_184;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_184, 0);
x_247 = lean_ctor_get(x_184, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_184);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
else
{
uint8_t x_249; 
lean_dec(x_164);
lean_dec(x_149);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_249 = !lean_is_exclusive(x_176);
if (x_249 == 0)
{
return x_176;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_176, 0);
x_251 = lean_ctor_get(x_176, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_176);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_164);
lean_dec(x_153);
lean_dec(x_149);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_267 = !lean_is_exclusive(x_166);
if (x_267 == 0)
{
return x_166;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_166, 0);
x_269 = lean_ctor_get(x_166, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_166);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
else
{
uint8_t x_271; 
lean_dec(x_153);
lean_dec(x_149);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_271 = !lean_is_exclusive(x_163);
if (x_271 == 0)
{
return x_163;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_163, 0);
x_273 = lean_ctor_get(x_163, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_163);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
else
{
uint8_t x_275; 
lean_dec(x_149);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_275 = !lean_is_exclusive(x_150);
if (x_275 == 0)
{
return x_150;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_150, 0);
x_277 = lean_ctor_get(x_150, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_150);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
}
case 2:
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_13);
lean_dec(x_11);
x_279 = lean_ctor_get(x_8, 5);
lean_inc(x_279);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_280 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_7, x_10, x_12, x_279, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
lean_dec(x_280);
x_282 = l_Lean_getMCtx___at_Lean_getMVarDecl___spec__1___rarg(x_15, x_16, x_17, x_281);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = lean_ctor_get(x_8, 6);
lean_inc(x_285);
x_286 = l_List_redLength___main___rarg(x_285);
x_287 = lean_mk_empty_array_with_capacity(x_286);
lean_dec(x_286);
lean_inc(x_285);
x_288 = l_List_toArrayAux___main___rarg(x_285, x_287);
x_289 = x_288;
x_290 = lean_unsigned_to_nat(0u);
lean_inc(x_283);
lean_inc(x_7);
lean_inc(x_1);
x_291 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_291, 0, x_1);
lean_closure_set(x_291, 1, x_7);
lean_closure_set(x_291, 2, x_10);
lean_closure_set(x_291, 3, x_12);
lean_closure_set(x_291, 4, x_283);
lean_closure_set(x_291, 5, x_285);
lean_closure_set(x_291, 6, x_290);
lean_closure_set(x_291, 7, x_289);
x_292 = x_291;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_293 = lean_apply_5(x_292, x_14, x_15, x_16, x_17, x_284);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
lean_inc(x_1);
x_296 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_295);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; uint8_t x_299; lean_object* x_300; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_299 == 0)
{
lean_object* x_384; uint8_t x_385; 
x_384 = l_Lean_MetavarContext_exprDependsOn(x_283, x_297, x_2);
x_385 = lean_unbox(x_384);
lean_dec(x_384);
if (x_385 == 0)
{
x_300 = x_298;
goto block_383;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; 
lean_dec(x_294);
lean_dec(x_279);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_386 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_386, 0, x_3);
x_387 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__6;
x_388 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_386);
x_389 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8;
x_390 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_390, 0, x_388);
lean_ctor_set(x_390, 1, x_389);
x_391 = lean_box(0);
x_392 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_390, x_391, x_14, x_15, x_16, x_17, x_298);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_393 = !lean_is_exclusive(x_392);
if (x_393 == 0)
{
return x_392;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_392, 0);
x_395 = lean_ctor_get(x_392, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_392);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
}
else
{
lean_dec(x_297);
lean_dec(x_283);
x_300 = x_298;
goto block_383;
}
block_383:
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; 
lean_inc(x_294);
x_301 = x_294;
x_302 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_290, x_301);
x_303 = x_302;
x_304 = lean_array_push(x_303, x_2);
x_305 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_306 = l_Lean_Meta_revert(x_1, x_304, x_305, x_14, x_15, x_16, x_17, x_300);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
x_309 = lean_ctor_get(x_307, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_307, 1);
lean_inc(x_310);
lean_dec(x_307);
x_311 = lean_array_get_size(x_294);
x_312 = lean_box(0);
x_313 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_314 = l_Lean_Meta_introN(x_310, x_311, x_312, x_313, x_14, x_15, x_16, x_17, x_308);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_317 = lean_ctor_get(x_315, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_315, 1);
lean_inc(x_318);
lean_dec(x_315);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_319 = l_Lean_Meta_intro1(x_318, x_313, x_14, x_15, x_16, x_17, x_316);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_346; lean_object* x_347; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
lean_dec(x_319);
x_322 = lean_ctor_get(x_320, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_320, 1);
lean_inc(x_323);
lean_dec(x_320);
x_324 = lean_box(0);
x_325 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_294, x_317, x_294, x_290, x_324);
lean_dec(x_294);
x_355 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_356 = lean_ctor_get(x_355, 2);
lean_inc(x_356);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_357 = lean_apply_5(x_356, x_14, x_15, x_16, x_17, x_321);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; uint8_t x_359; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get_uint8(x_358, sizeof(void*)*1);
lean_dec(x_358);
if (x_359 == 0)
{
lean_object* x_360; 
x_360 = lean_ctor_get(x_357, 1);
lean_inc(x_360);
lean_dec(x_357);
x_346 = x_313;
x_347 = x_360;
goto block_354;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; 
x_361 = lean_ctor_get(x_357, 1);
lean_inc(x_361);
lean_dec(x_357);
x_362 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_363 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_362, x_14, x_15, x_16, x_17, x_361);
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
lean_dec(x_363);
x_366 = lean_unbox(x_364);
lean_dec(x_364);
x_346 = x_366;
x_347 = x_365;
goto block_354;
}
}
else
{
uint8_t x_367; 
lean_dec(x_325);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_317);
lean_dec(x_309);
lean_dec(x_279);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_367 = !lean_is_exclusive(x_357);
if (x_367 == 0)
{
return x_357;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_357, 0);
x_369 = lean_ctor_get(x_357, 1);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_357);
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
return x_370;
}
}
block_345:
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_327 = x_317;
x_328 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_290, x_327);
x_329 = x_328;
lean_inc(x_322);
x_330 = l_Lean_mkFVar(x_322);
lean_inc(x_323);
x_331 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_331, 0, x_323);
x_332 = lean_box(x_299);
lean_inc(x_323);
x_333 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___lambda__1___boxed), 19, 13);
lean_closure_set(x_333, 0, x_322);
lean_closure_set(x_333, 1, x_9);
lean_closure_set(x_333, 2, x_323);
lean_closure_set(x_333, 3, x_3);
lean_closure_set(x_333, 4, x_4);
lean_closure_set(x_333, 5, x_7);
lean_closure_set(x_333, 6, x_8);
lean_closure_set(x_333, 7, x_279);
lean_closure_set(x_333, 8, x_332);
lean_closure_set(x_333, 9, x_309);
lean_closure_set(x_333, 10, x_325);
lean_closure_set(x_333, 11, x_329);
lean_closure_set(x_333, 12, x_330);
x_334 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_334, 0, x_331);
lean_closure_set(x_334, 1, x_333);
x_335 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_323, x_14, x_15, x_16, x_17, x_326);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
x_339 = lean_ctor_get(x_336, 4);
lean_inc(x_339);
lean_dec(x_336);
x_340 = l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(x_338, x_339, x_334, x_14, x_15, x_16, x_17, x_337);
return x_340;
}
else
{
uint8_t x_341; 
lean_dec(x_334);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_341 = !lean_is_exclusive(x_335);
if (x_341 == 0)
{
return x_335;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_335, 0);
x_343 = lean_ctor_get(x_335, 1);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_335);
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
return x_344;
}
}
}
block_354:
{
if (x_346 == 0)
{
x_326 = x_347;
goto block_345;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_inc(x_323);
x_348 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_348, 0, x_323);
x_349 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5;
x_350 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_348);
x_351 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_352 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_351, x_350, x_14, x_15, x_16, x_17, x_347);
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
lean_dec(x_352);
x_326 = x_353;
goto block_345;
}
}
}
else
{
uint8_t x_371; 
lean_dec(x_317);
lean_dec(x_309);
lean_dec(x_294);
lean_dec(x_279);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_371 = !lean_is_exclusive(x_319);
if (x_371 == 0)
{
return x_319;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_319, 0);
x_373 = lean_ctor_get(x_319, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_319);
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
return x_374;
}
}
}
else
{
uint8_t x_375; 
lean_dec(x_309);
lean_dec(x_294);
lean_dec(x_279);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_375 = !lean_is_exclusive(x_314);
if (x_375 == 0)
{
return x_314;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_314, 0);
x_377 = lean_ctor_get(x_314, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_314);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
return x_378;
}
}
}
else
{
uint8_t x_379; 
lean_dec(x_294);
lean_dec(x_279);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_379 = !lean_is_exclusive(x_306);
if (x_379 == 0)
{
return x_306;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_306, 0);
x_381 = lean_ctor_get(x_306, 1);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_306);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
return x_382;
}
}
}
}
else
{
uint8_t x_397; 
lean_dec(x_294);
lean_dec(x_283);
lean_dec(x_279);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_397 = !lean_is_exclusive(x_296);
if (x_397 == 0)
{
return x_296;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_296, 0);
x_399 = lean_ctor_get(x_296, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_296);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
}
else
{
uint8_t x_401; 
lean_dec(x_283);
lean_dec(x_279);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_401 = !lean_is_exclusive(x_293);
if (x_401 == 0)
{
return x_293;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = lean_ctor_get(x_293, 0);
x_403 = lean_ctor_get(x_293, 1);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_293);
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_403);
return x_404;
}
}
}
else
{
uint8_t x_405; 
lean_dec(x_279);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_405 = !lean_is_exclusive(x_280);
if (x_405 == 0)
{
return x_280;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_280, 0);
x_407 = lean_ctor_get(x_280, 1);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_280);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
return x_408;
}
}
}
case 3:
{
lean_object* x_409; lean_object* x_410; 
lean_dec(x_13);
lean_dec(x_11);
x_409 = lean_ctor_get(x_8, 5);
lean_inc(x_409);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_410 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_7, x_10, x_12, x_409, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_411 = lean_ctor_get(x_410, 1);
lean_inc(x_411);
lean_dec(x_410);
x_412 = l_Lean_getMCtx___at_Lean_getMVarDecl___spec__1___rarg(x_15, x_16, x_17, x_411);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
lean_dec(x_412);
x_415 = lean_ctor_get(x_8, 6);
lean_inc(x_415);
x_416 = l_List_redLength___main___rarg(x_415);
x_417 = lean_mk_empty_array_with_capacity(x_416);
lean_dec(x_416);
lean_inc(x_415);
x_418 = l_List_toArrayAux___main___rarg(x_415, x_417);
x_419 = x_418;
x_420 = lean_unsigned_to_nat(0u);
lean_inc(x_413);
lean_inc(x_7);
lean_inc(x_1);
x_421 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_421, 0, x_1);
lean_closure_set(x_421, 1, x_7);
lean_closure_set(x_421, 2, x_10);
lean_closure_set(x_421, 3, x_12);
lean_closure_set(x_421, 4, x_413);
lean_closure_set(x_421, 5, x_415);
lean_closure_set(x_421, 6, x_420);
lean_closure_set(x_421, 7, x_419);
x_422 = x_421;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_423 = lean_apply_5(x_422, x_14, x_15, x_16, x_17, x_414);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
lean_dec(x_423);
lean_inc(x_1);
x_426 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_425);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
x_429 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_429 == 0)
{
lean_object* x_514; uint8_t x_515; 
x_514 = l_Lean_MetavarContext_exprDependsOn(x_413, x_427, x_2);
x_515 = lean_unbox(x_514);
lean_dec(x_514);
if (x_515 == 0)
{
x_430 = x_428;
goto block_513;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; uint8_t x_523; 
lean_dec(x_424);
lean_dec(x_409);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_516 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_516, 0, x_3);
x_517 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__6;
x_518 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_516);
x_519 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8;
x_520 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_520, 0, x_518);
lean_ctor_set(x_520, 1, x_519);
x_521 = lean_box(0);
x_522 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_520, x_521, x_14, x_15, x_16, x_17, x_428);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_523 = !lean_is_exclusive(x_522);
if (x_523 == 0)
{
return x_522;
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_524 = lean_ctor_get(x_522, 0);
x_525 = lean_ctor_get(x_522, 1);
lean_inc(x_525);
lean_inc(x_524);
lean_dec(x_522);
x_526 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_526, 0, x_524);
lean_ctor_set(x_526, 1, x_525);
return x_526;
}
}
}
else
{
lean_dec(x_427);
lean_dec(x_413);
x_430 = x_428;
goto block_513;
}
block_513:
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; lean_object* x_436; 
lean_inc(x_424);
x_431 = x_424;
x_432 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_420, x_431);
x_433 = x_432;
x_434 = lean_array_push(x_433, x_2);
x_435 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_436 = l_Lean_Meta_revert(x_1, x_434, x_435, x_14, x_15, x_16, x_17, x_430);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; lean_object* x_444; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec(x_436);
x_439 = lean_ctor_get(x_437, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_437, 1);
lean_inc(x_440);
lean_dec(x_437);
x_441 = lean_array_get_size(x_424);
x_442 = lean_box(0);
x_443 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_444 = l_Lean_Meta_introN(x_440, x_441, x_442, x_443, x_14, x_15, x_16, x_17, x_438);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_444, 1);
lean_inc(x_446);
lean_dec(x_444);
x_447 = lean_ctor_get(x_445, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_445, 1);
lean_inc(x_448);
lean_dec(x_445);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_449 = l_Lean_Meta_intro1(x_448, x_443, x_14, x_15, x_16, x_17, x_446);
if (lean_obj_tag(x_449) == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_476; lean_object* x_477; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_449, 1);
lean_inc(x_451);
lean_dec(x_449);
x_452 = lean_ctor_get(x_450, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_450, 1);
lean_inc(x_453);
lean_dec(x_450);
x_454 = lean_box(0);
x_455 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_424, x_447, x_424, x_420, x_454);
lean_dec(x_424);
x_485 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_486 = lean_ctor_get(x_485, 2);
lean_inc(x_486);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_487 = lean_apply_5(x_486, x_14, x_15, x_16, x_17, x_451);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_488; uint8_t x_489; 
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
x_489 = lean_ctor_get_uint8(x_488, sizeof(void*)*1);
lean_dec(x_488);
if (x_489 == 0)
{
lean_object* x_490; 
x_490 = lean_ctor_get(x_487, 1);
lean_inc(x_490);
lean_dec(x_487);
x_476 = x_443;
x_477 = x_490;
goto block_484;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; 
x_491 = lean_ctor_get(x_487, 1);
lean_inc(x_491);
lean_dec(x_487);
x_492 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_493 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_492, x_14, x_15, x_16, x_17, x_491);
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
lean_dec(x_493);
x_496 = lean_unbox(x_494);
lean_dec(x_494);
x_476 = x_496;
x_477 = x_495;
goto block_484;
}
}
else
{
uint8_t x_497; 
lean_dec(x_455);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_447);
lean_dec(x_439);
lean_dec(x_409);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_497 = !lean_is_exclusive(x_487);
if (x_497 == 0)
{
return x_487;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = lean_ctor_get(x_487, 0);
x_499 = lean_ctor_get(x_487, 1);
lean_inc(x_499);
lean_inc(x_498);
lean_dec(x_487);
x_500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_499);
return x_500;
}
}
block_475:
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_457 = x_447;
x_458 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_420, x_457);
x_459 = x_458;
lean_inc(x_452);
x_460 = l_Lean_mkFVar(x_452);
lean_inc(x_453);
x_461 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_461, 0, x_453);
x_462 = lean_box(x_429);
lean_inc(x_453);
x_463 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___lambda__1___boxed), 19, 13);
lean_closure_set(x_463, 0, x_452);
lean_closure_set(x_463, 1, x_9);
lean_closure_set(x_463, 2, x_453);
lean_closure_set(x_463, 3, x_3);
lean_closure_set(x_463, 4, x_4);
lean_closure_set(x_463, 5, x_7);
lean_closure_set(x_463, 6, x_8);
lean_closure_set(x_463, 7, x_409);
lean_closure_set(x_463, 8, x_462);
lean_closure_set(x_463, 9, x_439);
lean_closure_set(x_463, 10, x_455);
lean_closure_set(x_463, 11, x_459);
lean_closure_set(x_463, 12, x_460);
x_464 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_464, 0, x_461);
lean_closure_set(x_464, 1, x_463);
x_465 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_453, x_14, x_15, x_16, x_17, x_456);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
lean_dec(x_465);
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
x_469 = lean_ctor_get(x_466, 4);
lean_inc(x_469);
lean_dec(x_466);
x_470 = l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(x_468, x_469, x_464, x_14, x_15, x_16, x_17, x_467);
return x_470;
}
else
{
uint8_t x_471; 
lean_dec(x_464);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_471 = !lean_is_exclusive(x_465);
if (x_471 == 0)
{
return x_465;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_465, 0);
x_473 = lean_ctor_get(x_465, 1);
lean_inc(x_473);
lean_inc(x_472);
lean_dec(x_465);
x_474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set(x_474, 1, x_473);
return x_474;
}
}
}
block_484:
{
if (x_476 == 0)
{
x_456 = x_477;
goto block_475;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_inc(x_453);
x_478 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_478, 0, x_453);
x_479 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5;
x_480 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_480, 0, x_479);
lean_ctor_set(x_480, 1, x_478);
x_481 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_482 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_481, x_480, x_14, x_15, x_16, x_17, x_477);
x_483 = lean_ctor_get(x_482, 1);
lean_inc(x_483);
lean_dec(x_482);
x_456 = x_483;
goto block_475;
}
}
}
else
{
uint8_t x_501; 
lean_dec(x_447);
lean_dec(x_439);
lean_dec(x_424);
lean_dec(x_409);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_501 = !lean_is_exclusive(x_449);
if (x_501 == 0)
{
return x_449;
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_502 = lean_ctor_get(x_449, 0);
x_503 = lean_ctor_get(x_449, 1);
lean_inc(x_503);
lean_inc(x_502);
lean_dec(x_449);
x_504 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_503);
return x_504;
}
}
}
else
{
uint8_t x_505; 
lean_dec(x_439);
lean_dec(x_424);
lean_dec(x_409);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_505 = !lean_is_exclusive(x_444);
if (x_505 == 0)
{
return x_444;
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_506 = lean_ctor_get(x_444, 0);
x_507 = lean_ctor_get(x_444, 1);
lean_inc(x_507);
lean_inc(x_506);
lean_dec(x_444);
x_508 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_508, 0, x_506);
lean_ctor_set(x_508, 1, x_507);
return x_508;
}
}
}
else
{
uint8_t x_509; 
lean_dec(x_424);
lean_dec(x_409);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_509 = !lean_is_exclusive(x_436);
if (x_509 == 0)
{
return x_436;
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_510 = lean_ctor_get(x_436, 0);
x_511 = lean_ctor_get(x_436, 1);
lean_inc(x_511);
lean_inc(x_510);
lean_dec(x_436);
x_512 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_512, 0, x_510);
lean_ctor_set(x_512, 1, x_511);
return x_512;
}
}
}
}
else
{
uint8_t x_527; 
lean_dec(x_424);
lean_dec(x_413);
lean_dec(x_409);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_527 = !lean_is_exclusive(x_426);
if (x_527 == 0)
{
return x_426;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_528 = lean_ctor_get(x_426, 0);
x_529 = lean_ctor_get(x_426, 1);
lean_inc(x_529);
lean_inc(x_528);
lean_dec(x_426);
x_530 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_530, 0, x_528);
lean_ctor_set(x_530, 1, x_529);
return x_530;
}
}
}
else
{
uint8_t x_531; 
lean_dec(x_413);
lean_dec(x_409);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_531 = !lean_is_exclusive(x_423);
if (x_531 == 0)
{
return x_423;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_532 = lean_ctor_get(x_423, 0);
x_533 = lean_ctor_get(x_423, 1);
lean_inc(x_533);
lean_inc(x_532);
lean_dec(x_423);
x_534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_534, 0, x_532);
lean_ctor_set(x_534, 1, x_533);
return x_534;
}
}
}
else
{
uint8_t x_535; 
lean_dec(x_409);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_535 = !lean_is_exclusive(x_410);
if (x_535 == 0)
{
return x_410;
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_536 = lean_ctor_get(x_410, 0);
x_537 = lean_ctor_get(x_410, 1);
lean_inc(x_537);
lean_inc(x_536);
lean_dec(x_410);
x_538 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_537);
return x_538;
}
}
}
case 4:
{
lean_object* x_539; lean_object* x_540; 
lean_dec(x_13);
lean_dec(x_11);
x_539 = lean_ctor_get(x_8, 5);
lean_inc(x_539);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_540 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_7, x_10, x_12, x_539, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_540) == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_541 = lean_ctor_get(x_540, 1);
lean_inc(x_541);
lean_dec(x_540);
x_542 = l_Lean_getMCtx___at_Lean_getMVarDecl___spec__1___rarg(x_15, x_16, x_17, x_541);
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_542, 1);
lean_inc(x_544);
lean_dec(x_542);
x_545 = lean_ctor_get(x_8, 6);
lean_inc(x_545);
x_546 = l_List_redLength___main___rarg(x_545);
x_547 = lean_mk_empty_array_with_capacity(x_546);
lean_dec(x_546);
lean_inc(x_545);
x_548 = l_List_toArrayAux___main___rarg(x_545, x_547);
x_549 = x_548;
x_550 = lean_unsigned_to_nat(0u);
lean_inc(x_543);
lean_inc(x_7);
lean_inc(x_1);
x_551 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_551, 0, x_1);
lean_closure_set(x_551, 1, x_7);
lean_closure_set(x_551, 2, x_10);
lean_closure_set(x_551, 3, x_12);
lean_closure_set(x_551, 4, x_543);
lean_closure_set(x_551, 5, x_545);
lean_closure_set(x_551, 6, x_550);
lean_closure_set(x_551, 7, x_549);
x_552 = x_551;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_553 = lean_apply_5(x_552, x_14, x_15, x_16, x_17, x_544);
if (lean_obj_tag(x_553) == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_554 = lean_ctor_get(x_553, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_553, 1);
lean_inc(x_555);
lean_dec(x_553);
lean_inc(x_1);
x_556 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_555);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; lean_object* x_558; uint8_t x_559; lean_object* x_560; 
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
lean_dec(x_556);
x_559 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_559 == 0)
{
lean_object* x_644; uint8_t x_645; 
x_644 = l_Lean_MetavarContext_exprDependsOn(x_543, x_557, x_2);
x_645 = lean_unbox(x_644);
lean_dec(x_644);
if (x_645 == 0)
{
x_560 = x_558;
goto block_643;
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; uint8_t x_653; 
lean_dec(x_554);
lean_dec(x_539);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_646 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_646, 0, x_3);
x_647 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__6;
x_648 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_648, 0, x_647);
lean_ctor_set(x_648, 1, x_646);
x_649 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8;
x_650 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_650, 0, x_648);
lean_ctor_set(x_650, 1, x_649);
x_651 = lean_box(0);
x_652 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_650, x_651, x_14, x_15, x_16, x_17, x_558);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_653 = !lean_is_exclusive(x_652);
if (x_653 == 0)
{
return x_652;
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_654 = lean_ctor_get(x_652, 0);
x_655 = lean_ctor_get(x_652, 1);
lean_inc(x_655);
lean_inc(x_654);
lean_dec(x_652);
x_656 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_656, 0, x_654);
lean_ctor_set(x_656, 1, x_655);
return x_656;
}
}
}
else
{
lean_dec(x_557);
lean_dec(x_543);
x_560 = x_558;
goto block_643;
}
block_643:
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; uint8_t x_565; lean_object* x_566; 
lean_inc(x_554);
x_561 = x_554;
x_562 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_550, x_561);
x_563 = x_562;
x_564 = lean_array_push(x_563, x_2);
x_565 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_566 = l_Lean_Meta_revert(x_1, x_564, x_565, x_14, x_15, x_16, x_17, x_560);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; uint8_t x_573; lean_object* x_574; 
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_566, 1);
lean_inc(x_568);
lean_dec(x_566);
x_569 = lean_ctor_get(x_567, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_567, 1);
lean_inc(x_570);
lean_dec(x_567);
x_571 = lean_array_get_size(x_554);
x_572 = lean_box(0);
x_573 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_574 = l_Lean_Meta_introN(x_570, x_571, x_572, x_573, x_14, x_15, x_16, x_17, x_568);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_574, 1);
lean_inc(x_576);
lean_dec(x_574);
x_577 = lean_ctor_get(x_575, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_575, 1);
lean_inc(x_578);
lean_dec(x_575);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_579 = l_Lean_Meta_intro1(x_578, x_573, x_14, x_15, x_16, x_17, x_576);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; uint8_t x_606; lean_object* x_607; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_579, 1);
lean_inc(x_581);
lean_dec(x_579);
x_582 = lean_ctor_get(x_580, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_580, 1);
lean_inc(x_583);
lean_dec(x_580);
x_584 = lean_box(0);
x_585 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_554, x_577, x_554, x_550, x_584);
lean_dec(x_554);
x_615 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_616 = lean_ctor_get(x_615, 2);
lean_inc(x_616);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_617 = lean_apply_5(x_616, x_14, x_15, x_16, x_17, x_581);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; uint8_t x_619; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
x_619 = lean_ctor_get_uint8(x_618, sizeof(void*)*1);
lean_dec(x_618);
if (x_619 == 0)
{
lean_object* x_620; 
x_620 = lean_ctor_get(x_617, 1);
lean_inc(x_620);
lean_dec(x_617);
x_606 = x_573;
x_607 = x_620;
goto block_614;
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; uint8_t x_626; 
x_621 = lean_ctor_get(x_617, 1);
lean_inc(x_621);
lean_dec(x_617);
x_622 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_623 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_622, x_14, x_15, x_16, x_17, x_621);
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_623, 1);
lean_inc(x_625);
lean_dec(x_623);
x_626 = lean_unbox(x_624);
lean_dec(x_624);
x_606 = x_626;
x_607 = x_625;
goto block_614;
}
}
else
{
uint8_t x_627; 
lean_dec(x_585);
lean_dec(x_583);
lean_dec(x_582);
lean_dec(x_577);
lean_dec(x_569);
lean_dec(x_539);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_627 = !lean_is_exclusive(x_617);
if (x_627 == 0)
{
return x_617;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = lean_ctor_get(x_617, 0);
x_629 = lean_ctor_get(x_617, 1);
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_617);
x_630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_629);
return x_630;
}
}
block_605:
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_587 = x_577;
x_588 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_550, x_587);
x_589 = x_588;
lean_inc(x_582);
x_590 = l_Lean_mkFVar(x_582);
lean_inc(x_583);
x_591 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_591, 0, x_583);
x_592 = lean_box(x_559);
lean_inc(x_583);
x_593 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___lambda__1___boxed), 19, 13);
lean_closure_set(x_593, 0, x_582);
lean_closure_set(x_593, 1, x_9);
lean_closure_set(x_593, 2, x_583);
lean_closure_set(x_593, 3, x_3);
lean_closure_set(x_593, 4, x_4);
lean_closure_set(x_593, 5, x_7);
lean_closure_set(x_593, 6, x_8);
lean_closure_set(x_593, 7, x_539);
lean_closure_set(x_593, 8, x_592);
lean_closure_set(x_593, 9, x_569);
lean_closure_set(x_593, 10, x_585);
lean_closure_set(x_593, 11, x_589);
lean_closure_set(x_593, 12, x_590);
x_594 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_594, 0, x_591);
lean_closure_set(x_594, 1, x_593);
x_595 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_583, x_14, x_15, x_16, x_17, x_586);
if (lean_obj_tag(x_595) == 0)
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_595, 1);
lean_inc(x_597);
lean_dec(x_595);
x_598 = lean_ctor_get(x_596, 1);
lean_inc(x_598);
x_599 = lean_ctor_get(x_596, 4);
lean_inc(x_599);
lean_dec(x_596);
x_600 = l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(x_598, x_599, x_594, x_14, x_15, x_16, x_17, x_597);
return x_600;
}
else
{
uint8_t x_601; 
lean_dec(x_594);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_601 = !lean_is_exclusive(x_595);
if (x_601 == 0)
{
return x_595;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_ctor_get(x_595, 0);
x_603 = lean_ctor_get(x_595, 1);
lean_inc(x_603);
lean_inc(x_602);
lean_dec(x_595);
x_604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set(x_604, 1, x_603);
return x_604;
}
}
}
block_614:
{
if (x_606 == 0)
{
x_586 = x_607;
goto block_605;
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_inc(x_583);
x_608 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_608, 0, x_583);
x_609 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5;
x_610 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_610, 0, x_609);
lean_ctor_set(x_610, 1, x_608);
x_611 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_612 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_611, x_610, x_14, x_15, x_16, x_17, x_607);
x_613 = lean_ctor_get(x_612, 1);
lean_inc(x_613);
lean_dec(x_612);
x_586 = x_613;
goto block_605;
}
}
}
else
{
uint8_t x_631; 
lean_dec(x_577);
lean_dec(x_569);
lean_dec(x_554);
lean_dec(x_539);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_631 = !lean_is_exclusive(x_579);
if (x_631 == 0)
{
return x_579;
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_632 = lean_ctor_get(x_579, 0);
x_633 = lean_ctor_get(x_579, 1);
lean_inc(x_633);
lean_inc(x_632);
lean_dec(x_579);
x_634 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_634, 0, x_632);
lean_ctor_set(x_634, 1, x_633);
return x_634;
}
}
}
else
{
uint8_t x_635; 
lean_dec(x_569);
lean_dec(x_554);
lean_dec(x_539);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_635 = !lean_is_exclusive(x_574);
if (x_635 == 0)
{
return x_574;
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_636 = lean_ctor_get(x_574, 0);
x_637 = lean_ctor_get(x_574, 1);
lean_inc(x_637);
lean_inc(x_636);
lean_dec(x_574);
x_638 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_638, 0, x_636);
lean_ctor_set(x_638, 1, x_637);
return x_638;
}
}
}
else
{
uint8_t x_639; 
lean_dec(x_554);
lean_dec(x_539);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_639 = !lean_is_exclusive(x_566);
if (x_639 == 0)
{
return x_566;
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_640 = lean_ctor_get(x_566, 0);
x_641 = lean_ctor_get(x_566, 1);
lean_inc(x_641);
lean_inc(x_640);
lean_dec(x_566);
x_642 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_642, 0, x_640);
lean_ctor_set(x_642, 1, x_641);
return x_642;
}
}
}
}
else
{
uint8_t x_657; 
lean_dec(x_554);
lean_dec(x_543);
lean_dec(x_539);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_657 = !lean_is_exclusive(x_556);
if (x_657 == 0)
{
return x_556;
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_658 = lean_ctor_get(x_556, 0);
x_659 = lean_ctor_get(x_556, 1);
lean_inc(x_659);
lean_inc(x_658);
lean_dec(x_556);
x_660 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_660, 0, x_658);
lean_ctor_set(x_660, 1, x_659);
return x_660;
}
}
}
else
{
uint8_t x_661; 
lean_dec(x_543);
lean_dec(x_539);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_661 = !lean_is_exclusive(x_553);
if (x_661 == 0)
{
return x_553;
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_662 = lean_ctor_get(x_553, 0);
x_663 = lean_ctor_get(x_553, 1);
lean_inc(x_663);
lean_inc(x_662);
lean_dec(x_553);
x_664 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_664, 0, x_662);
lean_ctor_set(x_664, 1, x_663);
return x_664;
}
}
}
else
{
uint8_t x_665; 
lean_dec(x_539);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_665 = !lean_is_exclusive(x_540);
if (x_665 == 0)
{
return x_540;
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_666 = lean_ctor_get(x_540, 0);
x_667 = lean_ctor_get(x_540, 1);
lean_inc(x_667);
lean_inc(x_666);
lean_dec(x_540);
x_668 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_668, 0, x_666);
lean_ctor_set(x_668, 1, x_667);
return x_668;
}
}
}
case 5:
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_669 = lean_ctor_get(x_11, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_11, 1);
lean_inc(x_670);
lean_dec(x_11);
x_671 = lean_array_set(x_12, x_13, x_670);
x_672 = lean_unsigned_to_nat(1u);
x_673 = lean_nat_sub(x_13, x_672);
lean_dec(x_13);
x_11 = x_669;
x_12 = x_671;
x_13 = x_673;
goto _start;
}
case 6:
{
lean_object* x_675; lean_object* x_676; 
lean_dec(x_13);
lean_dec(x_11);
x_675 = lean_ctor_get(x_8, 5);
lean_inc(x_675);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_676 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_7, x_10, x_12, x_675, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_677 = lean_ctor_get(x_676, 1);
lean_inc(x_677);
lean_dec(x_676);
x_678 = l_Lean_getMCtx___at_Lean_getMVarDecl___spec__1___rarg(x_15, x_16, x_17, x_677);
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_678, 1);
lean_inc(x_680);
lean_dec(x_678);
x_681 = lean_ctor_get(x_8, 6);
lean_inc(x_681);
x_682 = l_List_redLength___main___rarg(x_681);
x_683 = lean_mk_empty_array_with_capacity(x_682);
lean_dec(x_682);
lean_inc(x_681);
x_684 = l_List_toArrayAux___main___rarg(x_681, x_683);
x_685 = x_684;
x_686 = lean_unsigned_to_nat(0u);
lean_inc(x_679);
lean_inc(x_7);
lean_inc(x_1);
x_687 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_687, 0, x_1);
lean_closure_set(x_687, 1, x_7);
lean_closure_set(x_687, 2, x_10);
lean_closure_set(x_687, 3, x_12);
lean_closure_set(x_687, 4, x_679);
lean_closure_set(x_687, 5, x_681);
lean_closure_set(x_687, 6, x_686);
lean_closure_set(x_687, 7, x_685);
x_688 = x_687;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_689 = lean_apply_5(x_688, x_14, x_15, x_16, x_17, x_680);
if (lean_obj_tag(x_689) == 0)
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_690 = lean_ctor_get(x_689, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_689, 1);
lean_inc(x_691);
lean_dec(x_689);
lean_inc(x_1);
x_692 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_691);
if (lean_obj_tag(x_692) == 0)
{
lean_object* x_693; lean_object* x_694; uint8_t x_695; lean_object* x_696; 
x_693 = lean_ctor_get(x_692, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_692, 1);
lean_inc(x_694);
lean_dec(x_692);
x_695 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_695 == 0)
{
lean_object* x_780; uint8_t x_781; 
x_780 = l_Lean_MetavarContext_exprDependsOn(x_679, x_693, x_2);
x_781 = lean_unbox(x_780);
lean_dec(x_780);
if (x_781 == 0)
{
x_696 = x_694;
goto block_779;
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; uint8_t x_789; 
lean_dec(x_690);
lean_dec(x_675);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_782 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_782, 0, x_3);
x_783 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__6;
x_784 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_784, 0, x_783);
lean_ctor_set(x_784, 1, x_782);
x_785 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8;
x_786 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_786, 0, x_784);
lean_ctor_set(x_786, 1, x_785);
x_787 = lean_box(0);
x_788 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_786, x_787, x_14, x_15, x_16, x_17, x_694);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_789 = !lean_is_exclusive(x_788);
if (x_789 == 0)
{
return x_788;
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_790 = lean_ctor_get(x_788, 0);
x_791 = lean_ctor_get(x_788, 1);
lean_inc(x_791);
lean_inc(x_790);
lean_dec(x_788);
x_792 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_792, 0, x_790);
lean_ctor_set(x_792, 1, x_791);
return x_792;
}
}
}
else
{
lean_dec(x_693);
lean_dec(x_679);
x_696 = x_694;
goto block_779;
}
block_779:
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; uint8_t x_701; lean_object* x_702; 
lean_inc(x_690);
x_697 = x_690;
x_698 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_686, x_697);
x_699 = x_698;
x_700 = lean_array_push(x_699, x_2);
x_701 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_702 = l_Lean_Meta_revert(x_1, x_700, x_701, x_14, x_15, x_16, x_17, x_696);
if (lean_obj_tag(x_702) == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; uint8_t x_709; lean_object* x_710; 
x_703 = lean_ctor_get(x_702, 0);
lean_inc(x_703);
x_704 = lean_ctor_get(x_702, 1);
lean_inc(x_704);
lean_dec(x_702);
x_705 = lean_ctor_get(x_703, 0);
lean_inc(x_705);
x_706 = lean_ctor_get(x_703, 1);
lean_inc(x_706);
lean_dec(x_703);
x_707 = lean_array_get_size(x_690);
x_708 = lean_box(0);
x_709 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_710 = l_Lean_Meta_introN(x_706, x_707, x_708, x_709, x_14, x_15, x_16, x_17, x_704);
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_711 = lean_ctor_get(x_710, 0);
lean_inc(x_711);
x_712 = lean_ctor_get(x_710, 1);
lean_inc(x_712);
lean_dec(x_710);
x_713 = lean_ctor_get(x_711, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_711, 1);
lean_inc(x_714);
lean_dec(x_711);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_715 = l_Lean_Meta_intro1(x_714, x_709, x_14, x_15, x_16, x_17, x_712);
if (lean_obj_tag(x_715) == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; uint8_t x_742; lean_object* x_743; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_716 = lean_ctor_get(x_715, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_715, 1);
lean_inc(x_717);
lean_dec(x_715);
x_718 = lean_ctor_get(x_716, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_716, 1);
lean_inc(x_719);
lean_dec(x_716);
x_720 = lean_box(0);
x_721 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_690, x_713, x_690, x_686, x_720);
lean_dec(x_690);
x_751 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_752 = lean_ctor_get(x_751, 2);
lean_inc(x_752);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_753 = lean_apply_5(x_752, x_14, x_15, x_16, x_17, x_717);
if (lean_obj_tag(x_753) == 0)
{
lean_object* x_754; uint8_t x_755; 
x_754 = lean_ctor_get(x_753, 0);
lean_inc(x_754);
x_755 = lean_ctor_get_uint8(x_754, sizeof(void*)*1);
lean_dec(x_754);
if (x_755 == 0)
{
lean_object* x_756; 
x_756 = lean_ctor_get(x_753, 1);
lean_inc(x_756);
lean_dec(x_753);
x_742 = x_709;
x_743 = x_756;
goto block_750;
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; uint8_t x_762; 
x_757 = lean_ctor_get(x_753, 1);
lean_inc(x_757);
lean_dec(x_753);
x_758 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_759 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_758, x_14, x_15, x_16, x_17, x_757);
x_760 = lean_ctor_get(x_759, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_759, 1);
lean_inc(x_761);
lean_dec(x_759);
x_762 = lean_unbox(x_760);
lean_dec(x_760);
x_742 = x_762;
x_743 = x_761;
goto block_750;
}
}
else
{
uint8_t x_763; 
lean_dec(x_721);
lean_dec(x_719);
lean_dec(x_718);
lean_dec(x_713);
lean_dec(x_705);
lean_dec(x_675);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_763 = !lean_is_exclusive(x_753);
if (x_763 == 0)
{
return x_753;
}
else
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_764 = lean_ctor_get(x_753, 0);
x_765 = lean_ctor_get(x_753, 1);
lean_inc(x_765);
lean_inc(x_764);
lean_dec(x_753);
x_766 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_766, 0, x_764);
lean_ctor_set(x_766, 1, x_765);
return x_766;
}
}
block_741:
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_723 = x_713;
x_724 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_686, x_723);
x_725 = x_724;
lean_inc(x_718);
x_726 = l_Lean_mkFVar(x_718);
lean_inc(x_719);
x_727 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_727, 0, x_719);
x_728 = lean_box(x_695);
lean_inc(x_719);
x_729 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___lambda__1___boxed), 19, 13);
lean_closure_set(x_729, 0, x_718);
lean_closure_set(x_729, 1, x_9);
lean_closure_set(x_729, 2, x_719);
lean_closure_set(x_729, 3, x_3);
lean_closure_set(x_729, 4, x_4);
lean_closure_set(x_729, 5, x_7);
lean_closure_set(x_729, 6, x_8);
lean_closure_set(x_729, 7, x_675);
lean_closure_set(x_729, 8, x_728);
lean_closure_set(x_729, 9, x_705);
lean_closure_set(x_729, 10, x_721);
lean_closure_set(x_729, 11, x_725);
lean_closure_set(x_729, 12, x_726);
x_730 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_730, 0, x_727);
lean_closure_set(x_730, 1, x_729);
x_731 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_719, x_14, x_15, x_16, x_17, x_722);
if (lean_obj_tag(x_731) == 0)
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_732 = lean_ctor_get(x_731, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_731, 1);
lean_inc(x_733);
lean_dec(x_731);
x_734 = lean_ctor_get(x_732, 1);
lean_inc(x_734);
x_735 = lean_ctor_get(x_732, 4);
lean_inc(x_735);
lean_dec(x_732);
x_736 = l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(x_734, x_735, x_730, x_14, x_15, x_16, x_17, x_733);
return x_736;
}
else
{
uint8_t x_737; 
lean_dec(x_730);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_737 = !lean_is_exclusive(x_731);
if (x_737 == 0)
{
return x_731;
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_738 = lean_ctor_get(x_731, 0);
x_739 = lean_ctor_get(x_731, 1);
lean_inc(x_739);
lean_inc(x_738);
lean_dec(x_731);
x_740 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_740, 0, x_738);
lean_ctor_set(x_740, 1, x_739);
return x_740;
}
}
}
block_750:
{
if (x_742 == 0)
{
x_722 = x_743;
goto block_741;
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
lean_inc(x_719);
x_744 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_744, 0, x_719);
x_745 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5;
x_746 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_746, 0, x_745);
lean_ctor_set(x_746, 1, x_744);
x_747 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_748 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_747, x_746, x_14, x_15, x_16, x_17, x_743);
x_749 = lean_ctor_get(x_748, 1);
lean_inc(x_749);
lean_dec(x_748);
x_722 = x_749;
goto block_741;
}
}
}
else
{
uint8_t x_767; 
lean_dec(x_713);
lean_dec(x_705);
lean_dec(x_690);
lean_dec(x_675);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_767 = !lean_is_exclusive(x_715);
if (x_767 == 0)
{
return x_715;
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; 
x_768 = lean_ctor_get(x_715, 0);
x_769 = lean_ctor_get(x_715, 1);
lean_inc(x_769);
lean_inc(x_768);
lean_dec(x_715);
x_770 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_770, 0, x_768);
lean_ctor_set(x_770, 1, x_769);
return x_770;
}
}
}
else
{
uint8_t x_771; 
lean_dec(x_705);
lean_dec(x_690);
lean_dec(x_675);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_771 = !lean_is_exclusive(x_710);
if (x_771 == 0)
{
return x_710;
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_772 = lean_ctor_get(x_710, 0);
x_773 = lean_ctor_get(x_710, 1);
lean_inc(x_773);
lean_inc(x_772);
lean_dec(x_710);
x_774 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_774, 0, x_772);
lean_ctor_set(x_774, 1, x_773);
return x_774;
}
}
}
else
{
uint8_t x_775; 
lean_dec(x_690);
lean_dec(x_675);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_775 = !lean_is_exclusive(x_702);
if (x_775 == 0)
{
return x_702;
}
else
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_776 = lean_ctor_get(x_702, 0);
x_777 = lean_ctor_get(x_702, 1);
lean_inc(x_777);
lean_inc(x_776);
lean_dec(x_702);
x_778 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_778, 0, x_776);
lean_ctor_set(x_778, 1, x_777);
return x_778;
}
}
}
}
else
{
uint8_t x_793; 
lean_dec(x_690);
lean_dec(x_679);
lean_dec(x_675);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_793 = !lean_is_exclusive(x_692);
if (x_793 == 0)
{
return x_692;
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; 
x_794 = lean_ctor_get(x_692, 0);
x_795 = lean_ctor_get(x_692, 1);
lean_inc(x_795);
lean_inc(x_794);
lean_dec(x_692);
x_796 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_796, 0, x_794);
lean_ctor_set(x_796, 1, x_795);
return x_796;
}
}
}
else
{
uint8_t x_797; 
lean_dec(x_679);
lean_dec(x_675);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_797 = !lean_is_exclusive(x_689);
if (x_797 == 0)
{
return x_689;
}
else
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; 
x_798 = lean_ctor_get(x_689, 0);
x_799 = lean_ctor_get(x_689, 1);
lean_inc(x_799);
lean_inc(x_798);
lean_dec(x_689);
x_800 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_800, 0, x_798);
lean_ctor_set(x_800, 1, x_799);
return x_800;
}
}
}
else
{
uint8_t x_801; 
lean_dec(x_675);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_801 = !lean_is_exclusive(x_676);
if (x_801 == 0)
{
return x_676;
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; 
x_802 = lean_ctor_get(x_676, 0);
x_803 = lean_ctor_get(x_676, 1);
lean_inc(x_803);
lean_inc(x_802);
lean_dec(x_676);
x_804 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_804, 0, x_802);
lean_ctor_set(x_804, 1, x_803);
return x_804;
}
}
}
case 7:
{
lean_object* x_805; lean_object* x_806; 
lean_dec(x_13);
lean_dec(x_11);
x_805 = lean_ctor_get(x_8, 5);
lean_inc(x_805);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_806 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_7, x_10, x_12, x_805, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_806) == 0)
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_807 = lean_ctor_get(x_806, 1);
lean_inc(x_807);
lean_dec(x_806);
x_808 = l_Lean_getMCtx___at_Lean_getMVarDecl___spec__1___rarg(x_15, x_16, x_17, x_807);
x_809 = lean_ctor_get(x_808, 0);
lean_inc(x_809);
x_810 = lean_ctor_get(x_808, 1);
lean_inc(x_810);
lean_dec(x_808);
x_811 = lean_ctor_get(x_8, 6);
lean_inc(x_811);
x_812 = l_List_redLength___main___rarg(x_811);
x_813 = lean_mk_empty_array_with_capacity(x_812);
lean_dec(x_812);
lean_inc(x_811);
x_814 = l_List_toArrayAux___main___rarg(x_811, x_813);
x_815 = x_814;
x_816 = lean_unsigned_to_nat(0u);
lean_inc(x_809);
lean_inc(x_7);
lean_inc(x_1);
x_817 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_817, 0, x_1);
lean_closure_set(x_817, 1, x_7);
lean_closure_set(x_817, 2, x_10);
lean_closure_set(x_817, 3, x_12);
lean_closure_set(x_817, 4, x_809);
lean_closure_set(x_817, 5, x_811);
lean_closure_set(x_817, 6, x_816);
lean_closure_set(x_817, 7, x_815);
x_818 = x_817;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_819 = lean_apply_5(x_818, x_14, x_15, x_16, x_17, x_810);
if (lean_obj_tag(x_819) == 0)
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; 
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_819, 1);
lean_inc(x_821);
lean_dec(x_819);
lean_inc(x_1);
x_822 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_821);
if (lean_obj_tag(x_822) == 0)
{
lean_object* x_823; lean_object* x_824; uint8_t x_825; lean_object* x_826; 
x_823 = lean_ctor_get(x_822, 0);
lean_inc(x_823);
x_824 = lean_ctor_get(x_822, 1);
lean_inc(x_824);
lean_dec(x_822);
x_825 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_825 == 0)
{
lean_object* x_910; uint8_t x_911; 
x_910 = l_Lean_MetavarContext_exprDependsOn(x_809, x_823, x_2);
x_911 = lean_unbox(x_910);
lean_dec(x_910);
if (x_911 == 0)
{
x_826 = x_824;
goto block_909;
}
else
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; uint8_t x_919; 
lean_dec(x_820);
lean_dec(x_805);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_912 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_912, 0, x_3);
x_913 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__6;
x_914 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_914, 0, x_913);
lean_ctor_set(x_914, 1, x_912);
x_915 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8;
x_916 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_916, 0, x_914);
lean_ctor_set(x_916, 1, x_915);
x_917 = lean_box(0);
x_918 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_916, x_917, x_14, x_15, x_16, x_17, x_824);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_919 = !lean_is_exclusive(x_918);
if (x_919 == 0)
{
return x_918;
}
else
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; 
x_920 = lean_ctor_get(x_918, 0);
x_921 = lean_ctor_get(x_918, 1);
lean_inc(x_921);
lean_inc(x_920);
lean_dec(x_918);
x_922 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_922, 0, x_920);
lean_ctor_set(x_922, 1, x_921);
return x_922;
}
}
}
else
{
lean_dec(x_823);
lean_dec(x_809);
x_826 = x_824;
goto block_909;
}
block_909:
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; uint8_t x_831; lean_object* x_832; 
lean_inc(x_820);
x_827 = x_820;
x_828 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_816, x_827);
x_829 = x_828;
x_830 = lean_array_push(x_829, x_2);
x_831 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_832 = l_Lean_Meta_revert(x_1, x_830, x_831, x_14, x_15, x_16, x_17, x_826);
if (lean_obj_tag(x_832) == 0)
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; uint8_t x_839; lean_object* x_840; 
x_833 = lean_ctor_get(x_832, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_832, 1);
lean_inc(x_834);
lean_dec(x_832);
x_835 = lean_ctor_get(x_833, 0);
lean_inc(x_835);
x_836 = lean_ctor_get(x_833, 1);
lean_inc(x_836);
lean_dec(x_833);
x_837 = lean_array_get_size(x_820);
x_838 = lean_box(0);
x_839 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_840 = l_Lean_Meta_introN(x_836, x_837, x_838, x_839, x_14, x_15, x_16, x_17, x_834);
if (lean_obj_tag(x_840) == 0)
{
lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; 
x_841 = lean_ctor_get(x_840, 0);
lean_inc(x_841);
x_842 = lean_ctor_get(x_840, 1);
lean_inc(x_842);
lean_dec(x_840);
x_843 = lean_ctor_get(x_841, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_841, 1);
lean_inc(x_844);
lean_dec(x_841);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_845 = l_Lean_Meta_intro1(x_844, x_839, x_14, x_15, x_16, x_17, x_842);
if (lean_obj_tag(x_845) == 0)
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; uint8_t x_872; lean_object* x_873; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_845, 1);
lean_inc(x_847);
lean_dec(x_845);
x_848 = lean_ctor_get(x_846, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_846, 1);
lean_inc(x_849);
lean_dec(x_846);
x_850 = lean_box(0);
x_851 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_820, x_843, x_820, x_816, x_850);
lean_dec(x_820);
x_881 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_882 = lean_ctor_get(x_881, 2);
lean_inc(x_882);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_883 = lean_apply_5(x_882, x_14, x_15, x_16, x_17, x_847);
if (lean_obj_tag(x_883) == 0)
{
lean_object* x_884; uint8_t x_885; 
x_884 = lean_ctor_get(x_883, 0);
lean_inc(x_884);
x_885 = lean_ctor_get_uint8(x_884, sizeof(void*)*1);
lean_dec(x_884);
if (x_885 == 0)
{
lean_object* x_886; 
x_886 = lean_ctor_get(x_883, 1);
lean_inc(x_886);
lean_dec(x_883);
x_872 = x_839;
x_873 = x_886;
goto block_880;
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; uint8_t x_892; 
x_887 = lean_ctor_get(x_883, 1);
lean_inc(x_887);
lean_dec(x_883);
x_888 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_889 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_888, x_14, x_15, x_16, x_17, x_887);
x_890 = lean_ctor_get(x_889, 0);
lean_inc(x_890);
x_891 = lean_ctor_get(x_889, 1);
lean_inc(x_891);
lean_dec(x_889);
x_892 = lean_unbox(x_890);
lean_dec(x_890);
x_872 = x_892;
x_873 = x_891;
goto block_880;
}
}
else
{
uint8_t x_893; 
lean_dec(x_851);
lean_dec(x_849);
lean_dec(x_848);
lean_dec(x_843);
lean_dec(x_835);
lean_dec(x_805);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_893 = !lean_is_exclusive(x_883);
if (x_893 == 0)
{
return x_883;
}
else
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; 
x_894 = lean_ctor_get(x_883, 0);
x_895 = lean_ctor_get(x_883, 1);
lean_inc(x_895);
lean_inc(x_894);
lean_dec(x_883);
x_896 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_896, 0, x_894);
lean_ctor_set(x_896, 1, x_895);
return x_896;
}
}
block_871:
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; 
x_853 = x_843;
x_854 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_816, x_853);
x_855 = x_854;
lean_inc(x_848);
x_856 = l_Lean_mkFVar(x_848);
lean_inc(x_849);
x_857 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_857, 0, x_849);
x_858 = lean_box(x_825);
lean_inc(x_849);
x_859 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___lambda__1___boxed), 19, 13);
lean_closure_set(x_859, 0, x_848);
lean_closure_set(x_859, 1, x_9);
lean_closure_set(x_859, 2, x_849);
lean_closure_set(x_859, 3, x_3);
lean_closure_set(x_859, 4, x_4);
lean_closure_set(x_859, 5, x_7);
lean_closure_set(x_859, 6, x_8);
lean_closure_set(x_859, 7, x_805);
lean_closure_set(x_859, 8, x_858);
lean_closure_set(x_859, 9, x_835);
lean_closure_set(x_859, 10, x_851);
lean_closure_set(x_859, 11, x_855);
lean_closure_set(x_859, 12, x_856);
x_860 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_860, 0, x_857);
lean_closure_set(x_860, 1, x_859);
x_861 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_849, x_14, x_15, x_16, x_17, x_852);
if (lean_obj_tag(x_861) == 0)
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; 
x_862 = lean_ctor_get(x_861, 0);
lean_inc(x_862);
x_863 = lean_ctor_get(x_861, 1);
lean_inc(x_863);
lean_dec(x_861);
x_864 = lean_ctor_get(x_862, 1);
lean_inc(x_864);
x_865 = lean_ctor_get(x_862, 4);
lean_inc(x_865);
lean_dec(x_862);
x_866 = l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(x_864, x_865, x_860, x_14, x_15, x_16, x_17, x_863);
return x_866;
}
else
{
uint8_t x_867; 
lean_dec(x_860);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_867 = !lean_is_exclusive(x_861);
if (x_867 == 0)
{
return x_861;
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; 
x_868 = lean_ctor_get(x_861, 0);
x_869 = lean_ctor_get(x_861, 1);
lean_inc(x_869);
lean_inc(x_868);
lean_dec(x_861);
x_870 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_870, 0, x_868);
lean_ctor_set(x_870, 1, x_869);
return x_870;
}
}
}
block_880:
{
if (x_872 == 0)
{
x_852 = x_873;
goto block_871;
}
else
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; 
lean_inc(x_849);
x_874 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_874, 0, x_849);
x_875 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5;
x_876 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_876, 0, x_875);
lean_ctor_set(x_876, 1, x_874);
x_877 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_878 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_877, x_876, x_14, x_15, x_16, x_17, x_873);
x_879 = lean_ctor_get(x_878, 1);
lean_inc(x_879);
lean_dec(x_878);
x_852 = x_879;
goto block_871;
}
}
}
else
{
uint8_t x_897; 
lean_dec(x_843);
lean_dec(x_835);
lean_dec(x_820);
lean_dec(x_805);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_897 = !lean_is_exclusive(x_845);
if (x_897 == 0)
{
return x_845;
}
else
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; 
x_898 = lean_ctor_get(x_845, 0);
x_899 = lean_ctor_get(x_845, 1);
lean_inc(x_899);
lean_inc(x_898);
lean_dec(x_845);
x_900 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_900, 0, x_898);
lean_ctor_set(x_900, 1, x_899);
return x_900;
}
}
}
else
{
uint8_t x_901; 
lean_dec(x_835);
lean_dec(x_820);
lean_dec(x_805);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_901 = !lean_is_exclusive(x_840);
if (x_901 == 0)
{
return x_840;
}
else
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; 
x_902 = lean_ctor_get(x_840, 0);
x_903 = lean_ctor_get(x_840, 1);
lean_inc(x_903);
lean_inc(x_902);
lean_dec(x_840);
x_904 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_904, 0, x_902);
lean_ctor_set(x_904, 1, x_903);
return x_904;
}
}
}
else
{
uint8_t x_905; 
lean_dec(x_820);
lean_dec(x_805);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_905 = !lean_is_exclusive(x_832);
if (x_905 == 0)
{
return x_832;
}
else
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; 
x_906 = lean_ctor_get(x_832, 0);
x_907 = lean_ctor_get(x_832, 1);
lean_inc(x_907);
lean_inc(x_906);
lean_dec(x_832);
x_908 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_908, 0, x_906);
lean_ctor_set(x_908, 1, x_907);
return x_908;
}
}
}
}
else
{
uint8_t x_923; 
lean_dec(x_820);
lean_dec(x_809);
lean_dec(x_805);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_923 = !lean_is_exclusive(x_822);
if (x_923 == 0)
{
return x_822;
}
else
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; 
x_924 = lean_ctor_get(x_822, 0);
x_925 = lean_ctor_get(x_822, 1);
lean_inc(x_925);
lean_inc(x_924);
lean_dec(x_822);
x_926 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_926, 0, x_924);
lean_ctor_set(x_926, 1, x_925);
return x_926;
}
}
}
else
{
uint8_t x_927; 
lean_dec(x_809);
lean_dec(x_805);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_927 = !lean_is_exclusive(x_819);
if (x_927 == 0)
{
return x_819;
}
else
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; 
x_928 = lean_ctor_get(x_819, 0);
x_929 = lean_ctor_get(x_819, 1);
lean_inc(x_929);
lean_inc(x_928);
lean_dec(x_819);
x_930 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_930, 0, x_928);
lean_ctor_set(x_930, 1, x_929);
return x_930;
}
}
}
else
{
uint8_t x_931; 
lean_dec(x_805);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_931 = !lean_is_exclusive(x_806);
if (x_931 == 0)
{
return x_806;
}
else
{
lean_object* x_932; lean_object* x_933; lean_object* x_934; 
x_932 = lean_ctor_get(x_806, 0);
x_933 = lean_ctor_get(x_806, 1);
lean_inc(x_933);
lean_inc(x_932);
lean_dec(x_806);
x_934 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_934, 0, x_932);
lean_ctor_set(x_934, 1, x_933);
return x_934;
}
}
}
case 8:
{
lean_object* x_935; lean_object* x_936; 
lean_dec(x_13);
lean_dec(x_11);
x_935 = lean_ctor_get(x_8, 5);
lean_inc(x_935);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_936 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_7, x_10, x_12, x_935, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_936) == 0)
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; 
x_937 = lean_ctor_get(x_936, 1);
lean_inc(x_937);
lean_dec(x_936);
x_938 = l_Lean_getMCtx___at_Lean_getMVarDecl___spec__1___rarg(x_15, x_16, x_17, x_937);
x_939 = lean_ctor_get(x_938, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_938, 1);
lean_inc(x_940);
lean_dec(x_938);
x_941 = lean_ctor_get(x_8, 6);
lean_inc(x_941);
x_942 = l_List_redLength___main___rarg(x_941);
x_943 = lean_mk_empty_array_with_capacity(x_942);
lean_dec(x_942);
lean_inc(x_941);
x_944 = l_List_toArrayAux___main___rarg(x_941, x_943);
x_945 = x_944;
x_946 = lean_unsigned_to_nat(0u);
lean_inc(x_939);
lean_inc(x_7);
lean_inc(x_1);
x_947 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_947, 0, x_1);
lean_closure_set(x_947, 1, x_7);
lean_closure_set(x_947, 2, x_10);
lean_closure_set(x_947, 3, x_12);
lean_closure_set(x_947, 4, x_939);
lean_closure_set(x_947, 5, x_941);
lean_closure_set(x_947, 6, x_946);
lean_closure_set(x_947, 7, x_945);
x_948 = x_947;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_949 = lean_apply_5(x_948, x_14, x_15, x_16, x_17, x_940);
if (lean_obj_tag(x_949) == 0)
{
lean_object* x_950; lean_object* x_951; lean_object* x_952; 
x_950 = lean_ctor_get(x_949, 0);
lean_inc(x_950);
x_951 = lean_ctor_get(x_949, 1);
lean_inc(x_951);
lean_dec(x_949);
lean_inc(x_1);
x_952 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_951);
if (lean_obj_tag(x_952) == 0)
{
lean_object* x_953; lean_object* x_954; uint8_t x_955; lean_object* x_956; 
x_953 = lean_ctor_get(x_952, 0);
lean_inc(x_953);
x_954 = lean_ctor_get(x_952, 1);
lean_inc(x_954);
lean_dec(x_952);
x_955 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_955 == 0)
{
lean_object* x_1040; uint8_t x_1041; 
x_1040 = l_Lean_MetavarContext_exprDependsOn(x_939, x_953, x_2);
x_1041 = lean_unbox(x_1040);
lean_dec(x_1040);
if (x_1041 == 0)
{
x_956 = x_954;
goto block_1039;
}
else
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; uint8_t x_1049; 
lean_dec(x_950);
lean_dec(x_935);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_1042 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1042, 0, x_3);
x_1043 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__6;
x_1044 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1044, 0, x_1043);
lean_ctor_set(x_1044, 1, x_1042);
x_1045 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8;
x_1046 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1046, 0, x_1044);
lean_ctor_set(x_1046, 1, x_1045);
x_1047 = lean_box(0);
x_1048 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_1046, x_1047, x_14, x_15, x_16, x_17, x_954);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_1049 = !lean_is_exclusive(x_1048);
if (x_1049 == 0)
{
return x_1048;
}
else
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; 
x_1050 = lean_ctor_get(x_1048, 0);
x_1051 = lean_ctor_get(x_1048, 1);
lean_inc(x_1051);
lean_inc(x_1050);
lean_dec(x_1048);
x_1052 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1052, 0, x_1050);
lean_ctor_set(x_1052, 1, x_1051);
return x_1052;
}
}
}
else
{
lean_dec(x_953);
lean_dec(x_939);
x_956 = x_954;
goto block_1039;
}
block_1039:
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; uint8_t x_961; lean_object* x_962; 
lean_inc(x_950);
x_957 = x_950;
x_958 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_946, x_957);
x_959 = x_958;
x_960 = lean_array_push(x_959, x_2);
x_961 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_962 = l_Lean_Meta_revert(x_1, x_960, x_961, x_14, x_15, x_16, x_17, x_956);
if (lean_obj_tag(x_962) == 0)
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; uint8_t x_969; lean_object* x_970; 
x_963 = lean_ctor_get(x_962, 0);
lean_inc(x_963);
x_964 = lean_ctor_get(x_962, 1);
lean_inc(x_964);
lean_dec(x_962);
x_965 = lean_ctor_get(x_963, 0);
lean_inc(x_965);
x_966 = lean_ctor_get(x_963, 1);
lean_inc(x_966);
lean_dec(x_963);
x_967 = lean_array_get_size(x_950);
x_968 = lean_box(0);
x_969 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_970 = l_Lean_Meta_introN(x_966, x_967, x_968, x_969, x_14, x_15, x_16, x_17, x_964);
if (lean_obj_tag(x_970) == 0)
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; 
x_971 = lean_ctor_get(x_970, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_970, 1);
lean_inc(x_972);
lean_dec(x_970);
x_973 = lean_ctor_get(x_971, 0);
lean_inc(x_973);
x_974 = lean_ctor_get(x_971, 1);
lean_inc(x_974);
lean_dec(x_971);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_975 = l_Lean_Meta_intro1(x_974, x_969, x_14, x_15, x_16, x_17, x_972);
if (lean_obj_tag(x_975) == 0)
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; uint8_t x_1002; lean_object* x_1003; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
x_976 = lean_ctor_get(x_975, 0);
lean_inc(x_976);
x_977 = lean_ctor_get(x_975, 1);
lean_inc(x_977);
lean_dec(x_975);
x_978 = lean_ctor_get(x_976, 0);
lean_inc(x_978);
x_979 = lean_ctor_get(x_976, 1);
lean_inc(x_979);
lean_dec(x_976);
x_980 = lean_box(0);
x_981 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_950, x_973, x_950, x_946, x_980);
lean_dec(x_950);
x_1011 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_1012 = lean_ctor_get(x_1011, 2);
lean_inc(x_1012);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1013 = lean_apply_5(x_1012, x_14, x_15, x_16, x_17, x_977);
if (lean_obj_tag(x_1013) == 0)
{
lean_object* x_1014; uint8_t x_1015; 
x_1014 = lean_ctor_get(x_1013, 0);
lean_inc(x_1014);
x_1015 = lean_ctor_get_uint8(x_1014, sizeof(void*)*1);
lean_dec(x_1014);
if (x_1015 == 0)
{
lean_object* x_1016; 
x_1016 = lean_ctor_get(x_1013, 1);
lean_inc(x_1016);
lean_dec(x_1013);
x_1002 = x_969;
x_1003 = x_1016;
goto block_1010;
}
else
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; uint8_t x_1022; 
x_1017 = lean_ctor_get(x_1013, 1);
lean_inc(x_1017);
lean_dec(x_1013);
x_1018 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_1019 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1018, x_14, x_15, x_16, x_17, x_1017);
x_1020 = lean_ctor_get(x_1019, 0);
lean_inc(x_1020);
x_1021 = lean_ctor_get(x_1019, 1);
lean_inc(x_1021);
lean_dec(x_1019);
x_1022 = lean_unbox(x_1020);
lean_dec(x_1020);
x_1002 = x_1022;
x_1003 = x_1021;
goto block_1010;
}
}
else
{
uint8_t x_1023; 
lean_dec(x_981);
lean_dec(x_979);
lean_dec(x_978);
lean_dec(x_973);
lean_dec(x_965);
lean_dec(x_935);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1023 = !lean_is_exclusive(x_1013);
if (x_1023 == 0)
{
return x_1013;
}
else
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
x_1024 = lean_ctor_get(x_1013, 0);
x_1025 = lean_ctor_get(x_1013, 1);
lean_inc(x_1025);
lean_inc(x_1024);
lean_dec(x_1013);
x_1026 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1026, 0, x_1024);
lean_ctor_set(x_1026, 1, x_1025);
return x_1026;
}
}
block_1001:
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; 
x_983 = x_973;
x_984 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_946, x_983);
x_985 = x_984;
lean_inc(x_978);
x_986 = l_Lean_mkFVar(x_978);
lean_inc(x_979);
x_987 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_987, 0, x_979);
x_988 = lean_box(x_955);
lean_inc(x_979);
x_989 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___lambda__1___boxed), 19, 13);
lean_closure_set(x_989, 0, x_978);
lean_closure_set(x_989, 1, x_9);
lean_closure_set(x_989, 2, x_979);
lean_closure_set(x_989, 3, x_3);
lean_closure_set(x_989, 4, x_4);
lean_closure_set(x_989, 5, x_7);
lean_closure_set(x_989, 6, x_8);
lean_closure_set(x_989, 7, x_935);
lean_closure_set(x_989, 8, x_988);
lean_closure_set(x_989, 9, x_965);
lean_closure_set(x_989, 10, x_981);
lean_closure_set(x_989, 11, x_985);
lean_closure_set(x_989, 12, x_986);
x_990 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_990, 0, x_987);
lean_closure_set(x_990, 1, x_989);
x_991 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_979, x_14, x_15, x_16, x_17, x_982);
if (lean_obj_tag(x_991) == 0)
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; 
x_992 = lean_ctor_get(x_991, 0);
lean_inc(x_992);
x_993 = lean_ctor_get(x_991, 1);
lean_inc(x_993);
lean_dec(x_991);
x_994 = lean_ctor_get(x_992, 1);
lean_inc(x_994);
x_995 = lean_ctor_get(x_992, 4);
lean_inc(x_995);
lean_dec(x_992);
x_996 = l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(x_994, x_995, x_990, x_14, x_15, x_16, x_17, x_993);
return x_996;
}
else
{
uint8_t x_997; 
lean_dec(x_990);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_997 = !lean_is_exclusive(x_991);
if (x_997 == 0)
{
return x_991;
}
else
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
x_998 = lean_ctor_get(x_991, 0);
x_999 = lean_ctor_get(x_991, 1);
lean_inc(x_999);
lean_inc(x_998);
lean_dec(x_991);
x_1000 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1000, 0, x_998);
lean_ctor_set(x_1000, 1, x_999);
return x_1000;
}
}
}
block_1010:
{
if (x_1002 == 0)
{
x_982 = x_1003;
goto block_1001;
}
else
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; 
lean_inc(x_979);
x_1004 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1004, 0, x_979);
x_1005 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5;
x_1006 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1006, 0, x_1005);
lean_ctor_set(x_1006, 1, x_1004);
x_1007 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_1008 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1007, x_1006, x_14, x_15, x_16, x_17, x_1003);
x_1009 = lean_ctor_get(x_1008, 1);
lean_inc(x_1009);
lean_dec(x_1008);
x_982 = x_1009;
goto block_1001;
}
}
}
else
{
uint8_t x_1027; 
lean_dec(x_973);
lean_dec(x_965);
lean_dec(x_950);
lean_dec(x_935);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1027 = !lean_is_exclusive(x_975);
if (x_1027 == 0)
{
return x_975;
}
else
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; 
x_1028 = lean_ctor_get(x_975, 0);
x_1029 = lean_ctor_get(x_975, 1);
lean_inc(x_1029);
lean_inc(x_1028);
lean_dec(x_975);
x_1030 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1030, 0, x_1028);
lean_ctor_set(x_1030, 1, x_1029);
return x_1030;
}
}
}
else
{
uint8_t x_1031; 
lean_dec(x_965);
lean_dec(x_950);
lean_dec(x_935);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1031 = !lean_is_exclusive(x_970);
if (x_1031 == 0)
{
return x_970;
}
else
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
x_1032 = lean_ctor_get(x_970, 0);
x_1033 = lean_ctor_get(x_970, 1);
lean_inc(x_1033);
lean_inc(x_1032);
lean_dec(x_970);
x_1034 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1034, 0, x_1032);
lean_ctor_set(x_1034, 1, x_1033);
return x_1034;
}
}
}
else
{
uint8_t x_1035; 
lean_dec(x_950);
lean_dec(x_935);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1035 = !lean_is_exclusive(x_962);
if (x_1035 == 0)
{
return x_962;
}
else
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
x_1036 = lean_ctor_get(x_962, 0);
x_1037 = lean_ctor_get(x_962, 1);
lean_inc(x_1037);
lean_inc(x_1036);
lean_dec(x_962);
x_1038 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1038, 0, x_1036);
lean_ctor_set(x_1038, 1, x_1037);
return x_1038;
}
}
}
}
else
{
uint8_t x_1053; 
lean_dec(x_950);
lean_dec(x_939);
lean_dec(x_935);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1053 = !lean_is_exclusive(x_952);
if (x_1053 == 0)
{
return x_952;
}
else
{
lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
x_1054 = lean_ctor_get(x_952, 0);
x_1055 = lean_ctor_get(x_952, 1);
lean_inc(x_1055);
lean_inc(x_1054);
lean_dec(x_952);
x_1056 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1056, 0, x_1054);
lean_ctor_set(x_1056, 1, x_1055);
return x_1056;
}
}
}
else
{
uint8_t x_1057; 
lean_dec(x_939);
lean_dec(x_935);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1057 = !lean_is_exclusive(x_949);
if (x_1057 == 0)
{
return x_949;
}
else
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
x_1058 = lean_ctor_get(x_949, 0);
x_1059 = lean_ctor_get(x_949, 1);
lean_inc(x_1059);
lean_inc(x_1058);
lean_dec(x_949);
x_1060 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1060, 0, x_1058);
lean_ctor_set(x_1060, 1, x_1059);
return x_1060;
}
}
}
else
{
uint8_t x_1061; 
lean_dec(x_935);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1061 = !lean_is_exclusive(x_936);
if (x_1061 == 0)
{
return x_936;
}
else
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; 
x_1062 = lean_ctor_get(x_936, 0);
x_1063 = lean_ctor_get(x_936, 1);
lean_inc(x_1063);
lean_inc(x_1062);
lean_dec(x_936);
x_1064 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1064, 0, x_1062);
lean_ctor_set(x_1064, 1, x_1063);
return x_1064;
}
}
}
case 9:
{
lean_object* x_1065; lean_object* x_1066; 
lean_dec(x_13);
lean_dec(x_11);
x_1065 = lean_ctor_get(x_8, 5);
lean_inc(x_1065);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_1066 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_7, x_10, x_12, x_1065, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_1066) == 0)
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
x_1067 = lean_ctor_get(x_1066, 1);
lean_inc(x_1067);
lean_dec(x_1066);
x_1068 = l_Lean_getMCtx___at_Lean_getMVarDecl___spec__1___rarg(x_15, x_16, x_17, x_1067);
x_1069 = lean_ctor_get(x_1068, 0);
lean_inc(x_1069);
x_1070 = lean_ctor_get(x_1068, 1);
lean_inc(x_1070);
lean_dec(x_1068);
x_1071 = lean_ctor_get(x_8, 6);
lean_inc(x_1071);
x_1072 = l_List_redLength___main___rarg(x_1071);
x_1073 = lean_mk_empty_array_with_capacity(x_1072);
lean_dec(x_1072);
lean_inc(x_1071);
x_1074 = l_List_toArrayAux___main___rarg(x_1071, x_1073);
x_1075 = x_1074;
x_1076 = lean_unsigned_to_nat(0u);
lean_inc(x_1069);
lean_inc(x_7);
lean_inc(x_1);
x_1077 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_1077, 0, x_1);
lean_closure_set(x_1077, 1, x_7);
lean_closure_set(x_1077, 2, x_10);
lean_closure_set(x_1077, 3, x_12);
lean_closure_set(x_1077, 4, x_1069);
lean_closure_set(x_1077, 5, x_1071);
lean_closure_set(x_1077, 6, x_1076);
lean_closure_set(x_1077, 7, x_1075);
x_1078 = x_1077;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1079 = lean_apply_5(x_1078, x_14, x_15, x_16, x_17, x_1070);
if (lean_obj_tag(x_1079) == 0)
{
lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; 
x_1080 = lean_ctor_get(x_1079, 0);
lean_inc(x_1080);
x_1081 = lean_ctor_get(x_1079, 1);
lean_inc(x_1081);
lean_dec(x_1079);
lean_inc(x_1);
x_1082 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_1081);
if (lean_obj_tag(x_1082) == 0)
{
lean_object* x_1083; lean_object* x_1084; uint8_t x_1085; lean_object* x_1086; 
x_1083 = lean_ctor_get(x_1082, 0);
lean_inc(x_1083);
x_1084 = lean_ctor_get(x_1082, 1);
lean_inc(x_1084);
lean_dec(x_1082);
x_1085 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_1085 == 0)
{
lean_object* x_1170; uint8_t x_1171; 
x_1170 = l_Lean_MetavarContext_exprDependsOn(x_1069, x_1083, x_2);
x_1171 = lean_unbox(x_1170);
lean_dec(x_1170);
if (x_1171 == 0)
{
x_1086 = x_1084;
goto block_1169;
}
else
{
lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; uint8_t x_1179; 
lean_dec(x_1080);
lean_dec(x_1065);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_1172 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1172, 0, x_3);
x_1173 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__6;
x_1174 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1174, 0, x_1173);
lean_ctor_set(x_1174, 1, x_1172);
x_1175 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8;
x_1176 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1176, 0, x_1174);
lean_ctor_set(x_1176, 1, x_1175);
x_1177 = lean_box(0);
x_1178 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_1176, x_1177, x_14, x_15, x_16, x_17, x_1084);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_1179 = !lean_is_exclusive(x_1178);
if (x_1179 == 0)
{
return x_1178;
}
else
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; 
x_1180 = lean_ctor_get(x_1178, 0);
x_1181 = lean_ctor_get(x_1178, 1);
lean_inc(x_1181);
lean_inc(x_1180);
lean_dec(x_1178);
x_1182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1182, 0, x_1180);
lean_ctor_set(x_1182, 1, x_1181);
return x_1182;
}
}
}
else
{
lean_dec(x_1083);
lean_dec(x_1069);
x_1086 = x_1084;
goto block_1169;
}
block_1169:
{
lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; uint8_t x_1091; lean_object* x_1092; 
lean_inc(x_1080);
x_1087 = x_1080;
x_1088 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1076, x_1087);
x_1089 = x_1088;
x_1090 = lean_array_push(x_1089, x_2);
x_1091 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1092 = l_Lean_Meta_revert(x_1, x_1090, x_1091, x_14, x_15, x_16, x_17, x_1086);
if (lean_obj_tag(x_1092) == 0)
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; uint8_t x_1099; lean_object* x_1100; 
x_1093 = lean_ctor_get(x_1092, 0);
lean_inc(x_1093);
x_1094 = lean_ctor_get(x_1092, 1);
lean_inc(x_1094);
lean_dec(x_1092);
x_1095 = lean_ctor_get(x_1093, 0);
lean_inc(x_1095);
x_1096 = lean_ctor_get(x_1093, 1);
lean_inc(x_1096);
lean_dec(x_1093);
x_1097 = lean_array_get_size(x_1080);
x_1098 = lean_box(0);
x_1099 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1100 = l_Lean_Meta_introN(x_1096, x_1097, x_1098, x_1099, x_14, x_15, x_16, x_17, x_1094);
if (lean_obj_tag(x_1100) == 0)
{
lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; 
x_1101 = lean_ctor_get(x_1100, 0);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1100, 1);
lean_inc(x_1102);
lean_dec(x_1100);
x_1103 = lean_ctor_get(x_1101, 0);
lean_inc(x_1103);
x_1104 = lean_ctor_get(x_1101, 1);
lean_inc(x_1104);
lean_dec(x_1101);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1105 = l_Lean_Meta_intro1(x_1104, x_1099, x_14, x_15, x_16, x_17, x_1102);
if (lean_obj_tag(x_1105) == 0)
{
lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; uint8_t x_1132; lean_object* x_1133; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
x_1106 = lean_ctor_get(x_1105, 0);
lean_inc(x_1106);
x_1107 = lean_ctor_get(x_1105, 1);
lean_inc(x_1107);
lean_dec(x_1105);
x_1108 = lean_ctor_get(x_1106, 0);
lean_inc(x_1108);
x_1109 = lean_ctor_get(x_1106, 1);
lean_inc(x_1109);
lean_dec(x_1106);
x_1110 = lean_box(0);
x_1111 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1080, x_1103, x_1080, x_1076, x_1110);
lean_dec(x_1080);
x_1141 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_1142 = lean_ctor_get(x_1141, 2);
lean_inc(x_1142);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1143 = lean_apply_5(x_1142, x_14, x_15, x_16, x_17, x_1107);
if (lean_obj_tag(x_1143) == 0)
{
lean_object* x_1144; uint8_t x_1145; 
x_1144 = lean_ctor_get(x_1143, 0);
lean_inc(x_1144);
x_1145 = lean_ctor_get_uint8(x_1144, sizeof(void*)*1);
lean_dec(x_1144);
if (x_1145 == 0)
{
lean_object* x_1146; 
x_1146 = lean_ctor_get(x_1143, 1);
lean_inc(x_1146);
lean_dec(x_1143);
x_1132 = x_1099;
x_1133 = x_1146;
goto block_1140;
}
else
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; uint8_t x_1152; 
x_1147 = lean_ctor_get(x_1143, 1);
lean_inc(x_1147);
lean_dec(x_1143);
x_1148 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_1149 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1148, x_14, x_15, x_16, x_17, x_1147);
x_1150 = lean_ctor_get(x_1149, 0);
lean_inc(x_1150);
x_1151 = lean_ctor_get(x_1149, 1);
lean_inc(x_1151);
lean_dec(x_1149);
x_1152 = lean_unbox(x_1150);
lean_dec(x_1150);
x_1132 = x_1152;
x_1133 = x_1151;
goto block_1140;
}
}
else
{
uint8_t x_1153; 
lean_dec(x_1111);
lean_dec(x_1109);
lean_dec(x_1108);
lean_dec(x_1103);
lean_dec(x_1095);
lean_dec(x_1065);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1153 = !lean_is_exclusive(x_1143);
if (x_1153 == 0)
{
return x_1143;
}
else
{
lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; 
x_1154 = lean_ctor_get(x_1143, 0);
x_1155 = lean_ctor_get(x_1143, 1);
lean_inc(x_1155);
lean_inc(x_1154);
lean_dec(x_1143);
x_1156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1156, 0, x_1154);
lean_ctor_set(x_1156, 1, x_1155);
return x_1156;
}
}
block_1131:
{
lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; 
x_1113 = x_1103;
x_1114 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1076, x_1113);
x_1115 = x_1114;
lean_inc(x_1108);
x_1116 = l_Lean_mkFVar(x_1108);
lean_inc(x_1109);
x_1117 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1117, 0, x_1109);
x_1118 = lean_box(x_1085);
lean_inc(x_1109);
x_1119 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___lambda__1___boxed), 19, 13);
lean_closure_set(x_1119, 0, x_1108);
lean_closure_set(x_1119, 1, x_9);
lean_closure_set(x_1119, 2, x_1109);
lean_closure_set(x_1119, 3, x_3);
lean_closure_set(x_1119, 4, x_4);
lean_closure_set(x_1119, 5, x_7);
lean_closure_set(x_1119, 6, x_8);
lean_closure_set(x_1119, 7, x_1065);
lean_closure_set(x_1119, 8, x_1118);
lean_closure_set(x_1119, 9, x_1095);
lean_closure_set(x_1119, 10, x_1111);
lean_closure_set(x_1119, 11, x_1115);
lean_closure_set(x_1119, 12, x_1116);
x_1120 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_1120, 0, x_1117);
lean_closure_set(x_1120, 1, x_1119);
x_1121 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_1109, x_14, x_15, x_16, x_17, x_1112);
if (lean_obj_tag(x_1121) == 0)
{
lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; 
x_1122 = lean_ctor_get(x_1121, 0);
lean_inc(x_1122);
x_1123 = lean_ctor_get(x_1121, 1);
lean_inc(x_1123);
lean_dec(x_1121);
x_1124 = lean_ctor_get(x_1122, 1);
lean_inc(x_1124);
x_1125 = lean_ctor_get(x_1122, 4);
lean_inc(x_1125);
lean_dec(x_1122);
x_1126 = l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(x_1124, x_1125, x_1120, x_14, x_15, x_16, x_17, x_1123);
return x_1126;
}
else
{
uint8_t x_1127; 
lean_dec(x_1120);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_1127 = !lean_is_exclusive(x_1121);
if (x_1127 == 0)
{
return x_1121;
}
else
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; 
x_1128 = lean_ctor_get(x_1121, 0);
x_1129 = lean_ctor_get(x_1121, 1);
lean_inc(x_1129);
lean_inc(x_1128);
lean_dec(x_1121);
x_1130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1130, 0, x_1128);
lean_ctor_set(x_1130, 1, x_1129);
return x_1130;
}
}
}
block_1140:
{
if (x_1132 == 0)
{
x_1112 = x_1133;
goto block_1131;
}
else
{
lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; 
lean_inc(x_1109);
x_1134 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1134, 0, x_1109);
x_1135 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5;
x_1136 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1136, 0, x_1135);
lean_ctor_set(x_1136, 1, x_1134);
x_1137 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_1138 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1137, x_1136, x_14, x_15, x_16, x_17, x_1133);
x_1139 = lean_ctor_get(x_1138, 1);
lean_inc(x_1139);
lean_dec(x_1138);
x_1112 = x_1139;
goto block_1131;
}
}
}
else
{
uint8_t x_1157; 
lean_dec(x_1103);
lean_dec(x_1095);
lean_dec(x_1080);
lean_dec(x_1065);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1157 = !lean_is_exclusive(x_1105);
if (x_1157 == 0)
{
return x_1105;
}
else
{
lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; 
x_1158 = lean_ctor_get(x_1105, 0);
x_1159 = lean_ctor_get(x_1105, 1);
lean_inc(x_1159);
lean_inc(x_1158);
lean_dec(x_1105);
x_1160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1160, 0, x_1158);
lean_ctor_set(x_1160, 1, x_1159);
return x_1160;
}
}
}
else
{
uint8_t x_1161; 
lean_dec(x_1095);
lean_dec(x_1080);
lean_dec(x_1065);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1161 = !lean_is_exclusive(x_1100);
if (x_1161 == 0)
{
return x_1100;
}
else
{
lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
x_1162 = lean_ctor_get(x_1100, 0);
x_1163 = lean_ctor_get(x_1100, 1);
lean_inc(x_1163);
lean_inc(x_1162);
lean_dec(x_1100);
x_1164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1164, 0, x_1162);
lean_ctor_set(x_1164, 1, x_1163);
return x_1164;
}
}
}
else
{
uint8_t x_1165; 
lean_dec(x_1080);
lean_dec(x_1065);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1165 = !lean_is_exclusive(x_1092);
if (x_1165 == 0)
{
return x_1092;
}
else
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; 
x_1166 = lean_ctor_get(x_1092, 0);
x_1167 = lean_ctor_get(x_1092, 1);
lean_inc(x_1167);
lean_inc(x_1166);
lean_dec(x_1092);
x_1168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1168, 0, x_1166);
lean_ctor_set(x_1168, 1, x_1167);
return x_1168;
}
}
}
}
else
{
uint8_t x_1183; 
lean_dec(x_1080);
lean_dec(x_1069);
lean_dec(x_1065);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1183 = !lean_is_exclusive(x_1082);
if (x_1183 == 0)
{
return x_1082;
}
else
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1184 = lean_ctor_get(x_1082, 0);
x_1185 = lean_ctor_get(x_1082, 1);
lean_inc(x_1185);
lean_inc(x_1184);
lean_dec(x_1082);
x_1186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1186, 0, x_1184);
lean_ctor_set(x_1186, 1, x_1185);
return x_1186;
}
}
}
else
{
uint8_t x_1187; 
lean_dec(x_1069);
lean_dec(x_1065);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1187 = !lean_is_exclusive(x_1079);
if (x_1187 == 0)
{
return x_1079;
}
else
{
lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; 
x_1188 = lean_ctor_get(x_1079, 0);
x_1189 = lean_ctor_get(x_1079, 1);
lean_inc(x_1189);
lean_inc(x_1188);
lean_dec(x_1079);
x_1190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1190, 0, x_1188);
lean_ctor_set(x_1190, 1, x_1189);
return x_1190;
}
}
}
else
{
uint8_t x_1191; 
lean_dec(x_1065);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1191 = !lean_is_exclusive(x_1066);
if (x_1191 == 0)
{
return x_1066;
}
else
{
lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; 
x_1192 = lean_ctor_get(x_1066, 0);
x_1193 = lean_ctor_get(x_1066, 1);
lean_inc(x_1193);
lean_inc(x_1192);
lean_dec(x_1066);
x_1194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1194, 0, x_1192);
lean_ctor_set(x_1194, 1, x_1193);
return x_1194;
}
}
}
case 10:
{
lean_object* x_1195; lean_object* x_1196; 
lean_dec(x_13);
lean_dec(x_11);
x_1195 = lean_ctor_get(x_8, 5);
lean_inc(x_1195);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_1196 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_7, x_10, x_12, x_1195, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_1196) == 0)
{
lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; 
x_1197 = lean_ctor_get(x_1196, 1);
lean_inc(x_1197);
lean_dec(x_1196);
x_1198 = l_Lean_getMCtx___at_Lean_getMVarDecl___spec__1___rarg(x_15, x_16, x_17, x_1197);
x_1199 = lean_ctor_get(x_1198, 0);
lean_inc(x_1199);
x_1200 = lean_ctor_get(x_1198, 1);
lean_inc(x_1200);
lean_dec(x_1198);
x_1201 = lean_ctor_get(x_8, 6);
lean_inc(x_1201);
x_1202 = l_List_redLength___main___rarg(x_1201);
x_1203 = lean_mk_empty_array_with_capacity(x_1202);
lean_dec(x_1202);
lean_inc(x_1201);
x_1204 = l_List_toArrayAux___main___rarg(x_1201, x_1203);
x_1205 = x_1204;
x_1206 = lean_unsigned_to_nat(0u);
lean_inc(x_1199);
lean_inc(x_7);
lean_inc(x_1);
x_1207 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_1207, 0, x_1);
lean_closure_set(x_1207, 1, x_7);
lean_closure_set(x_1207, 2, x_10);
lean_closure_set(x_1207, 3, x_12);
lean_closure_set(x_1207, 4, x_1199);
lean_closure_set(x_1207, 5, x_1201);
lean_closure_set(x_1207, 6, x_1206);
lean_closure_set(x_1207, 7, x_1205);
x_1208 = x_1207;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1209 = lean_apply_5(x_1208, x_14, x_15, x_16, x_17, x_1200);
if (lean_obj_tag(x_1209) == 0)
{
lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; 
x_1210 = lean_ctor_get(x_1209, 0);
lean_inc(x_1210);
x_1211 = lean_ctor_get(x_1209, 1);
lean_inc(x_1211);
lean_dec(x_1209);
lean_inc(x_1);
x_1212 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_1211);
if (lean_obj_tag(x_1212) == 0)
{
lean_object* x_1213; lean_object* x_1214; uint8_t x_1215; lean_object* x_1216; 
x_1213 = lean_ctor_get(x_1212, 0);
lean_inc(x_1213);
x_1214 = lean_ctor_get(x_1212, 1);
lean_inc(x_1214);
lean_dec(x_1212);
x_1215 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_1215 == 0)
{
lean_object* x_1300; uint8_t x_1301; 
x_1300 = l_Lean_MetavarContext_exprDependsOn(x_1199, x_1213, x_2);
x_1301 = lean_unbox(x_1300);
lean_dec(x_1300);
if (x_1301 == 0)
{
x_1216 = x_1214;
goto block_1299;
}
else
{
lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; uint8_t x_1309; 
lean_dec(x_1210);
lean_dec(x_1195);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_1302 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1302, 0, x_3);
x_1303 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__6;
x_1304 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1304, 0, x_1303);
lean_ctor_set(x_1304, 1, x_1302);
x_1305 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8;
x_1306 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1306, 0, x_1304);
lean_ctor_set(x_1306, 1, x_1305);
x_1307 = lean_box(0);
x_1308 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_1306, x_1307, x_14, x_15, x_16, x_17, x_1214);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_1309 = !lean_is_exclusive(x_1308);
if (x_1309 == 0)
{
return x_1308;
}
else
{
lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; 
x_1310 = lean_ctor_get(x_1308, 0);
x_1311 = lean_ctor_get(x_1308, 1);
lean_inc(x_1311);
lean_inc(x_1310);
lean_dec(x_1308);
x_1312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1312, 0, x_1310);
lean_ctor_set(x_1312, 1, x_1311);
return x_1312;
}
}
}
else
{
lean_dec(x_1213);
lean_dec(x_1199);
x_1216 = x_1214;
goto block_1299;
}
block_1299:
{
lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; uint8_t x_1221; lean_object* x_1222; 
lean_inc(x_1210);
x_1217 = x_1210;
x_1218 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1206, x_1217);
x_1219 = x_1218;
x_1220 = lean_array_push(x_1219, x_2);
x_1221 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1222 = l_Lean_Meta_revert(x_1, x_1220, x_1221, x_14, x_15, x_16, x_17, x_1216);
if (lean_obj_tag(x_1222) == 0)
{
lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; uint8_t x_1229; lean_object* x_1230; 
x_1223 = lean_ctor_get(x_1222, 0);
lean_inc(x_1223);
x_1224 = lean_ctor_get(x_1222, 1);
lean_inc(x_1224);
lean_dec(x_1222);
x_1225 = lean_ctor_get(x_1223, 0);
lean_inc(x_1225);
x_1226 = lean_ctor_get(x_1223, 1);
lean_inc(x_1226);
lean_dec(x_1223);
x_1227 = lean_array_get_size(x_1210);
x_1228 = lean_box(0);
x_1229 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1230 = l_Lean_Meta_introN(x_1226, x_1227, x_1228, x_1229, x_14, x_15, x_16, x_17, x_1224);
if (lean_obj_tag(x_1230) == 0)
{
lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; 
x_1231 = lean_ctor_get(x_1230, 0);
lean_inc(x_1231);
x_1232 = lean_ctor_get(x_1230, 1);
lean_inc(x_1232);
lean_dec(x_1230);
x_1233 = lean_ctor_get(x_1231, 0);
lean_inc(x_1233);
x_1234 = lean_ctor_get(x_1231, 1);
lean_inc(x_1234);
lean_dec(x_1231);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1235 = l_Lean_Meta_intro1(x_1234, x_1229, x_14, x_15, x_16, x_17, x_1232);
if (lean_obj_tag(x_1235) == 0)
{
lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; uint8_t x_1262; lean_object* x_1263; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; 
x_1236 = lean_ctor_get(x_1235, 0);
lean_inc(x_1236);
x_1237 = lean_ctor_get(x_1235, 1);
lean_inc(x_1237);
lean_dec(x_1235);
x_1238 = lean_ctor_get(x_1236, 0);
lean_inc(x_1238);
x_1239 = lean_ctor_get(x_1236, 1);
lean_inc(x_1239);
lean_dec(x_1236);
x_1240 = lean_box(0);
x_1241 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1210, x_1233, x_1210, x_1206, x_1240);
lean_dec(x_1210);
x_1271 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_1272 = lean_ctor_get(x_1271, 2);
lean_inc(x_1272);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1273 = lean_apply_5(x_1272, x_14, x_15, x_16, x_17, x_1237);
if (lean_obj_tag(x_1273) == 0)
{
lean_object* x_1274; uint8_t x_1275; 
x_1274 = lean_ctor_get(x_1273, 0);
lean_inc(x_1274);
x_1275 = lean_ctor_get_uint8(x_1274, sizeof(void*)*1);
lean_dec(x_1274);
if (x_1275 == 0)
{
lean_object* x_1276; 
x_1276 = lean_ctor_get(x_1273, 1);
lean_inc(x_1276);
lean_dec(x_1273);
x_1262 = x_1229;
x_1263 = x_1276;
goto block_1270;
}
else
{
lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; uint8_t x_1282; 
x_1277 = lean_ctor_get(x_1273, 1);
lean_inc(x_1277);
lean_dec(x_1273);
x_1278 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_1279 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1278, x_14, x_15, x_16, x_17, x_1277);
x_1280 = lean_ctor_get(x_1279, 0);
lean_inc(x_1280);
x_1281 = lean_ctor_get(x_1279, 1);
lean_inc(x_1281);
lean_dec(x_1279);
x_1282 = lean_unbox(x_1280);
lean_dec(x_1280);
x_1262 = x_1282;
x_1263 = x_1281;
goto block_1270;
}
}
else
{
uint8_t x_1283; 
lean_dec(x_1241);
lean_dec(x_1239);
lean_dec(x_1238);
lean_dec(x_1233);
lean_dec(x_1225);
lean_dec(x_1195);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1283 = !lean_is_exclusive(x_1273);
if (x_1283 == 0)
{
return x_1273;
}
else
{
lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; 
x_1284 = lean_ctor_get(x_1273, 0);
x_1285 = lean_ctor_get(x_1273, 1);
lean_inc(x_1285);
lean_inc(x_1284);
lean_dec(x_1273);
x_1286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1286, 0, x_1284);
lean_ctor_set(x_1286, 1, x_1285);
return x_1286;
}
}
block_1261:
{
lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; 
x_1243 = x_1233;
x_1244 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1206, x_1243);
x_1245 = x_1244;
lean_inc(x_1238);
x_1246 = l_Lean_mkFVar(x_1238);
lean_inc(x_1239);
x_1247 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1247, 0, x_1239);
x_1248 = lean_box(x_1215);
lean_inc(x_1239);
x_1249 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___lambda__1___boxed), 19, 13);
lean_closure_set(x_1249, 0, x_1238);
lean_closure_set(x_1249, 1, x_9);
lean_closure_set(x_1249, 2, x_1239);
lean_closure_set(x_1249, 3, x_3);
lean_closure_set(x_1249, 4, x_4);
lean_closure_set(x_1249, 5, x_7);
lean_closure_set(x_1249, 6, x_8);
lean_closure_set(x_1249, 7, x_1195);
lean_closure_set(x_1249, 8, x_1248);
lean_closure_set(x_1249, 9, x_1225);
lean_closure_set(x_1249, 10, x_1241);
lean_closure_set(x_1249, 11, x_1245);
lean_closure_set(x_1249, 12, x_1246);
x_1250 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_1250, 0, x_1247);
lean_closure_set(x_1250, 1, x_1249);
x_1251 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_1239, x_14, x_15, x_16, x_17, x_1242);
if (lean_obj_tag(x_1251) == 0)
{
lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; 
x_1252 = lean_ctor_get(x_1251, 0);
lean_inc(x_1252);
x_1253 = lean_ctor_get(x_1251, 1);
lean_inc(x_1253);
lean_dec(x_1251);
x_1254 = lean_ctor_get(x_1252, 1);
lean_inc(x_1254);
x_1255 = lean_ctor_get(x_1252, 4);
lean_inc(x_1255);
lean_dec(x_1252);
x_1256 = l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(x_1254, x_1255, x_1250, x_14, x_15, x_16, x_17, x_1253);
return x_1256;
}
else
{
uint8_t x_1257; 
lean_dec(x_1250);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_1257 = !lean_is_exclusive(x_1251);
if (x_1257 == 0)
{
return x_1251;
}
else
{
lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; 
x_1258 = lean_ctor_get(x_1251, 0);
x_1259 = lean_ctor_get(x_1251, 1);
lean_inc(x_1259);
lean_inc(x_1258);
lean_dec(x_1251);
x_1260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1260, 0, x_1258);
lean_ctor_set(x_1260, 1, x_1259);
return x_1260;
}
}
}
block_1270:
{
if (x_1262 == 0)
{
x_1242 = x_1263;
goto block_1261;
}
else
{
lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; 
lean_inc(x_1239);
x_1264 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1264, 0, x_1239);
x_1265 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5;
x_1266 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1266, 0, x_1265);
lean_ctor_set(x_1266, 1, x_1264);
x_1267 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_1268 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1267, x_1266, x_14, x_15, x_16, x_17, x_1263);
x_1269 = lean_ctor_get(x_1268, 1);
lean_inc(x_1269);
lean_dec(x_1268);
x_1242 = x_1269;
goto block_1261;
}
}
}
else
{
uint8_t x_1287; 
lean_dec(x_1233);
lean_dec(x_1225);
lean_dec(x_1210);
lean_dec(x_1195);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1287 = !lean_is_exclusive(x_1235);
if (x_1287 == 0)
{
return x_1235;
}
else
{
lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; 
x_1288 = lean_ctor_get(x_1235, 0);
x_1289 = lean_ctor_get(x_1235, 1);
lean_inc(x_1289);
lean_inc(x_1288);
lean_dec(x_1235);
x_1290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1290, 0, x_1288);
lean_ctor_set(x_1290, 1, x_1289);
return x_1290;
}
}
}
else
{
uint8_t x_1291; 
lean_dec(x_1225);
lean_dec(x_1210);
lean_dec(x_1195);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1291 = !lean_is_exclusive(x_1230);
if (x_1291 == 0)
{
return x_1230;
}
else
{
lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; 
x_1292 = lean_ctor_get(x_1230, 0);
x_1293 = lean_ctor_get(x_1230, 1);
lean_inc(x_1293);
lean_inc(x_1292);
lean_dec(x_1230);
x_1294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1294, 0, x_1292);
lean_ctor_set(x_1294, 1, x_1293);
return x_1294;
}
}
}
else
{
uint8_t x_1295; 
lean_dec(x_1210);
lean_dec(x_1195);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1295 = !lean_is_exclusive(x_1222);
if (x_1295 == 0)
{
return x_1222;
}
else
{
lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; 
x_1296 = lean_ctor_get(x_1222, 0);
x_1297 = lean_ctor_get(x_1222, 1);
lean_inc(x_1297);
lean_inc(x_1296);
lean_dec(x_1222);
x_1298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1298, 0, x_1296);
lean_ctor_set(x_1298, 1, x_1297);
return x_1298;
}
}
}
}
else
{
uint8_t x_1313; 
lean_dec(x_1210);
lean_dec(x_1199);
lean_dec(x_1195);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1313 = !lean_is_exclusive(x_1212);
if (x_1313 == 0)
{
return x_1212;
}
else
{
lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; 
x_1314 = lean_ctor_get(x_1212, 0);
x_1315 = lean_ctor_get(x_1212, 1);
lean_inc(x_1315);
lean_inc(x_1314);
lean_dec(x_1212);
x_1316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1316, 0, x_1314);
lean_ctor_set(x_1316, 1, x_1315);
return x_1316;
}
}
}
else
{
uint8_t x_1317; 
lean_dec(x_1199);
lean_dec(x_1195);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1317 = !lean_is_exclusive(x_1209);
if (x_1317 == 0)
{
return x_1209;
}
else
{
lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; 
x_1318 = lean_ctor_get(x_1209, 0);
x_1319 = lean_ctor_get(x_1209, 1);
lean_inc(x_1319);
lean_inc(x_1318);
lean_dec(x_1209);
x_1320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1320, 0, x_1318);
lean_ctor_set(x_1320, 1, x_1319);
return x_1320;
}
}
}
else
{
uint8_t x_1321; 
lean_dec(x_1195);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1321 = !lean_is_exclusive(x_1196);
if (x_1321 == 0)
{
return x_1196;
}
else
{
lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; 
x_1322 = lean_ctor_get(x_1196, 0);
x_1323 = lean_ctor_get(x_1196, 1);
lean_inc(x_1323);
lean_inc(x_1322);
lean_dec(x_1196);
x_1324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1324, 0, x_1322);
lean_ctor_set(x_1324, 1, x_1323);
return x_1324;
}
}
}
case 11:
{
lean_object* x_1325; lean_object* x_1326; 
lean_dec(x_13);
lean_dec(x_11);
x_1325 = lean_ctor_get(x_8, 5);
lean_inc(x_1325);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_1326 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_7, x_10, x_12, x_1325, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_1326) == 0)
{
lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; 
x_1327 = lean_ctor_get(x_1326, 1);
lean_inc(x_1327);
lean_dec(x_1326);
x_1328 = l_Lean_getMCtx___at_Lean_getMVarDecl___spec__1___rarg(x_15, x_16, x_17, x_1327);
x_1329 = lean_ctor_get(x_1328, 0);
lean_inc(x_1329);
x_1330 = lean_ctor_get(x_1328, 1);
lean_inc(x_1330);
lean_dec(x_1328);
x_1331 = lean_ctor_get(x_8, 6);
lean_inc(x_1331);
x_1332 = l_List_redLength___main___rarg(x_1331);
x_1333 = lean_mk_empty_array_with_capacity(x_1332);
lean_dec(x_1332);
lean_inc(x_1331);
x_1334 = l_List_toArrayAux___main___rarg(x_1331, x_1333);
x_1335 = x_1334;
x_1336 = lean_unsigned_to_nat(0u);
lean_inc(x_1329);
lean_inc(x_7);
lean_inc(x_1);
x_1337 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_1337, 0, x_1);
lean_closure_set(x_1337, 1, x_7);
lean_closure_set(x_1337, 2, x_10);
lean_closure_set(x_1337, 3, x_12);
lean_closure_set(x_1337, 4, x_1329);
lean_closure_set(x_1337, 5, x_1331);
lean_closure_set(x_1337, 6, x_1336);
lean_closure_set(x_1337, 7, x_1335);
x_1338 = x_1337;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1339 = lean_apply_5(x_1338, x_14, x_15, x_16, x_17, x_1330);
if (lean_obj_tag(x_1339) == 0)
{
lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; 
x_1340 = lean_ctor_get(x_1339, 0);
lean_inc(x_1340);
x_1341 = lean_ctor_get(x_1339, 1);
lean_inc(x_1341);
lean_dec(x_1339);
lean_inc(x_1);
x_1342 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_1341);
if (lean_obj_tag(x_1342) == 0)
{
lean_object* x_1343; lean_object* x_1344; uint8_t x_1345; lean_object* x_1346; 
x_1343 = lean_ctor_get(x_1342, 0);
lean_inc(x_1343);
x_1344 = lean_ctor_get(x_1342, 1);
lean_inc(x_1344);
lean_dec(x_1342);
x_1345 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_1345 == 0)
{
lean_object* x_1430; uint8_t x_1431; 
x_1430 = l_Lean_MetavarContext_exprDependsOn(x_1329, x_1343, x_2);
x_1431 = lean_unbox(x_1430);
lean_dec(x_1430);
if (x_1431 == 0)
{
x_1346 = x_1344;
goto block_1429;
}
else
{
lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; uint8_t x_1439; 
lean_dec(x_1340);
lean_dec(x_1325);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_1432 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1432, 0, x_3);
x_1433 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__6;
x_1434 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1434, 0, x_1433);
lean_ctor_set(x_1434, 1, x_1432);
x_1435 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8;
x_1436 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1436, 0, x_1434);
lean_ctor_set(x_1436, 1, x_1435);
x_1437 = lean_box(0);
x_1438 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_1436, x_1437, x_14, x_15, x_16, x_17, x_1344);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_1439 = !lean_is_exclusive(x_1438);
if (x_1439 == 0)
{
return x_1438;
}
else
{
lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; 
x_1440 = lean_ctor_get(x_1438, 0);
x_1441 = lean_ctor_get(x_1438, 1);
lean_inc(x_1441);
lean_inc(x_1440);
lean_dec(x_1438);
x_1442 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1442, 0, x_1440);
lean_ctor_set(x_1442, 1, x_1441);
return x_1442;
}
}
}
else
{
lean_dec(x_1343);
lean_dec(x_1329);
x_1346 = x_1344;
goto block_1429;
}
block_1429:
{
lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; uint8_t x_1351; lean_object* x_1352; 
lean_inc(x_1340);
x_1347 = x_1340;
x_1348 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1336, x_1347);
x_1349 = x_1348;
x_1350 = lean_array_push(x_1349, x_2);
x_1351 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1352 = l_Lean_Meta_revert(x_1, x_1350, x_1351, x_14, x_15, x_16, x_17, x_1346);
if (lean_obj_tag(x_1352) == 0)
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; uint8_t x_1359; lean_object* x_1360; 
x_1353 = lean_ctor_get(x_1352, 0);
lean_inc(x_1353);
x_1354 = lean_ctor_get(x_1352, 1);
lean_inc(x_1354);
lean_dec(x_1352);
x_1355 = lean_ctor_get(x_1353, 0);
lean_inc(x_1355);
x_1356 = lean_ctor_get(x_1353, 1);
lean_inc(x_1356);
lean_dec(x_1353);
x_1357 = lean_array_get_size(x_1340);
x_1358 = lean_box(0);
x_1359 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1360 = l_Lean_Meta_introN(x_1356, x_1357, x_1358, x_1359, x_14, x_15, x_16, x_17, x_1354);
if (lean_obj_tag(x_1360) == 0)
{
lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; 
x_1361 = lean_ctor_get(x_1360, 0);
lean_inc(x_1361);
x_1362 = lean_ctor_get(x_1360, 1);
lean_inc(x_1362);
lean_dec(x_1360);
x_1363 = lean_ctor_get(x_1361, 0);
lean_inc(x_1363);
x_1364 = lean_ctor_get(x_1361, 1);
lean_inc(x_1364);
lean_dec(x_1361);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1365 = l_Lean_Meta_intro1(x_1364, x_1359, x_14, x_15, x_16, x_17, x_1362);
if (lean_obj_tag(x_1365) == 0)
{
lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; uint8_t x_1392; lean_object* x_1393; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
x_1366 = lean_ctor_get(x_1365, 0);
lean_inc(x_1366);
x_1367 = lean_ctor_get(x_1365, 1);
lean_inc(x_1367);
lean_dec(x_1365);
x_1368 = lean_ctor_get(x_1366, 0);
lean_inc(x_1368);
x_1369 = lean_ctor_get(x_1366, 1);
lean_inc(x_1369);
lean_dec(x_1366);
x_1370 = lean_box(0);
x_1371 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1340, x_1363, x_1340, x_1336, x_1370);
lean_dec(x_1340);
x_1401 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_1402 = lean_ctor_get(x_1401, 2);
lean_inc(x_1402);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1403 = lean_apply_5(x_1402, x_14, x_15, x_16, x_17, x_1367);
if (lean_obj_tag(x_1403) == 0)
{
lean_object* x_1404; uint8_t x_1405; 
x_1404 = lean_ctor_get(x_1403, 0);
lean_inc(x_1404);
x_1405 = lean_ctor_get_uint8(x_1404, sizeof(void*)*1);
lean_dec(x_1404);
if (x_1405 == 0)
{
lean_object* x_1406; 
x_1406 = lean_ctor_get(x_1403, 1);
lean_inc(x_1406);
lean_dec(x_1403);
x_1392 = x_1359;
x_1393 = x_1406;
goto block_1400;
}
else
{
lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; uint8_t x_1412; 
x_1407 = lean_ctor_get(x_1403, 1);
lean_inc(x_1407);
lean_dec(x_1403);
x_1408 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_1409 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1408, x_14, x_15, x_16, x_17, x_1407);
x_1410 = lean_ctor_get(x_1409, 0);
lean_inc(x_1410);
x_1411 = lean_ctor_get(x_1409, 1);
lean_inc(x_1411);
lean_dec(x_1409);
x_1412 = lean_unbox(x_1410);
lean_dec(x_1410);
x_1392 = x_1412;
x_1393 = x_1411;
goto block_1400;
}
}
else
{
uint8_t x_1413; 
lean_dec(x_1371);
lean_dec(x_1369);
lean_dec(x_1368);
lean_dec(x_1363);
lean_dec(x_1355);
lean_dec(x_1325);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1413 = !lean_is_exclusive(x_1403);
if (x_1413 == 0)
{
return x_1403;
}
else
{
lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; 
x_1414 = lean_ctor_get(x_1403, 0);
x_1415 = lean_ctor_get(x_1403, 1);
lean_inc(x_1415);
lean_inc(x_1414);
lean_dec(x_1403);
x_1416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1416, 0, x_1414);
lean_ctor_set(x_1416, 1, x_1415);
return x_1416;
}
}
block_1391:
{
lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; 
x_1373 = x_1363;
x_1374 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1336, x_1373);
x_1375 = x_1374;
lean_inc(x_1368);
x_1376 = l_Lean_mkFVar(x_1368);
lean_inc(x_1369);
x_1377 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1377, 0, x_1369);
x_1378 = lean_box(x_1345);
lean_inc(x_1369);
x_1379 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___lambda__1___boxed), 19, 13);
lean_closure_set(x_1379, 0, x_1368);
lean_closure_set(x_1379, 1, x_9);
lean_closure_set(x_1379, 2, x_1369);
lean_closure_set(x_1379, 3, x_3);
lean_closure_set(x_1379, 4, x_4);
lean_closure_set(x_1379, 5, x_7);
lean_closure_set(x_1379, 6, x_8);
lean_closure_set(x_1379, 7, x_1325);
lean_closure_set(x_1379, 8, x_1378);
lean_closure_set(x_1379, 9, x_1355);
lean_closure_set(x_1379, 10, x_1371);
lean_closure_set(x_1379, 11, x_1375);
lean_closure_set(x_1379, 12, x_1376);
x_1380 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_1380, 0, x_1377);
lean_closure_set(x_1380, 1, x_1379);
x_1381 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_1369, x_14, x_15, x_16, x_17, x_1372);
if (lean_obj_tag(x_1381) == 0)
{
lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; 
x_1382 = lean_ctor_get(x_1381, 0);
lean_inc(x_1382);
x_1383 = lean_ctor_get(x_1381, 1);
lean_inc(x_1383);
lean_dec(x_1381);
x_1384 = lean_ctor_get(x_1382, 1);
lean_inc(x_1384);
x_1385 = lean_ctor_get(x_1382, 4);
lean_inc(x_1385);
lean_dec(x_1382);
x_1386 = l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(x_1384, x_1385, x_1380, x_14, x_15, x_16, x_17, x_1383);
return x_1386;
}
else
{
uint8_t x_1387; 
lean_dec(x_1380);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_1387 = !lean_is_exclusive(x_1381);
if (x_1387 == 0)
{
return x_1381;
}
else
{
lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; 
x_1388 = lean_ctor_get(x_1381, 0);
x_1389 = lean_ctor_get(x_1381, 1);
lean_inc(x_1389);
lean_inc(x_1388);
lean_dec(x_1381);
x_1390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1390, 0, x_1388);
lean_ctor_set(x_1390, 1, x_1389);
return x_1390;
}
}
}
block_1400:
{
if (x_1392 == 0)
{
x_1372 = x_1393;
goto block_1391;
}
else
{
lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; 
lean_inc(x_1369);
x_1394 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1394, 0, x_1369);
x_1395 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5;
x_1396 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1396, 0, x_1395);
lean_ctor_set(x_1396, 1, x_1394);
x_1397 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_1398 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1397, x_1396, x_14, x_15, x_16, x_17, x_1393);
x_1399 = lean_ctor_get(x_1398, 1);
lean_inc(x_1399);
lean_dec(x_1398);
x_1372 = x_1399;
goto block_1391;
}
}
}
else
{
uint8_t x_1417; 
lean_dec(x_1363);
lean_dec(x_1355);
lean_dec(x_1340);
lean_dec(x_1325);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1417 = !lean_is_exclusive(x_1365);
if (x_1417 == 0)
{
return x_1365;
}
else
{
lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; 
x_1418 = lean_ctor_get(x_1365, 0);
x_1419 = lean_ctor_get(x_1365, 1);
lean_inc(x_1419);
lean_inc(x_1418);
lean_dec(x_1365);
x_1420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1420, 0, x_1418);
lean_ctor_set(x_1420, 1, x_1419);
return x_1420;
}
}
}
else
{
uint8_t x_1421; 
lean_dec(x_1355);
lean_dec(x_1340);
lean_dec(x_1325);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1421 = !lean_is_exclusive(x_1360);
if (x_1421 == 0)
{
return x_1360;
}
else
{
lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; 
x_1422 = lean_ctor_get(x_1360, 0);
x_1423 = lean_ctor_get(x_1360, 1);
lean_inc(x_1423);
lean_inc(x_1422);
lean_dec(x_1360);
x_1424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1424, 0, x_1422);
lean_ctor_set(x_1424, 1, x_1423);
return x_1424;
}
}
}
else
{
uint8_t x_1425; 
lean_dec(x_1340);
lean_dec(x_1325);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1425 = !lean_is_exclusive(x_1352);
if (x_1425 == 0)
{
return x_1352;
}
else
{
lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; 
x_1426 = lean_ctor_get(x_1352, 0);
x_1427 = lean_ctor_get(x_1352, 1);
lean_inc(x_1427);
lean_inc(x_1426);
lean_dec(x_1352);
x_1428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1428, 0, x_1426);
lean_ctor_set(x_1428, 1, x_1427);
return x_1428;
}
}
}
}
else
{
uint8_t x_1443; 
lean_dec(x_1340);
lean_dec(x_1329);
lean_dec(x_1325);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1443 = !lean_is_exclusive(x_1342);
if (x_1443 == 0)
{
return x_1342;
}
else
{
lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; 
x_1444 = lean_ctor_get(x_1342, 0);
x_1445 = lean_ctor_get(x_1342, 1);
lean_inc(x_1445);
lean_inc(x_1444);
lean_dec(x_1342);
x_1446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1446, 0, x_1444);
lean_ctor_set(x_1446, 1, x_1445);
return x_1446;
}
}
}
else
{
uint8_t x_1447; 
lean_dec(x_1329);
lean_dec(x_1325);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1447 = !lean_is_exclusive(x_1339);
if (x_1447 == 0)
{
return x_1339;
}
else
{
lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; 
x_1448 = lean_ctor_get(x_1339, 0);
x_1449 = lean_ctor_get(x_1339, 1);
lean_inc(x_1449);
lean_inc(x_1448);
lean_dec(x_1339);
x_1450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1450, 0, x_1448);
lean_ctor_set(x_1450, 1, x_1449);
return x_1450;
}
}
}
else
{
uint8_t x_1451; 
lean_dec(x_1325);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1451 = !lean_is_exclusive(x_1326);
if (x_1451 == 0)
{
return x_1326;
}
else
{
lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; 
x_1452 = lean_ctor_get(x_1326, 0);
x_1453 = lean_ctor_get(x_1326, 1);
lean_inc(x_1453);
lean_inc(x_1452);
lean_dec(x_1326);
x_1454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1454, 0, x_1452);
lean_ctor_set(x_1454, 1, x_1453);
return x_1454;
}
}
}
default: 
{
lean_object* x_1455; lean_object* x_1456; 
lean_dec(x_13);
lean_dec(x_11);
x_1455 = lean_ctor_get(x_8, 5);
lean_inc(x_1455);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_1456 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_7, x_10, x_12, x_1455, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_1456) == 0)
{
lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; 
x_1457 = lean_ctor_get(x_1456, 1);
lean_inc(x_1457);
lean_dec(x_1456);
x_1458 = l_Lean_getMCtx___at_Lean_getMVarDecl___spec__1___rarg(x_15, x_16, x_17, x_1457);
x_1459 = lean_ctor_get(x_1458, 0);
lean_inc(x_1459);
x_1460 = lean_ctor_get(x_1458, 1);
lean_inc(x_1460);
lean_dec(x_1458);
x_1461 = lean_ctor_get(x_8, 6);
lean_inc(x_1461);
x_1462 = l_List_redLength___main___rarg(x_1461);
x_1463 = lean_mk_empty_array_with_capacity(x_1462);
lean_dec(x_1462);
lean_inc(x_1461);
x_1464 = l_List_toArrayAux___main___rarg(x_1461, x_1463);
x_1465 = x_1464;
x_1466 = lean_unsigned_to_nat(0u);
lean_inc(x_1459);
lean_inc(x_7);
lean_inc(x_1);
x_1467 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_1467, 0, x_1);
lean_closure_set(x_1467, 1, x_7);
lean_closure_set(x_1467, 2, x_10);
lean_closure_set(x_1467, 3, x_12);
lean_closure_set(x_1467, 4, x_1459);
lean_closure_set(x_1467, 5, x_1461);
lean_closure_set(x_1467, 6, x_1466);
lean_closure_set(x_1467, 7, x_1465);
x_1468 = x_1467;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1469 = lean_apply_5(x_1468, x_14, x_15, x_16, x_17, x_1460);
if (lean_obj_tag(x_1469) == 0)
{
lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; 
x_1470 = lean_ctor_get(x_1469, 0);
lean_inc(x_1470);
x_1471 = lean_ctor_get(x_1469, 1);
lean_inc(x_1471);
lean_dec(x_1469);
lean_inc(x_1);
x_1472 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_1471);
if (lean_obj_tag(x_1472) == 0)
{
lean_object* x_1473; lean_object* x_1474; uint8_t x_1475; lean_object* x_1476; 
x_1473 = lean_ctor_get(x_1472, 0);
lean_inc(x_1473);
x_1474 = lean_ctor_get(x_1472, 1);
lean_inc(x_1474);
lean_dec(x_1472);
x_1475 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_1475 == 0)
{
lean_object* x_1560; uint8_t x_1561; 
x_1560 = l_Lean_MetavarContext_exprDependsOn(x_1459, x_1473, x_2);
x_1561 = lean_unbox(x_1560);
lean_dec(x_1560);
if (x_1561 == 0)
{
x_1476 = x_1474;
goto block_1559;
}
else
{
lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; uint8_t x_1569; 
lean_dec(x_1470);
lean_dec(x_1455);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_1562 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1562, 0, x_3);
x_1563 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__6;
x_1564 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1564, 0, x_1563);
lean_ctor_set(x_1564, 1, x_1562);
x_1565 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8;
x_1566 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1566, 0, x_1564);
lean_ctor_set(x_1566, 1, x_1565);
x_1567 = lean_box(0);
x_1568 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_1566, x_1567, x_14, x_15, x_16, x_17, x_1474);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_1569 = !lean_is_exclusive(x_1568);
if (x_1569 == 0)
{
return x_1568;
}
else
{
lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; 
x_1570 = lean_ctor_get(x_1568, 0);
x_1571 = lean_ctor_get(x_1568, 1);
lean_inc(x_1571);
lean_inc(x_1570);
lean_dec(x_1568);
x_1572 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1572, 0, x_1570);
lean_ctor_set(x_1572, 1, x_1571);
return x_1572;
}
}
}
else
{
lean_dec(x_1473);
lean_dec(x_1459);
x_1476 = x_1474;
goto block_1559;
}
block_1559:
{
lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; uint8_t x_1481; lean_object* x_1482; 
lean_inc(x_1470);
x_1477 = x_1470;
x_1478 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1466, x_1477);
x_1479 = x_1478;
x_1480 = lean_array_push(x_1479, x_2);
x_1481 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1482 = l_Lean_Meta_revert(x_1, x_1480, x_1481, x_14, x_15, x_16, x_17, x_1476);
if (lean_obj_tag(x_1482) == 0)
{
lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; uint8_t x_1489; lean_object* x_1490; 
x_1483 = lean_ctor_get(x_1482, 0);
lean_inc(x_1483);
x_1484 = lean_ctor_get(x_1482, 1);
lean_inc(x_1484);
lean_dec(x_1482);
x_1485 = lean_ctor_get(x_1483, 0);
lean_inc(x_1485);
x_1486 = lean_ctor_get(x_1483, 1);
lean_inc(x_1486);
lean_dec(x_1483);
x_1487 = lean_array_get_size(x_1470);
x_1488 = lean_box(0);
x_1489 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1490 = l_Lean_Meta_introN(x_1486, x_1487, x_1488, x_1489, x_14, x_15, x_16, x_17, x_1484);
if (lean_obj_tag(x_1490) == 0)
{
lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; 
x_1491 = lean_ctor_get(x_1490, 0);
lean_inc(x_1491);
x_1492 = lean_ctor_get(x_1490, 1);
lean_inc(x_1492);
lean_dec(x_1490);
x_1493 = lean_ctor_get(x_1491, 0);
lean_inc(x_1493);
x_1494 = lean_ctor_get(x_1491, 1);
lean_inc(x_1494);
lean_dec(x_1491);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1495 = l_Lean_Meta_intro1(x_1494, x_1489, x_14, x_15, x_16, x_17, x_1492);
if (lean_obj_tag(x_1495) == 0)
{
lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; uint8_t x_1522; lean_object* x_1523; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; 
x_1496 = lean_ctor_get(x_1495, 0);
lean_inc(x_1496);
x_1497 = lean_ctor_get(x_1495, 1);
lean_inc(x_1497);
lean_dec(x_1495);
x_1498 = lean_ctor_get(x_1496, 0);
lean_inc(x_1498);
x_1499 = lean_ctor_get(x_1496, 1);
lean_inc(x_1499);
lean_dec(x_1496);
x_1500 = lean_box(0);
x_1501 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1470, x_1493, x_1470, x_1466, x_1500);
lean_dec(x_1470);
x_1531 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_1532 = lean_ctor_get(x_1531, 2);
lean_inc(x_1532);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1533 = lean_apply_5(x_1532, x_14, x_15, x_16, x_17, x_1497);
if (lean_obj_tag(x_1533) == 0)
{
lean_object* x_1534; uint8_t x_1535; 
x_1534 = lean_ctor_get(x_1533, 0);
lean_inc(x_1534);
x_1535 = lean_ctor_get_uint8(x_1534, sizeof(void*)*1);
lean_dec(x_1534);
if (x_1535 == 0)
{
lean_object* x_1536; 
x_1536 = lean_ctor_get(x_1533, 1);
lean_inc(x_1536);
lean_dec(x_1533);
x_1522 = x_1489;
x_1523 = x_1536;
goto block_1530;
}
else
{
lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; uint8_t x_1542; 
x_1537 = lean_ctor_get(x_1533, 1);
lean_inc(x_1537);
lean_dec(x_1533);
x_1538 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_1539 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1538, x_14, x_15, x_16, x_17, x_1537);
x_1540 = lean_ctor_get(x_1539, 0);
lean_inc(x_1540);
x_1541 = lean_ctor_get(x_1539, 1);
lean_inc(x_1541);
lean_dec(x_1539);
x_1542 = lean_unbox(x_1540);
lean_dec(x_1540);
x_1522 = x_1542;
x_1523 = x_1541;
goto block_1530;
}
}
else
{
uint8_t x_1543; 
lean_dec(x_1501);
lean_dec(x_1499);
lean_dec(x_1498);
lean_dec(x_1493);
lean_dec(x_1485);
lean_dec(x_1455);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1543 = !lean_is_exclusive(x_1533);
if (x_1543 == 0)
{
return x_1533;
}
else
{
lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; 
x_1544 = lean_ctor_get(x_1533, 0);
x_1545 = lean_ctor_get(x_1533, 1);
lean_inc(x_1545);
lean_inc(x_1544);
lean_dec(x_1533);
x_1546 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1546, 0, x_1544);
lean_ctor_set(x_1546, 1, x_1545);
return x_1546;
}
}
block_1521:
{
lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; 
x_1503 = x_1493;
x_1504 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1466, x_1503);
x_1505 = x_1504;
lean_inc(x_1498);
x_1506 = l_Lean_mkFVar(x_1498);
lean_inc(x_1499);
x_1507 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1507, 0, x_1499);
x_1508 = lean_box(x_1475);
lean_inc(x_1499);
x_1509 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___lambda__1___boxed), 19, 13);
lean_closure_set(x_1509, 0, x_1498);
lean_closure_set(x_1509, 1, x_9);
lean_closure_set(x_1509, 2, x_1499);
lean_closure_set(x_1509, 3, x_3);
lean_closure_set(x_1509, 4, x_4);
lean_closure_set(x_1509, 5, x_7);
lean_closure_set(x_1509, 6, x_8);
lean_closure_set(x_1509, 7, x_1455);
lean_closure_set(x_1509, 8, x_1508);
lean_closure_set(x_1509, 9, x_1485);
lean_closure_set(x_1509, 10, x_1501);
lean_closure_set(x_1509, 11, x_1505);
lean_closure_set(x_1509, 12, x_1506);
x_1510 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_1510, 0, x_1507);
lean_closure_set(x_1510, 1, x_1509);
x_1511 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_1499, x_14, x_15, x_16, x_17, x_1502);
if (lean_obj_tag(x_1511) == 0)
{
lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; 
x_1512 = lean_ctor_get(x_1511, 0);
lean_inc(x_1512);
x_1513 = lean_ctor_get(x_1511, 1);
lean_inc(x_1513);
lean_dec(x_1511);
x_1514 = lean_ctor_get(x_1512, 1);
lean_inc(x_1514);
x_1515 = lean_ctor_get(x_1512, 4);
lean_inc(x_1515);
lean_dec(x_1512);
x_1516 = l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(x_1514, x_1515, x_1510, x_14, x_15, x_16, x_17, x_1513);
return x_1516;
}
else
{
uint8_t x_1517; 
lean_dec(x_1510);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_1517 = !lean_is_exclusive(x_1511);
if (x_1517 == 0)
{
return x_1511;
}
else
{
lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; 
x_1518 = lean_ctor_get(x_1511, 0);
x_1519 = lean_ctor_get(x_1511, 1);
lean_inc(x_1519);
lean_inc(x_1518);
lean_dec(x_1511);
x_1520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1520, 0, x_1518);
lean_ctor_set(x_1520, 1, x_1519);
return x_1520;
}
}
}
block_1530:
{
if (x_1522 == 0)
{
x_1502 = x_1523;
goto block_1521;
}
else
{
lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; 
lean_inc(x_1499);
x_1524 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1524, 0, x_1499);
x_1525 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5;
x_1526 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1526, 0, x_1525);
lean_ctor_set(x_1526, 1, x_1524);
x_1527 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_1528 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1527, x_1526, x_14, x_15, x_16, x_17, x_1523);
x_1529 = lean_ctor_get(x_1528, 1);
lean_inc(x_1529);
lean_dec(x_1528);
x_1502 = x_1529;
goto block_1521;
}
}
}
else
{
uint8_t x_1547; 
lean_dec(x_1493);
lean_dec(x_1485);
lean_dec(x_1470);
lean_dec(x_1455);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1547 = !lean_is_exclusive(x_1495);
if (x_1547 == 0)
{
return x_1495;
}
else
{
lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; 
x_1548 = lean_ctor_get(x_1495, 0);
x_1549 = lean_ctor_get(x_1495, 1);
lean_inc(x_1549);
lean_inc(x_1548);
lean_dec(x_1495);
x_1550 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1550, 0, x_1548);
lean_ctor_set(x_1550, 1, x_1549);
return x_1550;
}
}
}
else
{
uint8_t x_1551; 
lean_dec(x_1485);
lean_dec(x_1470);
lean_dec(x_1455);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1551 = !lean_is_exclusive(x_1490);
if (x_1551 == 0)
{
return x_1490;
}
else
{
lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; 
x_1552 = lean_ctor_get(x_1490, 0);
x_1553 = lean_ctor_get(x_1490, 1);
lean_inc(x_1553);
lean_inc(x_1552);
lean_dec(x_1490);
x_1554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1554, 0, x_1552);
lean_ctor_set(x_1554, 1, x_1553);
return x_1554;
}
}
}
else
{
uint8_t x_1555; 
lean_dec(x_1470);
lean_dec(x_1455);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1555 = !lean_is_exclusive(x_1482);
if (x_1555 == 0)
{
return x_1482;
}
else
{
lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; 
x_1556 = lean_ctor_get(x_1482, 0);
x_1557 = lean_ctor_get(x_1482, 1);
lean_inc(x_1557);
lean_inc(x_1556);
lean_dec(x_1482);
x_1558 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1558, 0, x_1556);
lean_ctor_set(x_1558, 1, x_1557);
return x_1558;
}
}
}
}
else
{
uint8_t x_1573; 
lean_dec(x_1470);
lean_dec(x_1459);
lean_dec(x_1455);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1573 = !lean_is_exclusive(x_1472);
if (x_1573 == 0)
{
return x_1472;
}
else
{
lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; 
x_1574 = lean_ctor_get(x_1472, 0);
x_1575 = lean_ctor_get(x_1472, 1);
lean_inc(x_1575);
lean_inc(x_1574);
lean_dec(x_1472);
x_1576 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1576, 0, x_1574);
lean_ctor_set(x_1576, 1, x_1575);
return x_1576;
}
}
}
else
{
uint8_t x_1577; 
lean_dec(x_1459);
lean_dec(x_1455);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1577 = !lean_is_exclusive(x_1469);
if (x_1577 == 0)
{
return x_1469;
}
else
{
lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; 
x_1578 = lean_ctor_get(x_1469, 0);
x_1579 = lean_ctor_get(x_1469, 1);
lean_inc(x_1579);
lean_inc(x_1578);
lean_dec(x_1469);
x_1580 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1580, 0, x_1578);
lean_ctor_set(x_1580, 1, x_1579);
return x_1580;
}
}
}
else
{
uint8_t x_1581; 
lean_dec(x_1455);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1581 = !lean_is_exclusive(x_1456);
if (x_1581 == 0)
{
return x_1456;
}
else
{
lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; 
x_1582 = lean_ctor_get(x_1456, 0);
x_1583 = lean_ctor_get(x_1456, 1);
lean_inc(x_1583);
lean_inc(x_1582);
lean_dec(x_1456);
x_1584 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1584, 0, x_1582);
lean_ctor_set(x_1584, 1, x_1583);
return x_1584;
}
}
}
}
}
}
lean_object* l_Lean_Meta_induction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_1);
x_14 = l_Lean_getLocalDecl___at_Lean_getFVarLocalDecl___spec__1(x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_18 = l_Lean_Meta_mkRecursorInfo(x_2, x_17, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_LocalDecl_type(x_15);
lean_dec(x_15);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_21);
x_23 = l_Lean_whnfUntil___at_Lean_Meta_induction___spec__1(x_21, x_22, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(x_3, x_21, x_9, x_10, x_11, x_12, x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Lean_Expr_getAppNumArgsAux___main(x_28, x_29);
x_31 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_30);
x_32 = lean_mk_array(x_30, x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_sub(x_30, x_33);
lean_dec(x_30);
lean_inc(x_28);
x_35 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11(x_3, x_1, x_2, x_4, x_5, x_6, x_7, x_19, x_22, x_28, x_28, x_32, x_34, x_9, x_10, x_11, x_12, x_27);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
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
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
lean_object* l_Lean_Meta_induction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = l___private_Lean_Meta_Basic_12__forallTelescopeReducingAuxAux___main___rarg___closed__2;
x_14 = l___private_Lean_Meta_Basic_12__forallTelescopeReducingAuxAux___main___rarg___closed__3;
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_induction___lambda__1___boxed), 13, 7);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_3);
lean_closure_set(x_15, 2, x_1);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_13);
lean_closure_set(x_15, 5, x_14);
lean_closure_set(x_15, 6, x_11);
x_16 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_16, 0, x_12);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 4);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(x_20, x_21, x_16, x_6, x_7, x_8, x_9, x_19);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_induction___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_whnfUntil___at_Lean_Meta_induction___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_whnfUntil___at_Lean_Meta_induction___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_List_elem___main___at_Lean_Meta_induction___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___main___at_Lean_Meta_induction___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_16;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
return x_14;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_foldlM___main___at_Lean_Meta_induction___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; lean_object* x_23; 
x_22 = lean_unbox(x_6);
lean_dec(x_6);
x_23 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10(x_1, x_2, x_3, x_4, x_5, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_23;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___lambda__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_9);
lean_dec(x_9);
x_21 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_21;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
}
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_induction___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
lean_object* l_Lean_Meta_induction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_induction(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_7__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_RecursorInfo(lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Revert(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Induction(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_RecursorInfo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FVarSubst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8);
l_Lean_Meta_InductionSubgoal_inhabited___closed__1 = _init_l_Lean_Meta_InductionSubgoal_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_InductionSubgoal_inhabited___closed__1);
l_Lean_Meta_InductionSubgoal_inhabited = _init_l_Lean_Meta_InductionSubgoal_inhabited();
lean_mark_persistent(l_Lean_Meta_InductionSubgoal_inhabited);
l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1);
l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2);
l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3 = _init_l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3);
l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1 = _init_l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1();
lean_mark_persistent(l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1);
l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2 = _init_l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2();
lean_mark_persistent(l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2);
l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3 = _init_l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3();
lean_mark_persistent(l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__2 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__2();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__2);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__7 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__7();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__7);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__3 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__3);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__5 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__5();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__5);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__6 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__6();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__6);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__1 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__1);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__2 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__2);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__3 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__3);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__4 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__4);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__5 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__5);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__6 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__6);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__7 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__7();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__7);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__8 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__8();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__8);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__9 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__9();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__10___closed__9);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__2 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__2);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__4 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__4);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__7 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__7();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__7);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8);
res = l___private_Lean_Meta_Tactic_Induction_7__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
