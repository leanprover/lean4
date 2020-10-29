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
lean_object* l_Array_iterateMAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction_match__7___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_elem___at_Lean_Meta_induction___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPredImp___at_Lean_Meta_induction___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_Level_Lean_Level___instance__4;
lean_object* l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__3(lean_object*);
lean_object* l_List_foldlM___at_Lean_Meta_induction___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction_match__10(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__1;
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___at_Lean_Meta_induction___spec__10___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InductionSubgoal_fields___default;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_induction___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object**);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__4;
lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthInstanceImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__2;
lean_object* l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8;
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4;
lean_object* l_Lean_Meta_induction_match__8(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_2206_(lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__4;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__7;
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVarsImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___closed__2;
lean_object* l_List_forM___at_Lean_Meta_induction___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___closed__1;
lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__3;
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction_match__7(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction_match__9___rarg(lean_object*, lean_object*);
lean_object* l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__5;
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__4(lean_object*);
lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams_match__2(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__1;
lean_object* l_Lean_Meta_induction_match__5___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__2;
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Array_umapMAux___at_Lean_LocalContext_getFVars___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction_match__8___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___boxed(lean_object**);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__5___rarg(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__8;
lean_object* l_Lean_Meta_InductionSubgoal_subst___default;
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4;
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*);
lean_object* l_Array_iterateMAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction_match__6(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__2___boxed(lean_object**);
lean_object* l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__1___boxed(lean_object**);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__4;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction_match__6___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction_match__2___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__5(lean_object*);
lean_object* l_Lean_Meta_induction_match__11___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__6;
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___boxed(lean_object**);
lean_object* l_Lean_MetavarContext_localDeclDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_induction___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__3;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_Init_LeanInit___instance__1;
lean_object* l_Lean_Meta_Lean_Meta_Tactic_Induction___instance__1___closed__1;
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__3;
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_induction___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_Meta_whnfHeadPredImp___at_Lean_Meta_induction___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthInstanceImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity_match__1(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_umapMAux___at_Lean_Meta_induction___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__3;
lean_object* l_Lean_Meta_induction_match__2(lean_object*);
uint8_t l_List_elem___at_Lean_Meta_induction___spec__5(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at_Lean_Meta_induction___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__2(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__6(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Lean_Meta_induction_match__12___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Lean_Expr___instance__11;
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__6___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7;
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___lambda__2___boxed(lean_object**);
lean_object* l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction_match__3___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_revert___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2___closed__2;
lean_object* l_Lean_Meta_Lean_Meta_Tactic_Induction___instance__1;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_List_foldlM___at_Lean_Meta_induction___spec__10___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1___closed__1;
lean_object* l_List_forM___at_Lean_Meta_induction___spec__4___closed__1;
lean_object* l_Lean_Meta_induction_match__5(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction_match__10___rarg(lean_object*, lean_object*);
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction_match__4(lean_object*);
lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1___closed__2;
lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
lean_object* l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__3;
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__4___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_induction___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__2;
lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_Meta_induction___spec__4___closed__2;
lean_object* l_Lean_Meta_induction_match__3(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_induction_match__12(lean_object*);
lean_object* l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__1;
lean_object* l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_Meta_induction___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6;
lean_object* l_Lean_Meta_induction_match__9(lean_object*);
lean_object* l_List_foldlM___at_Lean_Meta_induction___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__2;
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Util___hyg_225____closed__2;
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction_match__11(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__8___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_4(x_3, x_5, x_6, x_7, x_9);
return x_10;
}
case 10:
{
lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_14 = lean_box_uint64(x_13);
x_15 = lean_apply_3(x_2, x_11, x_12, x_14);
return x_15;
}
default: 
{
lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_apply_1(x_4, x_1);
return x_16;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
return x_5;
}
case 10:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_1 = x_6;
goto _start;
}
default: 
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isHeadBetaTarget(x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(0u);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Lean_Expr_headBeta(x_1);
x_1 = x_10;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_2);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_5, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_apply_3(x_4, x_11, x_10, x_2);
return x_12;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams_match__2___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_mkApp(x_1, x_5);
x_12 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("induction");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed recursor");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to generate type class instance parameter");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_13 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_4, x_5, x_6, x_7, x_8, x_9);
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
x_16 = l_Lean_Meta_whnfForall___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___spec__1(x_14, x_5, x_6, x_7, x_8, x_15);
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
x_20 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthInstanceImp(x_19, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___lambda__1(x_4, x_1, x_2, x_12, x_21, x_5, x_6, x_7, x_8, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_4);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_26 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8;
x_27 = lean_box(0);
x_28 = l_Lean_Meta_throwTacticEx___rarg(x_25, x_1, x_26, x_27, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_17);
lean_dec(x_4);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_dec(x_16);
x_34 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_35 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_36 = lean_box(0);
x_37 = l_Lean_Meta_throwTacticEx___rarg(x_34, x_1, x_35, x_36, x_5, x_6, x_7, x_8, x_33);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_37;
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
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
return x_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_13, 0);
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_13);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_3, 1);
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_array_get_size(x_2);
x_49 = lean_nat_dec_lt(x_47, x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_4);
x_50 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_51 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_52 = lean_box(0);
x_53 = l_Lean_Meta_throwTacticEx___rarg(x_50, x_1, x_51, x_52, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_array_fget(x_2, x_47);
x_55 = l_Lean_mkApp(x_4, x_54);
x_3 = x_46;
x_4 = x_55;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_InductionSubgoal_fields___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_InductionSubgoal_subst___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Lean_Meta_Tactic_Induction___instance__1___closed__1() {
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
static lean_object* _init_l_Lean_Meta_Lean_Meta_Tactic_Induction___instance__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Lean_Meta_Tactic_Induction___instance__1___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_whnfForall___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
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
x_20 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_21 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
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
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__4___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__5___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__5___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop_match__6___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
lean_dec(x_6);
x_12 = lean_nat_add(x_11, x_10);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_12);
x_14 = lean_nat_add(x_3, x_10);
x_15 = lean_nat_dec_lt(x_13, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = l_Lean_Init_LeanInit___instance__1;
x_17 = lean_array_get(x_16, x_1, x_13);
x_18 = lean_nat_sub(x_13, x_3);
lean_dec(x_13);
x_19 = lean_nat_sub(x_18, x_10);
lean_dec(x_18);
x_20 = lean_array_get(x_16, x_4, x_19);
lean_dec(x_19);
x_21 = l_Lean_mkFVar(x_20);
x_22 = l_Lean_Meta_FVarSubst_insert(x_7, x_17, x_21);
x_6 = x_11;
x_7 = x_22;
goto _start;
}
else
{
lean_dec(x_13);
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
lean_object* l_Lean_Meta_synthInstance_x3f___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthInstanceImp_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Array_iterateMAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_21 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_1, x_19, x_14, x_6, x_7, x_8, x_9, x_10);
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
x_32 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_1, x_30, x_14, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, uint8_t x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25) {
_start:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_26 = lean_nat_sub(x_1, x_2);
x_27 = lean_array_get_size(x_3);
x_28 = lean_array_get_size(x_4);
x_29 = lean_nat_sub(x_27, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_29, x_30);
lean_dec(x_29);
x_84 = lean_array_get_size(x_13);
x_85 = lean_nat_dec_lt(x_11, x_84);
lean_dec(x_84);
x_86 = l_Lean_Name_append(x_17, x_18);
lean_inc(x_21);
x_87 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_19, x_86, x_21, x_22, x_23, x_24, x_25);
if (x_85 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_box(0);
x_32 = x_90;
x_33 = x_88;
x_34 = x_89;
goto block_83;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
lean_dec(x_87);
x_93 = lean_array_fget(x_13, x_11);
x_32 = x_93;
x_33 = x_91;
x_34 = x_92;
goto block_83;
}
block_83:
{
lean_object* x_35; lean_object* x_36; 
lean_inc(x_33);
x_35 = l_Lean_mkApp(x_5, x_33);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_6);
x_36 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_6, x_7, x_33, x_21, x_22, x_23, x_24, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Expr_mvarId_x21(x_33);
lean_dec(x_33);
x_40 = l_Lean_Expr_fvarId_x21(x_8);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_41 = l_Lean_Meta_tryClear(x_39, x_40, x_21, x_22, x_23, x_24, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = 0;
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_45 = l_Lean_Meta_introNCore(x_42, x_26, x_32, x_44, x_21, x_22, x_23, x_24, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
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
x_50 = lean_box(0);
x_51 = 1;
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_52 = l_Lean_Meta_introNCore(x_49, x_31, x_50, x_51, x_21, x_22, x_23, x_24, x_47);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
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
lean_inc(x_9);
lean_inc(x_27);
x_57 = l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1(x_3, x_4, x_28, x_55, x_27, x_27, x_9);
lean_dec(x_27);
lean_dec(x_55);
lean_dec(x_28);
x_58 = x_48;
x_59 = lean_unsigned_to_nat(0u);
x_60 = l_Array_umapMAux___at_Lean_LocalContext_getFVars___spec__1(x_59, x_58);
x_61 = x_60;
x_62 = lean_nat_add(x_10, x_30);
x_63 = lean_nat_add(x_11, x_30);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_57);
x_65 = lean_array_push(x_12, x_64);
x_66 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(x_6, x_13, x_14, x_3, x_8, x_4, x_9, x_2, x_15, x_62, x_63, x_35, x_37, x_16, x_65, x_21, x_22, x_23, x_24, x_54);
lean_dec(x_63);
return x_66;
}
else
{
uint8_t x_67; 
lean_dec(x_48);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
return x_52;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_52, 0);
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_52);
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
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_71 = !lean_is_exclusive(x_45);
if (x_71 == 0)
{
return x_45;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_45, 0);
x_73 = lean_ctor_get(x_45, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_45);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_75 = !lean_is_exclusive(x_41);
if (x_75 == 0)
{
return x_41;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_41, 0);
x_77 = lean_ctor_get(x_41, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_41);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_79 = !lean_is_exclusive(x_36);
if (x_79 == 0)
{
return x_36;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_36, 0);
x_81 = lean_ctor_get(x_36, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_36);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.Tactic.Induction");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Meta.Tactic.Induction.0.Lean.Meta.finalize.loop");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__2;
x_3 = lean_unsigned_to_nat(111u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, uint8_t x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_23; lean_object* x_24; uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_41; uint8_t x_42; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_26 = l_Lean_Expr_headBeta(x_24);
x_41 = (uint8_t)((x_25 << 24) >> 61);
x_42 = l_Lean_BinderInfo_isInstImplicit(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_box(0);
x_27 = x_43;
goto block_40;
}
else
{
uint8_t x_44; 
x_44 = l_Array_isEmpty___rarg(x_12);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_box(0);
x_27 = x_45;
goto block_40;
}
else
{
lean_object* x_46; 
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_26);
x_46 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthInstanceImp_x3f(x_26, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Name_append(x_16, x_23);
lean_inc(x_18);
x_50 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_26, x_49, x_18, x_19, x_20, x_21, x_48);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_51);
x_53 = l_Lean_mkApp(x_5, x_51);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_6);
x_54 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_6, x_1, x_51, x_18, x_19, x_20, x_21, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_9, x_57);
x_59 = lean_nat_add(x_10, x_57);
x_60 = l_Lean_Expr_mvarId_x21(x_51);
lean_dec(x_51);
x_61 = lean_box(0);
x_62 = l_Array_empty___closed__1;
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_61);
x_64 = lean_array_push(x_11, x_63);
x_65 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(x_6, x_12, x_13, x_3, x_7, x_4, x_8, x_2, x_14, x_58, x_59, x_53, x_55, x_15, x_64, x_18, x_19, x_20, x_21, x_56);
lean_dec(x_59);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_66 = !lean_is_exclusive(x_54);
if (x_66 == 0)
{
return x_54;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_54, 0);
x_68 = lean_ctor_get(x_54, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_54);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_26);
lean_dec(x_23);
x_70 = lean_ctor_get(x_46, 1);
lean_inc(x_70);
lean_dec(x_46);
x_71 = lean_ctor_get(x_47, 0);
lean_inc(x_71);
lean_dec(x_47);
lean_inc(x_71);
x_72 = l_Lean_mkApp(x_5, x_71);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_6);
x_73 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_6, x_1, x_71, x_18, x_19, x_20, x_21, x_70);
lean_dec(x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_nat_add(x_9, x_76);
x_78 = lean_nat_add(x_10, x_76);
x_79 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(x_6, x_12, x_13, x_3, x_7, x_4, x_8, x_2, x_14, x_77, x_78, x_72, x_74, x_15, x_11, x_18, x_19, x_20, x_21, x_75);
lean_dec(x_78);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_72);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_80 = !lean_is_exclusive(x_73);
if (x_80 == 0)
{
return x_73;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_73, 0);
x_82 = lean_ctor_get(x_73, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_73);
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
uint8_t x_84; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_46);
if (x_84 == 0)
{
return x_46;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_46, 0);
x_86 = lean_ctor_get(x_46, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_46);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
block_40:
{
lean_object* x_28; uint8_t x_29; 
lean_dec(x_27);
lean_inc(x_26);
x_28 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(x_26);
x_29 = lean_nat_dec_lt(x_28, x_2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
x_31 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__2(x_28, x_2, x_3, x_4, x_5, x_6, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_23, x_26, x_30, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_28);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_32 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_33 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_34 = lean_box(0);
x_35 = l_Lean_Meta_throwTacticEx___rarg(x_32, x_6, x_33, x_34, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
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
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_88 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_89 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__3;
x_90 = lean_panic_fn(x_88, x_89);
x_91 = lean_apply_5(x_90, x_18, x_19, x_20, x_21, x_22);
return x_91;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_21 = l_Lean_Meta_whnfForall___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___spec__1(x_13, x_16, x_17, x_18, x_19, x_20);
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
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
if (x_14 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_12);
x_25 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_26 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
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
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1(x_1, x_12, x_15, x_33, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_34;
}
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_3, 3);
x_36 = lean_nat_dec_lt(x_10, x_35);
if (x_36 == 0)
{
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
if (x_14 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_15);
lean_dec(x_12);
x_37 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_38 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_39 = lean_box(0);
x_40 = l_Lean_Meta_throwTacticEx___rarg(x_37, x_1, x_38, x_39, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_box(0);
x_46 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1(x_1, x_12, x_15, x_45, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_46;
}
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = l_Lean_Meta_RecursorInfo_firstIndexPos(x_3);
x_48 = lean_nat_dec_eq(x_10, x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_inc(x_1);
x_49 = l_Lean_Meta_getMVarTag(x_1, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_nat_dec_le(x_9, x_11);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_box(0);
x_54 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3(x_22, x_8, x_4, x_6, x_12, x_1, x_5, x_7, x_10, x_11, x_15, x_2, x_3, x_9, x_14, x_50, x_53, x_16, x_17, x_18, x_19, x_51);
lean_dec(x_50);
lean_dec(x_10);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_50);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
x_55 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_56 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_57 = lean_box(0);
x_58 = l_Lean_Meta_throwTacticEx___rarg(x_55, x_1, x_56, x_57, x_16, x_17, x_18, x_19, x_51);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_49);
if (x_63 == 0)
{
return x_49;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_49, 0);
x_65 = lean_ctor_get(x_49, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_49);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_12);
lean_ctor_set(x_67, 1, x_22);
x_68 = lean_unsigned_to_nat(0u);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_69 = l_Array_iterateMAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__3(x_1, x_6, x_6, x_68, x_67, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
lean_inc(x_5);
x_74 = l_Lean_mkApp(x_72, x_5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_75 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTypeBody(x_1, x_73, x_5, x_16, x_17, x_18, x_19, x_71);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_add(x_10, x_78);
lean_dec(x_10);
x_80 = lean_array_get_size(x_6);
x_81 = lean_nat_add(x_79, x_80);
lean_dec(x_80);
lean_dec(x_79);
x_82 = 1;
x_10 = x_81;
x_12 = x_74;
x_13 = x_76;
x_14 = x_82;
x_20 = x_77;
goto _start;
}
else
{
uint8_t x_84; 
lean_dec(x_74);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_75);
if (x_84 == 0)
{
return x_75;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_75, 0);
x_86 = lean_ctor_get(x_75, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_75);
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
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_69);
if (x_88 == 0)
{
return x_69;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_69, 0);
x_90 = lean_ctor_get(x_69, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_69);
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
else
{
uint8_t x_92; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_21);
if (x_92 == 0)
{
return x_21;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_21, 0);
x_94 = lean_ctor_get(x_21, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_21);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
lean_object* l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateMAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_iterateMAux___at___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__2___boxed(lean_object** _args) {
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
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
_start:
{
uint8_t x_26; lean_object* x_27; 
x_26 = lean_unbox(x_16);
lean_dec(x_16);
x_27 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_26, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_27;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___boxed(lean_object** _args) {
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
lean_object* x_22 = _args[21];
_start:
{
uint8_t x_23; lean_object* x_24; 
x_23 = lean_unbox(x_15);
lean_dec(x_15);
x_24 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_23, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_24;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___boxed(lean_object** _args) {
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
x_22 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_21, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_17 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_getTargetArity(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_8, x_9, x_10, x_11, x_12, x_16);
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
x_23 = l_List_lengthAux___rarg(x_21, x_22);
x_24 = lean_ctor_get(x_3, 5);
x_25 = l_List_lengthAux___rarg(x_24, x_22);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_25, x_26);
lean_dec(x_25);
x_28 = 0;
x_29 = l_Array_empty___closed__1;
x_30 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_23, x_27, x_22, x_8, x_19, x_28, x_29, x_9, x_10, x_11, x_12, x_20);
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
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected major premise type");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_indentExpr(x_2);
x_9 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__2;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
x_14 = lean_box(0);
x_15 = l_Lean_Meta_throwTacticEx___rarg(x_13, x_1, x_12, x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_induction_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_induction_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_induction_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_induction_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_induction_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_induction_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_induction_match__3___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_induction_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_induction_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_induction_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_induction_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_induction_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_induction_match__5___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_induction_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_induction_match__5___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_induction_match__6___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_induction_match__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_induction_match__6___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_induction_match__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Meta_induction_match__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_induction_match__7___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_induction_match__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_induction_match__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_induction_match__8___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_induction_match__9___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_induction_match__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_induction_match__9___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_induction_match__10___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_induction_match__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_induction_match__10___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_induction_match__11___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_induction_match__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_induction_match__11___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_induction_match__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_induction_match__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_induction_match__12___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_induction___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_9 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__3;
x_10 = lean_panic_fn(x_8, x_9);
x_11 = lean_apply_5(x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_inc(x_3);
lean_inc(x_12);
x_13 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_14, 4);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_14, sizeof(void*)*5);
lean_dec(x_14);
x_22 = l_Lean_Meta_getConfig___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__3(x_3, x_4, x_5, x_6, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_23, 6);
if (x_24 == 0)
{
if (x_21 == 0)
{
uint8_t x_25; 
lean_dec(x_2);
x_25 = lean_ctor_get_uint8(x_23, 7);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_12);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_2 = x_20;
x_7 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_st_ref_take(x_4, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_30, 2);
x_34 = lean_box(0);
x_35 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_33, x_12, x_34);
lean_ctor_set(x_30, 2, x_35);
x_36 = lean_st_ref_set(x_4, x_30, x_31);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_2 = x_20;
x_7 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
x_41 = lean_ctor_get(x_30, 2);
x_42 = lean_ctor_get(x_30, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
x_43 = lean_box(0);
x_44 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_41, x_12, x_43);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_42);
x_46 = lean_st_ref_set(x_4, x_45, x_31);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_2 = x_20;
x_7 = x_47;
goto _start;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_22);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_22, 0);
lean_dec(x_50);
lean_ctor_set(x_22, 0, x_2);
return x_22;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_22, 1);
lean_inc(x_51);
lean_dec(x_22);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_2);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_2);
x_53 = lean_ctor_get_uint8(x_23, 7);
lean_dec(x_23);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_12);
x_54 = lean_ctor_get(x_22, 1);
lean_inc(x_54);
lean_dec(x_22);
x_2 = x_20;
x_7 = x_54;
goto _start;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
lean_dec(x_22);
x_57 = lean_st_ref_take(x_4, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_58, 2);
x_62 = lean_box(0);
x_63 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_61, x_12, x_62);
lean_ctor_set(x_58, 2, x_63);
x_64 = lean_st_ref_set(x_4, x_58, x_59);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_2 = x_20;
x_7 = x_65;
goto _start;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_58, 0);
x_68 = lean_ctor_get(x_58, 1);
x_69 = lean_ctor_get(x_58, 2);
x_70 = lean_ctor_get(x_58, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_58);
x_71 = lean_box(0);
x_72 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_69, x_12, x_71);
x_73 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_68);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_73, 3, x_70);
x_74 = lean_st_ref_set(x_4, x_73, x_59);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_2 = x_20;
x_7 = x_75;
goto _start;
}
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_13);
if (x_77 == 0)
{
return x_13;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_13, 0);
x_79 = lean_ctor_get(x_13, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_13);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
case 2:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_2, 0);
lean_inc(x_81);
x_82 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___spec__1(x_81, x_3, x_4, x_5, x_6, x_7);
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
lean_ctor_set(x_82, 0, x_2);
return x_82;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_2);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_2);
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
case 4:
{
lean_object* x_91; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_91 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_ctor_get(x_91, 1);
x_95 = l_Lean_Expr_isAppOf(x_93, x_1);
if (x_95 == 0)
{
lean_object* x_96; 
lean_free_object(x_91);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_93);
x_96 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_93, x_3, x_4, x_5, x_6, x_94);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_98 = !lean_is_exclusive(x_96);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_96, 0);
lean_dec(x_99);
lean_ctor_set(x_96, 0, x_93);
return x_96;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_93);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_93);
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
lean_dec(x_96);
x_103 = lean_ctor_get(x_97, 0);
lean_inc(x_103);
lean_dec(x_97);
x_2 = x_103;
x_7 = x_102;
goto _start;
}
}
else
{
uint8_t x_105; 
lean_dec(x_93);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_105 = !lean_is_exclusive(x_96);
if (x_105 == 0)
{
return x_96;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_96, 0);
x_107 = lean_ctor_get(x_96, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_96);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_91;
}
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_ctor_get(x_91, 0);
x_110 = lean_ctor_get(x_91, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_91);
x_111 = l_Lean_Expr_isAppOf(x_109, x_1);
if (x_111 == 0)
{
lean_object* x_112; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_109);
x_112 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_109, x_3, x_4, x_5, x_6, x_110);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_115 = x_112;
} else {
 lean_dec_ref(x_112);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_109);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_109);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
lean_dec(x_112);
x_118 = lean_ctor_get(x_113, 0);
lean_inc(x_118);
lean_dec(x_113);
x_2 = x_118;
x_7 = x_117;
goto _start;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_109);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_120 = lean_ctor_get(x_112, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_112, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_122 = x_112;
} else {
 lean_dec_ref(x_112);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
lean_object* x_124; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_109);
lean_ctor_set(x_124, 1, x_110);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_125 = !lean_is_exclusive(x_91);
if (x_125 == 0)
{
return x_91;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_91, 0);
x_127 = lean_ctor_get(x_91, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_91);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
case 5:
{
lean_object* x_129; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_129 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = lean_ctor_get(x_129, 0);
x_132 = lean_ctor_get(x_129, 1);
x_133 = l_Lean_Expr_isAppOf(x_131, x_1);
if (x_133 == 0)
{
lean_object* x_134; 
lean_free_object(x_129);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_131);
x_134 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_131, x_3, x_4, x_5, x_6, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_136 = !lean_is_exclusive(x_134);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_134, 0);
lean_dec(x_137);
lean_ctor_set(x_134, 0, x_131);
return x_134;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
lean_dec(x_134);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_131);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_131);
x_140 = lean_ctor_get(x_134, 1);
lean_inc(x_140);
lean_dec(x_134);
x_141 = lean_ctor_get(x_135, 0);
lean_inc(x_141);
lean_dec(x_135);
x_2 = x_141;
x_7 = x_140;
goto _start;
}
}
else
{
uint8_t x_143; 
lean_dec(x_131);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_143 = !lean_is_exclusive(x_134);
if (x_143 == 0)
{
return x_134;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_134, 0);
x_145 = lean_ctor_get(x_134, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_134);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_129;
}
}
else
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = lean_ctor_get(x_129, 0);
x_148 = lean_ctor_get(x_129, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_129);
x_149 = l_Lean_Expr_isAppOf(x_147, x_1);
if (x_149 == 0)
{
lean_object* x_150; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_147);
x_150 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_147, x_3, x_4, x_5, x_6, x_148);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_147);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_147);
x_155 = lean_ctor_get(x_150, 1);
lean_inc(x_155);
lean_dec(x_150);
x_156 = lean_ctor_get(x_151, 0);
lean_inc(x_156);
lean_dec(x_151);
x_2 = x_156;
x_7 = x_155;
goto _start;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_147);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_158 = lean_ctor_get(x_150, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_150, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_160 = x_150;
} else {
 lean_dec_ref(x_150);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
else
{
lean_object* x_162; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_147);
lean_ctor_set(x_162, 1, x_148);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_163 = !lean_is_exclusive(x_129);
if (x_163 == 0)
{
return x_129;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_129, 0);
x_165 = lean_ctor_get(x_129, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_129);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
case 8:
{
lean_object* x_167; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_167 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_167) == 0)
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_167, 0);
x_170 = lean_ctor_get(x_167, 1);
x_171 = l_Lean_Expr_isAppOf(x_169, x_1);
if (x_171 == 0)
{
lean_object* x_172; 
lean_free_object(x_167);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_169);
x_172 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_169, x_3, x_4, x_5, x_6, x_170);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_174 = !lean_is_exclusive(x_172);
if (x_174 == 0)
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_172, 0);
lean_dec(x_175);
lean_ctor_set(x_172, 0, x_169);
return x_172;
}
else
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
lean_dec(x_172);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_169);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_169);
x_178 = lean_ctor_get(x_172, 1);
lean_inc(x_178);
lean_dec(x_172);
x_179 = lean_ctor_get(x_173, 0);
lean_inc(x_179);
lean_dec(x_173);
x_2 = x_179;
x_7 = x_178;
goto _start;
}
}
else
{
uint8_t x_181; 
lean_dec(x_169);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_181 = !lean_is_exclusive(x_172);
if (x_181 == 0)
{
return x_172;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_172, 0);
x_183 = lean_ctor_get(x_172, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_172);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_167;
}
}
else
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = lean_ctor_get(x_167, 0);
x_186 = lean_ctor_get(x_167, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_167);
x_187 = l_Lean_Expr_isAppOf(x_185, x_1);
if (x_187 == 0)
{
lean_object* x_188; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_185);
x_188 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_185, x_3, x_4, x_5, x_6, x_186);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_191 = x_188;
} else {
 lean_dec_ref(x_188);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_185);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_185);
x_193 = lean_ctor_get(x_188, 1);
lean_inc(x_193);
lean_dec(x_188);
x_194 = lean_ctor_get(x_189, 0);
lean_inc(x_194);
lean_dec(x_189);
x_2 = x_194;
x_7 = x_193;
goto _start;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_185);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_196 = lean_ctor_get(x_188, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_188, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_198 = x_188;
} else {
 lean_dec_ref(x_188);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
else
{
lean_object* x_200; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_185);
lean_ctor_set(x_200, 1, x_186);
return x_200;
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_201 = !lean_is_exclusive(x_167);
if (x_201 == 0)
{
return x_167;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_167, 0);
x_203 = lean_ctor_get(x_167, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_167);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
case 10:
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_2, 1);
lean_inc(x_205);
lean_dec(x_2);
x_2 = x_205;
goto _start;
}
case 11:
{
lean_object* x_207; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_207 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_207) == 0)
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_209 = lean_ctor_get(x_207, 0);
x_210 = lean_ctor_get(x_207, 1);
x_211 = l_Lean_Expr_isAppOf(x_209, x_1);
if (x_211 == 0)
{
lean_object* x_212; 
lean_free_object(x_207);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_209);
x_212 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_209, x_3, x_4, x_5, x_6, x_210);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
if (lean_obj_tag(x_213) == 0)
{
uint8_t x_214; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_214 = !lean_is_exclusive(x_212);
if (x_214 == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_212, 0);
lean_dec(x_215);
lean_ctor_set(x_212, 0, x_209);
return x_212;
}
else
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_212, 1);
lean_inc(x_216);
lean_dec(x_212);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_209);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_209);
x_218 = lean_ctor_get(x_212, 1);
lean_inc(x_218);
lean_dec(x_212);
x_219 = lean_ctor_get(x_213, 0);
lean_inc(x_219);
lean_dec(x_213);
x_2 = x_219;
x_7 = x_218;
goto _start;
}
}
else
{
uint8_t x_221; 
lean_dec(x_209);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_221 = !lean_is_exclusive(x_212);
if (x_221 == 0)
{
return x_212;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_212, 0);
x_223 = lean_ctor_get(x_212, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_212);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_207;
}
}
else
{
lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_225 = lean_ctor_get(x_207, 0);
x_226 = lean_ctor_get(x_207, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_207);
x_227 = l_Lean_Expr_isAppOf(x_225, x_1);
if (x_227 == 0)
{
lean_object* x_228; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_225);
x_228 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_225, x_3, x_4, x_5, x_6, x_226);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_231 = x_228;
} else {
 lean_dec_ref(x_228);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_225);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_225);
x_233 = lean_ctor_get(x_228, 1);
lean_inc(x_233);
lean_dec(x_228);
x_234 = lean_ctor_get(x_229, 0);
lean_inc(x_234);
lean_dec(x_229);
x_2 = x_234;
x_7 = x_233;
goto _start;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_225);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_236 = lean_ctor_get(x_228, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_228, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_238 = x_228;
} else {
 lean_dec_ref(x_228);
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
lean_object* x_240; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_225);
lean_ctor_set(x_240, 1, x_226);
return x_240;
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_241 = !lean_is_exclusive(x_207);
if (x_241 == 0)
{
return x_207;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_207, 0);
x_243 = lean_ctor_get(x_207, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_207);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
case 12:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_2);
x_245 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_246 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__4;
x_247 = lean_panic_fn(x_245, x_246);
x_248 = lean_apply_5(x_247, x_3, x_4, x_5, x_6, x_7);
return x_248;
}
default: 
{
lean_object* x_249; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_2);
lean_ctor_set(x_249, 1, x_7);
return x_249;
}
}
}
}
lean_object* l_Lean_Meta_whnfHeadPredImp___at_Lean_Meta_induction___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_induction___spec__3(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
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
static lean_object* _init_l_List_forM___at_Lean_Meta_induction___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise type is ill-formed");
return x_1;
}
}
static lean_object* _init_l_List_forM___at_Lean_Meta_induction___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___at_Lean_Meta_induction___spec__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_List_forM___at_Lean_Meta_induction___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = l_Lean_indentExpr(x_3);
x_22 = l_List_forM___at_Lean_Meta_induction___spec__4___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_25, x_26, x_6, x_7, x_8, x_9, x_10);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
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
uint8_t l_List_elem___at_Lean_Meta_induction___spec__5(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is an index in major premise, but it depends on index occurring at position #");
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_1, x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = l_List_elem___at_Lean_Meta_induction___spec__5(x_2, x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = l_Lean_Expr_isFVar(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_14);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Expr_fvarId_x21(x_5);
lean_inc(x_10);
x_25 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_24, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = l_Lean_Expr_fvarId_x21(x_4);
x_30 = l_Lean_MetavarContext_localDeclDependsOn(x_6, x_27, x_29);
lean_dec(x_29);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_32 = lean_box(0);
lean_ctor_set(x_25, 0, x_32);
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_free_object(x_25);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_5);
x_34 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1___closed__2;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_2, x_38);
x_40 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_box(0);
x_46 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_44, x_45, x_10, x_11, x_12, x_13, x_28);
lean_dec(x_10);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_25, 0);
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_25);
x_49 = l_Lean_Expr_fvarId_x21(x_4);
x_50 = l_Lean_MetavarContext_localDeclDependsOn(x_6, x_47, x_49);
lean_dec(x_49);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_5);
x_55 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1___closed__2;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_2, x_59);
x_61 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_60);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_box(0);
x_67 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_65, x_66, x_10, x_11, x_12, x_13, x_48);
lean_dec(x_10);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_68 = !lean_is_exclusive(x_25);
if (x_68 == 0)
{
return x_25;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_25, 0);
x_70 = lean_ctor_get(x_25, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_25);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is an index in major premise, but it occurs in previous arguments");
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_nat_dec_lt(x_2, x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
x_17 = lean_box(0);
x_18 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_Expr_fvarId_x21(x_5);
lean_inc(x_4);
lean_inc(x_6);
x_20 = l_Lean_MetavarContext_exprDependsOn(x_6, x_4, x_19);
lean_dec(x_19);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
x_22 = lean_box(0);
x_23 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_6);
lean_dec(x_4);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_5);
x_25 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_indentExpr(x_9);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_box(0);
x_34 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_8, x_32, x_33, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_11);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is an index in major premise, but it occurs more than once");
return x_1;
}
}
static lean_object* _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_10, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_10, x_18);
lean_dec(x_10);
x_20 = lean_nat_sub(x_9, x_19);
x_21 = lean_nat_sub(x_20, x_18);
lean_dec(x_20);
x_22 = l_Lean_Expr_Lean_Expr___instance__11;
x_23 = lean_array_get(x_22, x_4, x_21);
x_24 = lean_nat_dec_eq(x_21, x_7);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_expr_eqv(x_23, x_8);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
lean_inc(x_11);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_8);
x_27 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2(x_7, x_21, x_6, x_23, x_8, x_5, x_2, x_1, x_3, x_26, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_10 = x_19;
x_15 = x_28;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_5);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_8);
x_35 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___closed__2;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_indentExpr(x_3);
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_box(0);
x_44 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_42, x_43, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_11);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_box(0);
lean_inc(x_11);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_8);
x_50 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2(x_7, x_21, x_6, x_23, x_8, x_5, x_2, x_1, x_3, x_49, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_21);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_10 = x_19;
x_15 = x_51;
goto _start;
}
else
{
uint8_t x_53; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_50);
if (x_53 == 0)
{
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_15);
return x_58;
}
}
}
lean_object* l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_get_size(x_1);
lean_inc(x_15);
lean_inc(x_8);
x_16 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__6(x_2, x_3, x_4, x_1, x_5, x_6, x_7, x_8, x_15, x_15, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_8);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_8);
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
static lean_object* _init_l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise type index ");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" is not variable");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Expr_Lean_Expr___instance__11;
x_15 = lean_array_get(x_14, x_1, x_2);
x_16 = l_Lean_Expr_isFVar(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_6);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_indentExpr(x_5);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = l_Lean_Meta_throwTacticEx___rarg(x_4, x_3, x_25, x_26, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(0);
x_33 = l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__1(x_1, x_3, x_4, x_5, x_6, x_7, x_2, x_15, x_32, x_9, x_10, x_11, x_12, x_13);
return x_33;
}
}
}
lean_object* l_Array_umapMAux___at_Lean_Meta_induction___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_8);
x_15 = lean_nat_dec_lt(x_7, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_array_fget(x_8, x_7);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_fset(x_8, x_7, x_19);
x_21 = x_18;
x_22 = lean_array_get_size(x_4);
x_23 = lean_nat_dec_le(x_22, x_21);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_25 = l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2(x_4, x_21, x_1, x_2, x_3, x_5, x_6, x_24, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_7, x_28);
x_30 = x_26;
x_31 = lean_array_fset(x_20, x_7, x_30);
lean_dec(x_7);
x_7 = x_29;
x_8 = x_31;
x_13 = x_27;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
return x_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
x_37 = l_Lean_indentExpr(x_3);
x_38 = l_List_forM___at_Lean_Meta_induction___spec__4___closed__2;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_box(0);
x_43 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_41, x_42, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
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
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_induction___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 < x_3;
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_2, x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
x_11 = l_Lean_Expr_fvarId_x21(x_7);
lean_dec(x_7);
x_12 = l_Lean_Init_LeanInit___instance__1;
x_13 = lean_array_get(x_12, x_1, x_10);
x_14 = l_Lean_mkFVar(x_13);
x_15 = l_Lean_Meta_FVarSubst_insert(x_9, x_11, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_10, x_16);
lean_dec(x_10);
lean_ctor_set(x_5, 1, x_17);
lean_ctor_set(x_5, 0, x_15);
x_18 = 1;
x_19 = x_4 + x_18;
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_5);
x_23 = l_Lean_Expr_fvarId_x21(x_7);
lean_dec(x_7);
x_24 = l_Lean_Init_LeanInit___instance__1;
x_25 = lean_array_get(x_24, x_1, x_22);
x_26 = l_Lean_mkFVar(x_25);
x_27 = l_Lean_Meta_FVarSubst_insert(x_21, x_23, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_22, x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = 1;
x_32 = x_4 + x_31;
x_4 = x_32;
x_5 = x_30;
goto _start;
}
}
}
}
lean_object* l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVarsImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Level_normalize(x_9);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = l_Lean_Level_normalize(x_11);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* l_List_foldlM___at_Lean_Meta_induction___spec__10___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_Level_Lean_Level___instance__4;
x_12 = lean_array_get(x_11, x_1, x_2);
x_13 = lean_array_push(x_3, x_12);
x_14 = lean_box(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
}
lean_object* l_List_foldlM___at_Lean_Meta_induction___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_6, 1);
x_30 = lean_ctor_get(x_5, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_array_get_size(x_4);
x_34 = lean_nat_dec_le(x_33, x_32);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_box(0);
x_36 = lean_unbox(x_31);
lean_dec(x_31);
x_37 = l_List_foldlM___at_Lean_Meta_induction___spec__10___lambda__1(x_4, x_32, x_30, x_36, x_35, x_7, x_8, x_9, x_10, x_11);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_5 = x_38;
x_6 = x_29;
x_11 = x_39;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_3);
x_41 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5;
x_42 = lean_box(0);
x_43 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_41, x_42, x_7, x_8, x_9, x_10, x_11);
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
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_10);
lean_inc(x_1);
x_15 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_1, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_mkApp(x_2, x_16);
x_19 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize(x_3, x_4, x_5, x_6, x_7, x_1, x_8, x_18, x_10, x_11, x_12, x_13, x_17);
lean_dec(x_1);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Array_toList___rarg(x_1);
x_20 = l_Lean_mkConst(x_2, x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_3);
x_21 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams(x_3, x_4, x_5, x_20, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___lambda__1(x_6, x_23, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_14, x_15, x_16, x_17, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_10);
x_29 = lean_array_push(x_28, x_10);
lean_inc(x_14);
x_30 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_29, x_12, x_14, x_15, x_16, x_17, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___lambda__1(x_6, x_26, x_3, x_7, x_8, x_9, x_10, x_11, x_31, x_14, x_15, x_16, x_17, x_32);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_30);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
return x_21;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_21, 0);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_21);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise is not of the form (C ...)");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_empty___closed__1;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("recursor '");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' can only eliminate into Prop");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
switch (lean_obj_tag(x_13)) {
case 4:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_15);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l_List_redLength___rarg(x_21);
x_23 = lean_mk_empty_array_with_capacity(x_22);
lean_dec(x_22);
x_24 = l_List_toArrayAux___rarg(x_21, x_23);
x_25 = lean_ctor_get(x_4, 2);
x_26 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__4;
lean_inc(x_12);
lean_inc(x_7);
lean_inc(x_3);
x_27 = l_List_foldlM___at_Lean_Meta_induction___spec__10(x_3, x_7, x_12, x_24, x_26, x_25, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
x_33 = l_Lean_Level_isZero(x_12);
lean_dec(x_12);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_32);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_34 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_34, 0, x_1);
x_35 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__6;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__8;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_box(0);
x_40 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_7, x_38, x_39, x_16, x_17, x_18, x_19, x_31);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_3);
x_45 = lean_box(0);
x_46 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___lambda__2(x_32, x_1, x_7, x_14, x_5, x_9, x_2, x_4, x_6, x_10, x_8, x_11, x_45, x_16, x_17, x_18, x_19, x_31);
lean_dec(x_14);
lean_dec(x_32);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_12);
lean_dec(x_3);
x_47 = lean_ctor_get(x_27, 1);
lean_inc(x_47);
lean_dec(x_27);
x_48 = lean_ctor_get(x_28, 0);
lean_inc(x_48);
lean_dec(x_28);
x_49 = lean_box(0);
x_50 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___lambda__2(x_48, x_1, x_7, x_14, x_5, x_9, x_2, x_4, x_6, x_10, x_8, x_11, x_49, x_16, x_17, x_18, x_19, x_47);
lean_dec(x_14);
lean_dec(x_48);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_27);
if (x_51 == 0)
{
return x_27;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_27, 0);
x_53 = lean_ctor_get(x_27, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_27);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
case 5:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_13, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_dec(x_13);
x_57 = lean_array_set(x_14, x_15, x_56);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_sub(x_15, x_58);
lean_dec(x_15);
x_13 = x_55;
x_14 = x_57;
x_15 = x_59;
goto _start;
}
default: 
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_61 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__3;
x_62 = lean_box(0);
x_63 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_7, x_61, x_62, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_63;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_19 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9(x_20, x_14, x_15, x_16, x_17, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_14);
x_25 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_1, x_14, x_15, x_16, x_17, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_LocalDecl_type(x_26);
lean_dec(x_26);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_28);
x_29 = l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(x_28, x_2, x_14, x_15, x_16, x_17, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg(x_3, x_28, x_14, x_15, x_16, x_17, x_31);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_28);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Expr_getAppNumArgsAux(x_34, x_35);
x_37 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_36);
x_38 = lean_mk_array(x_36, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_36, x_39);
lean_dec(x_36);
x_41 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11(x_4, x_5, x_6, x_7, x_8, x_9, x_3, x_10, x_11, x_12, x_13, x_23, x_34, x_38, x_40, x_14, x_15, x_16, x_17, x_33);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_29);
if (x_42 == 0)
{
return x_29;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_29, 0);
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_29);
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
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_25);
if (x_46 == 0)
{
return x_25;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_25, 0);
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_25);
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
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_19);
if (x_50 == 0)
{
return x_19;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_19, 0);
x_52 = lean_ctor_get(x_19, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_19);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Util___hyg_225____closed__2;
x_2 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after revert&intro\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
lean_inc(x_1);
x_16 = x_1;
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_umapMAux___at___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp___spec__1(x_17, x_16);
x_19 = x_18;
x_20 = lean_array_push(x_19, x_2);
x_21 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_22 = l_Lean_Meta_revert(x_3, x_20, x_21, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_array_get_size(x_1);
x_28 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_27);
x_29 = l_Lean_Meta_introNCore(x_26, x_27, x_28, x_21, x_11, x_12, x_13, x_14, x_24);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_34 = l_Lean_Meta_intro1Core(x_33, x_21, x_11, x_12, x_13, x_14, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_54; lean_object* x_55; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
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
x_39 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_40 = 0;
x_41 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__1;
x_42 = l_Array_forInUnsafe_loop___at_Lean_Meta_induction___spec__8(x_32, x_1, x_39, x_40, x_41);
lean_dec(x_1);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_65 = lean_st_ref_get(x_14, x_36);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 3);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_ctor_get_uint8(x_67, sizeof(void*)*1);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
x_70 = 0;
x_54 = x_70;
x_55 = x_69;
goto block_64;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
lean_dec(x_65);
x_72 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__2;
x_73 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_72, x_11, x_12, x_13, x_14, x_71);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_unbox(x_74);
lean_dec(x_74);
x_54 = x_76;
x_55 = x_75;
goto block_64;
}
block_53:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = x_32;
x_46 = l_Array_umapMAux___at_Lean_LocalContext_getFVars___spec__1(x_17, x_45);
x_47 = x_46;
lean_inc(x_37);
x_48 = l_Lean_mkFVar(x_37);
lean_inc(x_38);
x_49 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_49, 0, x_38);
lean_inc(x_38);
x_50 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 18, 12);
lean_closure_set(x_50, 0, x_37);
lean_closure_set(x_50, 1, x_4);
lean_closure_set(x_50, 2, x_38);
lean_closure_set(x_50, 3, x_5);
lean_closure_set(x_50, 4, x_6);
lean_closure_set(x_50, 5, x_7);
lean_closure_set(x_50, 6, x_8);
lean_closure_set(x_50, 7, x_9);
lean_closure_set(x_50, 8, x_25);
lean_closure_set(x_50, 9, x_43);
lean_closure_set(x_50, 10, x_47);
lean_closure_set(x_50, 11, x_48);
x_51 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__8___spec__2___rarg), 7, 2);
lean_closure_set(x_51, 0, x_49);
lean_closure_set(x_51, 1, x_50);
x_52 = l_Lean_Meta_withMVarContext___at_Lean_Meta_revert___spec__5___rarg(x_38, x_51, x_11, x_12, x_13, x_14, x_44);
return x_52;
}
block_64:
{
if (x_54 == 0)
{
x_44 = x_55;
goto block_53;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_inc(x_38);
x_56 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_56, 0, x_38);
x_57 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__4;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__2;
x_62 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_61, x_60, x_11, x_12, x_13, x_14, x_55);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_44 = x_63;
goto block_53;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_34);
if (x_77 == 0)
{
return x_34;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_34, 0);
x_79 = lean_ctor_get(x_34, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_34);
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
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_29);
if (x_81 == 0)
{
return x_29;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_29, 0);
x_83 = lean_ctor_get(x_29, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_29);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_22);
if (x_85 == 0)
{
return x_22;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_22, 0);
x_87 = lean_ctor_get(x_22, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_22);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not support dependent elimination, but conclusion depends on major premise");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (lean_obj_tag(x_9) == 5)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_array_set(x_10, x_11, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_11, x_20);
lean_dec(x_11);
x_9 = x_17;
x_10 = x_19;
x_11 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_9);
x_23 = lean_ctor_get(x_6, 5);
lean_inc(x_23);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_24 = l_List_forM___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_23, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_get(x_13, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_6, 6);
lean_inc(x_30);
x_31 = l_List_redLength___rarg(x_30);
x_32 = lean_mk_empty_array_with_capacity(x_31);
lean_dec(x_31);
lean_inc(x_30);
x_33 = l_List_toArrayAux___rarg(x_30, x_32);
x_34 = x_33;
x_35 = lean_unsigned_to_nat(0u);
lean_inc(x_29);
lean_inc(x_5);
lean_inc(x_1);
x_36 = lean_alloc_closure((void*)(l_Array_umapMAux___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_36, 0, x_1);
lean_closure_set(x_36, 1, x_5);
lean_closure_set(x_36, 2, x_8);
lean_closure_set(x_36, 3, x_10);
lean_closure_set(x_36, 4, x_29);
lean_closure_set(x_36, 5, x_30);
lean_closure_set(x_36, 6, x_35);
lean_closure_set(x_36, 7, x_34);
x_37 = x_36;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_38 = lean_apply_5(x_37, x_12, x_13, x_14, x_15, x_28);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_1);
x_41 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_40);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l_Lean_MetavarContext_exprDependsOn(x_29, x_43, x_2);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_box(0);
x_48 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2(x_39, x_2, x_1, x_7, x_3, x_4, x_5, x_6, x_23, x_47, x_12, x_13, x_14, x_15, x_44);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_39);
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_49 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_49, 0, x_3);
x_50 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__6;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___closed__2;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_box(0);
x_55 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_53, x_54, x_12, x_13, x_14, x_15, x_44);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
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
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_29);
x_60 = lean_ctor_get(x_41, 1);
lean_inc(x_60);
lean_dec(x_41);
x_61 = lean_box(0);
x_62 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2(x_39, x_2, x_1, x_7, x_3, x_4, x_5, x_6, x_23, x_61, x_12, x_13, x_14, x_15, x_60);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_39);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_41);
if (x_63 == 0)
{
return x_41;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_41, 0);
x_65 = lean_ctor_get(x_41, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_41);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_38);
if (x_67 == 0)
{
return x_38;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_38, 0);
x_69 = lean_ctor_get(x_38, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_38);
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
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_24);
if (x_71 == 0)
{
return x_24;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_24, 0);
x_73 = lean_ctor_get(x_24, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_24);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
lean_object* l_Lean_Meta_induction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_7);
lean_inc(x_1);
x_12 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_16 = l_Lean_Meta_mkRecursorInfo(x_2, x_15, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_LocalDecl_type(x_13);
lean_dec(x_13);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_19);
x_21 = l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(x_19, x_20, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg(x_3, x_19, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_19);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_Expr_getAppNumArgsAux(x_26, x_27);
x_29 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_28);
x_30 = lean_mk_array(x_28, x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_sub(x_28, x_31);
lean_dec(x_28);
lean_inc(x_26);
x_33 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12(x_3, x_1, x_2, x_4, x_5, x_17, x_20, x_26, x_26, x_30, x_32, x_7, x_8, x_9, x_10, x_25);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
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
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_12);
if (x_42 == 0)
{
return x_12;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_12, 0);
x_44 = lean_ctor_get(x_12, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_12);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* l_Lean_Meta_induction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2;
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_induction___lambda__1___boxed), 11, 5);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_11);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__8___spec__2___rarg), 7, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_14, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_induction___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfHeadPredImp___at_Lean_Meta_induction___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfHeadPredImp___at_Lean_Meta_induction___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_List_forM___at_Lean_Meta_induction___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forM___at_Lean_Meta_induction___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_List_elem___at_Lean_Meta_induction___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lean_Meta_induction___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
lean_object* l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Nat_forM_loop___at_Lean_Meta_induction___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_16;
}
}
lean_object* l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Array_umapMAux___at_Lean_Meta_induction___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_umapMAux___at_Lean_Meta_induction___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
return x_14;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_induction___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forInUnsafe_loop___at_Lean_Meta_induction___spec__8(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_List_foldlM___at_Lean_Meta_induction___spec__10___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_List_foldlM___at_Lean_Meta_induction___spec__10___lambda__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_List_foldlM___at_Lean_Meta_induction___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_foldlM___at_Lean_Meta_induction___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___lambda__2___boxed(lean_object** _args) {
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
x_19 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_19;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___boxed(lean_object** _args) {
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
lean_object* x_21; 
x_21 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_21;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__1___boxed(lean_object** _args) {
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
x_19 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_19;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
return x_16;
}
}
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_induction___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
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
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_2206_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__2;
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
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
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
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__1);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__2);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__3);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__4);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__5);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__6);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__7);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_addRecParams___closed__8);
l_Lean_Meta_InductionSubgoal_fields___default = _init_l_Lean_Meta_InductionSubgoal_fields___default();
lean_mark_persistent(l_Lean_Meta_InductionSubgoal_fields___default);
l_Lean_Meta_InductionSubgoal_subst___default = _init_l_Lean_Meta_InductionSubgoal_subst___default();
lean_mark_persistent(l_Lean_Meta_InductionSubgoal_subst___default);
l_Lean_Meta_Lean_Meta_Tactic_Induction___instance__1___closed__1 = _init_l_Lean_Meta_Lean_Meta_Tactic_Induction___instance__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Lean_Meta_Tactic_Induction___instance__1___closed__1);
l_Lean_Meta_Lean_Meta_Tactic_Induction___instance__1 = _init_l_Lean_Meta_Lean_Meta_Tactic_Induction___instance__1();
lean_mark_persistent(l_Lean_Meta_Lean_Meta_Tactic_Induction___instance__1);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__1 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__1);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__2 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__2);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__3 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_finalize_loop___lambda__3___closed__3);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__1);
l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_0__Lean_Meta_throwUnexpectedMajorType___rarg___closed__2);
l_List_forM___at_Lean_Meta_induction___spec__4___closed__1 = _init_l_List_forM___at_Lean_Meta_induction___spec__4___closed__1();
lean_mark_persistent(l_List_forM___at_Lean_Meta_induction___spec__4___closed__1);
l_List_forM___at_Lean_Meta_induction___spec__4___closed__2 = _init_l_List_forM___at_Lean_Meta_induction___spec__4___closed__2();
lean_mark_persistent(l_List_forM___at_Lean_Meta_induction___spec__4___closed__2);
l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1___closed__1 = _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1___closed__1);
l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1___closed__2 = _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1___closed__2();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__1___closed__2);
l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2___closed__1 = _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2___closed__1);
l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2___closed__2 = _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2___closed__2();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___lambda__2___closed__2);
l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___closed__1 = _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___closed__1();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___closed__1);
l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___closed__2 = _init_l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___closed__2();
lean_mark_persistent(l_Nat_forM_loop___at_Lean_Meta_induction___spec__6___closed__2);
l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__1 = _init_l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__1();
lean_mark_persistent(l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__1);
l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__2 = _init_l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__2();
lean_mark_persistent(l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__2);
l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__3 = _init_l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__3();
lean_mark_persistent(l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__3);
l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__4 = _init_l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__4();
lean_mark_persistent(l_Array_umapMAux___at_Lean_Meta_induction___spec__7___lambda__2___closed__4);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__4);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__5 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__5);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__6 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__6);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__7 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__7();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__7);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__8 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__8();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__11___closed__8);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___lambda__2___closed__4);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_induction___spec__12___closed__2);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Induction___hyg_2206_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
