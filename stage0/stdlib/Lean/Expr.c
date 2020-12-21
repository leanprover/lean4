// Lean compiler output
// Module: Lean.Expr
// Imports: Init Lean.Data.KVMap Lean.Level
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
lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux_match__1(lean_object*);
lean_object* l_Lean_Expr_isBinding___boxed(lean_object*);
lean_object* l_Lean_Expr_letName_x21___closed__2;
lean_object* l_Lean_Expr_data_match__1(lean_object*);
lean_object* l_Lean_Expr_ctorName___closed__7;
uint8_t l_Lean_Expr_bindingInfo_x21(lean_object*);
lean_object* l_Lean_Expr_updateSort___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setBool(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_mkDecIsFalse___closed__2;
lean_object* l_Lean_Expr_bvarIdx_x21___closed__3;
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Expr_Data_hash___boxed(lean_object*);
lean_object* l_Lean_Expr_isApp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hasAnyFVar_visit_match__1(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Expr_updateSort_x21_match__1(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object*);
uint8_t l_Lean_Expr_isCharLit(lean_object*);
lean_object* l_Lean_Expr_letName_x21(lean_object*);
uint8_t l_Lean_Expr_isNatLit(lean_object*);
lean_object* l_Lean_mkFreshMVarId___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateFn_match__1(lean_object*);
lean_object* l_Lean_BinderInfo_isAuxDecl_match__1___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_isAppOf___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
uint8_t l_Lean_Expr_isHeadBetaTargetFn(lean_object*);
uint8_t l_UInt64_decEq(uint64_t, uint64_t);
lean_object* l_Lean_Expr_bindingDomain_x21___closed__2;
lean_object* l_Lean_Expr_abstract___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___closed__1;
lean_object* l_Lean_Expr_isAtomic_match__1(lean_object*);
lean_object* l_Lean_Expr_updateConst___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkDecIsTrue___closed__3;
lean_object* l_Lean_Expr_withApp(lean_object*);
size_t l_UInt32_toUSize(uint32_t);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
lean_object* l_Lean_Expr_withAppAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateForall_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkDecIsFalse___closed__1;
lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux_match__1(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Expr_instHashableExpr___closed__1;
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Expr_getAppArgs(lean_object*);
lean_object* l_Lean_Expr_updateSort_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_setAppPPExplicit_match__1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_natLit_x3f_match__1(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkAppN___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isLit___boxed(lean_object*);
lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateLambda_x21___closed__3;
lean_object* l_Lean_Expr_getAppFn_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint64_t l_UInt64_add(uint64_t, uint64_t);
lean_object* l_Lean_Expr_constName_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isStringLit_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isLet_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_14__match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateConst_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingInfo_x21___closed__1;
lean_object* l_Lean_BinderInfo_isExplicit_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isMVar_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isApp_match__1(lean_object*);
lean_object* l_Lean_ExprStructEq_instHashableExprStructEq;
uint64_t l_Bool_toUInt64(uint8_t);
lean_object* l_Lean_Expr_updateMData_x21___closed__2;
lean_object* l_Lean_Expr_instantiateLevelParamsArray___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRevAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Expr_instantiateLevelParams___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isOptParam___boxed(lean_object*);
lean_object* l_Lean_Expr_updateMData_x21___closed__1;
lean_object* l_Lean_mkForallEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
lean_object* l_Lean_mkLit(lean_object*);
lean_object* l_Lean_Expr_getAppRevArgs(lean_object*);
lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_BinderInfo_toUInt64_match__1(lean_object*);
lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object*);
size_t l_Lean_Expr_Data_hash(uint64_t);
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit_match__1(lean_object*);
lean_object* l_Lean_mkDecIsTrue___closed__5;
lean_object* l_Lean_instDecidableLess___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateProj_match__1(lean_object*);
lean_object* l_Lean_annotation_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
size_t l_USize_sub(size_t, size_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Lean_Expr_isAppOfArity_match__1(lean_object*);
lean_object* l_Lean_Expr_betaRev___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object*);
lean_object* l_Lean_Expr_ctorName___closed__1;
lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21___closed__1;
extern lean_object* l_Lean_Level_mkData___closed__1;
lean_object* l_Lean_Expr_mvarId_x21___closed__1;
lean_object* l_Lean_ExprStructEq_beq_match__1(lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* l_Lean_Expr_constName_x21___boxed(lean_object*);
lean_object* l_Lean_Literal_type_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppRev___rarg(lean_object*, lean_object*);
uint64_t l_Lean_Expr_mkData___closed__3;
lean_object* l_Lean_annotation_x3f___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206__match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_mkDataForBinder(size_t, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_setPPExplicit(lean_object*, uint8_t);
uint64_t l___private_Lean_Expr_0__Lean_Expr_mkDataCore(size_t, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubst___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object*);
lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_Data_binderInfo___boxed(lean_object*);
lean_object* l_Lean_Expr_ctorName___closed__2;
lean_object* l_Lean_Expr_updateApp_x21___closed__2;
uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object*);
size_t l_Lean_Level_hash(lean_object*);
lean_object* l_Lean_Expr_ctorName___closed__8;
lean_object* l_Lean_Expr_lt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
extern lean_object* l_instInhabitedNat;
lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object*);
lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21___closed__2;
lean_object* l_Lean_mkSimpleThunkType___closed__1;
lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21___closed__1;
lean_object* l_Lean_Expr_isAppOfArity_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRevAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ctorName___closed__4;
uint8_t l_List_foldr___at_Lean_mkConst___spec__2(uint8_t, lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Literal_type___closed__3;
lean_object* l_Lean_Expr_isLet_match__1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_level_mvar(lean_object*);
lean_object* l_Lean_Expr_updateProj_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_instBEqExprStructEq___closed__1;
lean_object* l_Lean_Expr_updateForall_x21___closed__1;
lean_object* l_Lean_ExprStructEq_instHashableExprStructEq___closed__1;
lean_object* l_Lean_Expr_appFn_x21___closed__3;
lean_object* l_Lean_Expr_natLit_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isNatLit_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object*);
lean_object* l_Nat_max(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArgD(lean_object*, lean_object*, lean_object*);
size_t l_List_foldl___at_Lean_mkConst___spec__1(size_t, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21_match__1(lean_object*);
lean_object* l_Lean_Expr_getAppArgs___closed__1;
uint8_t l_Lean_Level_hasParam(lean_object*);
lean_object* l_Lean_Expr_updateMData_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateApp_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mkAppRevRange(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateLet_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isHeadBetaTargetFn_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_setAppPPExplicit_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateForall_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21___closed__2;
uint8_t lean_expr_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letName_x21___closed__1;
lean_object* l_Lean_Expr_getRevArgD_match__1(lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Expr_letName_x21___boxed(lean_object*);
lean_object* l_Lean_instCoeExprExprStructEq___boxed(lean_object*);
lean_object* l_Lean_Expr_updateForall_x21___closed__3;
lean_object* l_Lean_Expr_updateForall_x21(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Expr_instantiateLevelParamsArray___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object*);
lean_object* l_Lean_Expr_isNatLit_match__1(lean_object*);
lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_BinderInfo_hash___boxed(lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_mkAppRev___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_containsFVar___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ctorName___boxed(lean_object*);
lean_object* lean_expr_mk_forall(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_expr_instantiate(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21___closed__2;
lean_object* l_Lean_Expr_setOption(lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206__match__1___rarg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_instBEqExprStructEq;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object*);
lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object*);
lean_object* l_Lean_mkAppRev___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_mkFreshFVarId(lean_object*);
lean_object* l_Lean_BinderInfo_isExplicit_match__1(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2094____closed__3;
lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object*);
lean_object* l_Lean_Expr_updateLambdaE_x21___closed__1;
lean_object* l_Lean_Expr_getAppFn___boxed(lean_object*);
lean_object* l_Lean_Expr_isBinding_match__1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_14__match__1(lean_object*);
lean_object* l_Lean_Expr_updateForallE_x21_match__1(lean_object*);
lean_object* l_Lean_Expr_inferImplicit_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_natLit_x3f___boxed(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21_match__1(lean_object*);
lean_object* l_Lean_mkMData(lean_object*, lean_object*);
lean_object* l_Lean_BinderInfo_hash_match__1(lean_object*);
lean_object* l_Lean_Expr_bindingInfo_x21_match__1(lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsCore(lean_object*, lean_object*);
extern lean_object* l_List_get_x21___rarg___closed__3;
lean_object* l_Lean_Expr_updateFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateMData_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkDecIsTrue(lean_object*, lean_object*);
extern uint64_t l_instInhabitedUInt64;
lean_object* l_Lean_mkLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instQuoteSubstring___closed__2;
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_setOption___at_Lean_Expr_setPPExplicit___spec__1(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_isMVar___boxed(lean_object*);
uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Literal_type(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubstArray(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21___closed__3;
lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isConstOf___boxed(lean_object*, lean_object*);
lean_object* lean_expr_mk_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Expr_isSort_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqBinderInfo;
lean_object* l_Lean_Expr_fvarId_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateSort_x21___closed__3;
uint64_t l_Lean_BinderInfo_toUInt64(uint8_t);
lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain_match__1(lean_object*);
lean_object* l_Lean_Expr_letName_x21___closed__3;
lean_object* l_Lean_Expr_updateLambda_x21(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_isProj_match__1(lean_object*);
lean_object* l_Lean_Expr_updateForall_x21___closed__2;
lean_object* l_Lean_Expr_updateLambdaE_x21___closed__2;
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getOptParamDefault_x3f___closed__2;
lean_object* l_Lean_BinderInfo_hash_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_inferImplicit_match__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateFn(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux_match__1(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateSort_x21(lean_object*, lean_object*);
uint8_t lean_expr_has_expr_mvar(lean_object*);
lean_object* l_Lean_Expr_constName_x21___closed__3;
uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
lean_object* l_Lean_Expr_etaExpandedStrict_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instCoeExprExprStructEq(lean_object*);
lean_object* l_Lean_Expr_updateConst_x21(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object*);
lean_object* l_Lean_Expr_isConst_match__1(lean_object*);
lean_object* l_Lean_Expr_ctorName_match__1(lean_object*);
lean_object* l_Lean_Expr_isAppOf_match__1(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21_match__1(lean_object*);
lean_object* l_Lean_Expr_isConstOf_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isLambda_match__1(lean_object*);
uint8_t lean_expr_has_mvar(lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_BinderInfo_toUInt64_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ctorName___closed__5;
lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21___closed__2;
lean_object* l_Lean_Expr_isBinding_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_BinderInfo_isInstImplicit_match__1(lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_annotation_x3f_match__1(lean_object*);
uint8_t lean_expr_binder_info(lean_object*);
uint64_t l_Lean_Expr_mkData___closed__2;
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letName_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isLit_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isHeadBetaTargetFn_match__1(lean_object*);
lean_object* l_Lean_Expr_isMData_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_etaExpandedStrict_x3f_match__1(lean_object*);
lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_abstractRange___boxed(lean_object*, lean_object*, lean_object*);
uint32_t l_UInt64_toUInt32(uint64_t);
lean_object* l_Lean_Expr_isLit_match__1(lean_object*);
lean_object* l_Lean_mkFreshId___rarg(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedLiteral;
lean_object* l_Lean_Expr_instToStringExpr___closed__1;
uint64_t l_Lean_Expr_data(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
extern lean_object* l_Lean_myMacro____x40_Init_NotationExtra___hyg_1127____closed__32;
lean_object* l_Lean_Expr_updateApp_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubstArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*);
uint8_t l_Lean_Expr_isBinding(lean_object*);
lean_object* l_Lean_Expr_isAppOf_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object*);
lean_object* l_Lean_Expr_consumeMData_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateProj_x21(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkDecIsTrue___closed__1;
lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21_match__1(lean_object*);
lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object*);
lean_object* l_Lean_Expr_isForall_match__1(lean_object*);
lean_object* l_Lean_BinderInfo_isExplicit_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object*);
lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubst_match__1(lean_object*);
lean_object* l_List_map___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206____boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_hasFVar(uint64_t);
lean_object* l_Lean_Expr_getAppNumArgsAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instBEqExpr___closed__1;
lean_object* l_Lean_Expr_hasMVarEx___boxed(lean_object*);
lean_object* l_Lean_mkAppRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateForallE_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateLambdaE_x21_match__1(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21___closed__1;
lean_object* l_Lean_Expr_updateConst_x21___closed__2;
lean_object* lean_expr_mk_bvar(lean_object*);
lean_object* l_Lean_Expr_updateApp_x21_match__1(lean_object*);
lean_object* l_Lean_Expr_instHashableExpr;
lean_object* l_Lean_mkDecIsTrue___closed__2;
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21___closed__3;
lean_object* l_Lean_Literal_type___boxed(lean_object*);
lean_object* l_Lean_Literal_type___closed__1;
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Literal_hash_match__1(lean_object*);
lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21___closed__1;
lean_object* l_Lean_Expr_isConst_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_BinderInfo_isInstImplicit_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ctorName___closed__3;
lean_object* l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_natLit_x3f(lean_object*);
lean_object* lean_expr_mk_const(lean_object*, lean_object*);
lean_object* l_Lean_Expr_data_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Literal_lt_match__1(lean_object*);
lean_object* l_Lean_mkAppRange(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isCharLit___closed__3;
lean_object* l_Lean_instHasLessLiteral;
lean_object* l_Lean_Literal_type___closed__4;
lean_object* l_Lean_mkDecIsTrue___closed__4;
lean_object* lean_expr_mk_lit(lean_object*);
lean_object* l_Lean_Expr_updateMData_x21(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_hasLevelMVar(uint64_t);
lean_object* lean_expr_dbg_to_string(lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Data_Options___hyg_487____closed__3;
lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateConst_x21___closed__1;
lean_object* l_Lean_Expr_constName_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_ctorName_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_mkDataForLet(size_t, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateProj_x21___closed__3;
lean_object* l_Lean_Expr_hasAnyFVar_visit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Literal_type___closed__2;
lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiate___boxed(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_14_(lean_object*, lean_object*);
lean_object* l_Lean_mkSimpleThunk___closed__1;
lean_object* l_Lean_Expr_appFn_x21___closed__1;
lean_object* l_Lean_Expr_updateApp_x21___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_BinderInfo_hash_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLevelMVar(lean_object*);
lean_object* lean_expr_mk_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21___closed__3;
lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hasFVar___boxed(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_instBEqData__1___boxed(lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isAuxDecl(uint8_t);
lean_object* l_Lean_Expr_bindingName_x21___closed__1;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object*);
uint8_t l_Lean_Expr_Data_nonDepLet(uint64_t);
lean_object* l_Lean_Expr_bindingName_x21_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object*);
lean_object* l_Lean_mkFreshFVarId___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint64_t l_UInt64_land(uint64_t, uint64_t);
lean_object* l_Lean_Expr_updateMData_x21_match__1(lean_object*);
lean_object* l_Lean_Expr_isMData_match__1(lean_object*);
lean_object* lean_expr_mk_app(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21___closed__2;
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_mkDecIsFalse(lean_object*, lean_object*);
uint8_t lean_expr_quick_lt(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLit(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__1;
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Expr_mkData___boxed__const__1;
lean_object* l_Lean_MData_empty;
size_t lean_usize_of_nat(lean_object*);
extern uint64_t l_instInhabitedUInt64___closed__1;
lean_object* l_Lean_mkSimpleThunkType(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRevAux_match__1(lean_object*);
size_t l_Lean_ExprStructEq_hash(lean_object*);
uint8_t l_Lean_Expr_isAutoParam(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21_match__1(lean_object*);
lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__2;
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_instInhabitedLiteral___closed__1;
lean_object* l_Lean_Expr_updateSort_x21___closed__2;
lean_object* l_Lean_BinderInfo_isAuxDecl_match__1(lean_object*);
lean_object* l_Lean_Expr_ctorName(lean_object*);
lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_NotationExtra___hyg_3476____closed__42;
lean_object* l_Lean_Expr_isSort_match__1(lean_object*);
lean_object* l_Lean_Expr_data___boxed(lean_object*);
lean_object* l_Lean_Expr_setPPExplicit___closed__1;
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Expr_setPPExplicit___closed__2;
lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
lean_object* l_Lean_Expr_bvarIdx_x21(lean_object*);
lean_object* l_Lean_Expr_updateProj_x21___closed__2;
lean_object* l_Lean_Expr_constName_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData_match__1(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21_match__1(lean_object*);
lean_object* l_Lean_Expr_setAppPPExplicit(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRevAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ctorName___closed__9;
lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain_match__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_instInhabitedBinderInfo;
lean_object* l_Lean_Expr_updateLambda_x21___closed__1;
lean_object* l_Lean_mkAppN___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingInfo_x21_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mkDataForLet___boxed__const__1;
lean_object* l_Lean_Expr_updateProj_x21___closed__1;
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__4;
lean_object* l_Lean_Expr_getAppFn_match__1(lean_object*);
lean_object* l_Lean_ExprStructEq_beq_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isProj___boxed(lean_object*);
lean_object* l_Lean_Expr_updateLambda_x21___closed__2;
lean_object* l_Lean_Expr_updateFn_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux_match__1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206__match__1(lean_object*);
lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object*);
lean_object* l_Lean_Expr_getRevArgD_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateMData___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object*);
lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object*);
lean_object* l_Lean_Expr_isAtomic_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableBinderInfo___closed__1;
lean_object* l___private_Lean_Expr_0__Lean_Expr_mkDataCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_mk_mvar(lean_object*);
lean_object* l_Lean_Expr_isForall_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object*);
lean_object* l_Lean_Expr_ctorName___closed__10;
lean_object* l_Lean_Expr_constLevels_x21___closed__1;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_mkAppRev___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_getOptParamDefault_x3f___closed__1;
uint8_t l_Lean_instDecidableLess(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
uint8_t lean_expr_has_fvar(lean_object*);
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hasAnyFVar(lean_object*, lean_object*);
lean_object* l_Lean_Expr_setPPExplicit___closed__3;
lean_object* l_Lean_Expr_hasMVar___boxed(lean_object*);
lean_object* l_Lean_mkForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21___closed__2;
lean_object* l___private_Lean_Expr_0__Lean_Expr_mkDataCore___boxed__const__1;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___boxed(lean_object*, lean_object*);
size_t l_Lean_Literal_hash(lean_object*);
lean_object* l_Lean_mkLambdaEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
uint64_t l_Lean_instInhabitedData__1;
lean_object* l_Lean_instBEqLiteral___closed__1;
lean_object* l_Lean_instHashableBinderInfo;
lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object*);
extern lean_object* l_Lean_KVMap_empty;
lean_object* l_Lean_Expr_isLambda_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_BinderInfo_isAuxDecl_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateMData_x21___closed__3;
lean_object* l_Lean_Expr_constName_x21_match__1(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object*);
lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateConst_x21_match__1(lean_object*);
lean_object* l_Lean_Expr_mkDataForBinder___boxed__const__1;
lean_object* l_Lean_Expr_bvarIdx_x21___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_14____boxed(lean_object*, lean_object*);
uint32_t l_USize_toUInt32(size_t);
lean_object* l_Lean_Expr_withApp___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateLet_x21_match__1(lean_object*);
lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubst(lean_object*, lean_object*, lean_object*);
uint64_t l_UInt64_shiftLeft(uint64_t, uint64_t);
lean_object* l_Lean_Expr_binderInfo___boxed(lean_object*);
lean_object* l_Lean_instInhabitedExpr___closed__1;
lean_object* l_Lean_Literal_lt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_insertCore(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
lean_object* l_Lean_BinderInfo_toUInt64_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21___closed__2;
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateLambda_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_mk_proj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isMVar_match__1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux_match__1(lean_object*);
lean_object* l_Lean_Expr_appFn_x21___closed__2;
lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object*);
lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object*);
lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvarIdx_x21___closed__2;
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21___closed__1;
uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t);
lean_object* l_Lean_Expr_dbgToString___boxed(lean_object*);
lean_object* l_Lean_Expr_isForall___boxed(lean_object*);
lean_object* l_Lean_Expr_isMData___boxed(lean_object*);
lean_object* l_Lean_Expr_isProp___boxed(lean_object*);
lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object*);
lean_object* l_Lean_Expr_updateLambdaE_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isStringLit___boxed(lean_object*);
lean_object* l_Lean_Expr_withAppRev(lean_object*);
lean_object* l_Lean_Expr_quickLt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_instToStringExpr;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isFVar_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint64_t l_UInt32_toUInt64(uint32_t);
lean_object* l_Lean_ExprStructEq_instToStringExprStructEq___boxed(lean_object*);
lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicit___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_BinderInfo_isAuxDecl___boxed(lean_object*);
lean_object* l_List_foldl___at_Lean_mkConst___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Literal_lt_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isFVar_match__1(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiate1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody_match__1(lean_object*);
lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Literal_hash_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
lean_object* l_Lean_Expr_isSort___boxed(lean_object*);
lean_object* l_Lean_Expr_updateLet_x21___closed__1;
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
uint64_t l_Lean_Expr_mkData___closed__4;
lean_object* l_Lean_BinderInfo_isInstImplicit_match__1___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Literal_type_match__1(lean_object*);
lean_object* lean_expr_mk_sort(lean_object*);
lean_object* l_Lean_Literal_hash___boxed(lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
lean_object* l_Lean_Expr_isBVar___boxed(lean_object*);
lean_object* l_Lean_instHashableLiteral___closed__1;
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParams___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_mk_fvar(lean_object*);
lean_object* l_Lean_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_updateProj___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isStringLit(lean_object*);
lean_object* l_Lean_mkFreshMVarId(lean_object*);
lean_object* l_Lean_Expr_isProp_match__1(lean_object*);
lean_object* l_Lean_ExprStructEq_hash_match__1(lean_object*);
size_t lean_expr_hash(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProj(lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206_(uint8_t, uint8_t);
lean_object* l_Lean_ExprStructEq_hash_match__1___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_binderInfo(lean_object*);
size_t lean_usize_mix_hash(size_t, size_t);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
lean_object* l_Lean_instHashableLiteral;
uint8_t l_Lean_Expr_isAtomic(lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getArg_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instBEqExpr;
lean_object* l_Lean_instInhabitedExprStructEq;
uint8_t l_List_foldr___at_Lean_mkConst___spec__3(uint8_t, lean_object*);
lean_object* l_Lean_Expr_updateProj_x21_match__1(lean_object*);
lean_object* l_Lean_Expr_appFn_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ctorName___closed__6;
lean_object* l_Lean_Expr_updateMData_match__1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_expr_loose_bvar_range(lean_object*);
lean_object* l_Lean_Expr_inferImplicit(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateForallE_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvarIdx_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isBVar_match__1(lean_object*);
uint8_t l_Lean_instBEqData__1(uint64_t, uint64_t);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkAppN___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubst_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mkData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_instToStringExprStructEq(lean_object*);
lean_object* l_Lean_Expr_isProp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_BinderInfo_isExplicit___boxed(lean_object*);
uint64_t l_Lean_Expr_mkData___closed__1;
lean_object* l_List_foldr___at_Lean_mkConst___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hashEx___boxed(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkDecIsFalse___closed__3;
lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object*);
lean_object* l_Lean_Expr_updateLet_x21___closed__2;
lean_object* l_Lean_Expr_constLevels_x21_match__1(lean_object*);
lean_object* l_Lean_Expr_setOption___at_Lean_Expr_setPPExplicit___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isAtomic___boxed(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux_match__1(lean_object*);
lean_object* l_Lean_Expr_Data_nonDepLet___boxed(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Level_instantiateParams(lean_object*, lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Lean_Expr_getArgD(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_updateForall_x21_match__1(lean_object*);
lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object*);
lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicit___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvarIdx_x21_match__1(lean_object*);
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
uint64_t l_UInt64_shiftRight(uint64_t, uint64_t);
lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object*);
lean_object* lean_lit_type(lean_object*);
lean_object* l_Lean_instBEqLiteral;
lean_object* l_Lean_Expr_getArgD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqBinderInfo___closed__1;
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isCharLit___closed__2;
lean_object* l_Lean_Expr_setOption___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(lean_object*, lean_object*, lean_object*);
size_t l_Lean_BinderInfo_hash(uint8_t);
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letName_x21_match__1(lean_object*);
lean_object* l_List_map___at_Lean_Expr_instantiateLevelParams___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21_match__1(lean_object*);
lean_object* l_Lean_Expr_isApp___boxed(lean_object*);
lean_object* l_Lean_Expr_isCharLit___closed__4;
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* lean_expr_mk_lambda(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_consumeMData___boxed(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_Expr_equal___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateLet_x21(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Literal_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object*);
lean_object* l_Lean_Expr_updateLambda_x21_match__1(lean_object*);
lean_object* l_Lean_mkSimpleThunk(lean_object*);
lean_object* l_Lean_Expr_inferImplicit_match__1(lean_object*);
lean_object* l_Lean_Expr_isLambda___boxed(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Expr_updateForallE_x21___closed__2;
lean_object* lean_expr_instantiate_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_List_map___at_Lean_Expr_instantiateLevelParamsArray___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux(lean_object*);
lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_11811____closed__19;
lean_object* l_Lean_Expr_updateProj_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___closed__2;
lean_object* l_Lean_Expr_updateForallE_x21___closed__1;
lean_object* l_Lean_Expr_hasAnyFVar_visit(lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21_match__1(lean_object*);
lean_object* l_Lean_Expr_updateSort_x21___closed__1;
lean_object* l_Lean_Expr_isConst___boxed(lean_object*);
lean_object* l_Lean_Expr_updateLambda_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isConstOf_match__1(lean_object*);
size_t lean_string_hash(lean_object*);
lean_object* l_Lean_Expr_isNatLit___boxed(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__3;
lean_object* l_List_foldr___at_Lean_mkConst___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
lean_object* l_Lean_Expr_isStringLit_match__1(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_isLet___boxed(lean_object*);
lean_object* l_Lean_Expr_bindingInfo_x21___closed__2;
lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
extern lean_object* l_myMacro____x40_Init_System_IO___hyg_2501____closed__17;
lean_object* l_Lean_Expr_isCharLit___closed__1;
lean_object* l_Lean_Expr_isCharLit___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t);
lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
lean_object* l_Lean_Expr_isBVar_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_mkData(size_t, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* l_Lean_Expr_isProj_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_level_param(lean_object*);
static lean_object* _init_l_Lean_instInhabitedLiteral___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedLiteral() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedLiteral___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_14__match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_apply_2(x_5, x_1, x_2);
return x_9;
}
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_2(x_5, x_1, x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_apply_2(x_4, x_11, x_12);
return x_13;
}
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_14__match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_14__match__1___rarg), 5, 0);
return x_2;
}
}
uint8_t l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_14_(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_string_dec_eq(x_8, x_9);
return x_10;
}
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_14____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_14_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqLiteral___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_14____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instBEqLiteral() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instBEqLiteral___closed__1;
return x_1;
}
}
lean_object* l_Lean_Literal_hash_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
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
lean_object* l_Lean_Literal_hash_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Literal_hash_match__1___rarg), 3, 0);
return x_2;
}
}
size_t l_Lean_Literal_hash(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; size_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_usize_of_nat(x_2);
return x_3;
}
else
{
lean_object* x_4; size_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_string_hash(x_4);
return x_5;
}
}
}
lean_object* l_Lean_Literal_hash___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Lean_Literal_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableLiteral___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Literal_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instHashableLiteral() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instHashableLiteral___closed__1;
return x_1;
}
}
lean_object* l_Lean_Literal_lt_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_2(x_4, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_2(x_3, x_10, x_11);
return x_12;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
lean_dec(x_5);
x_13 = lean_apply_2(x_6, x_1, x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_apply_2(x_5, x_14, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_Literal_lt_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Literal_lt_match__1___rarg), 6, 0);
return x_2;
}
}
uint8_t l_Lean_Literal_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_lt(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_string_dec_lt(x_8, x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_Literal_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Literal_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instHasLessLiteral() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
uint8_t l_Lean_instDecidableLess(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Literal_lt(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_instDecidableLess___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_instDecidableLess(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static uint8_t _init_l_Lean_instInhabitedBinderInfo() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
lean_object* l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206__match__1___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_box(x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_3);
x_12 = lean_box(x_1);
x_13 = lean_box(x_2);
x_14 = lean_apply_2(x_8, x_12, x_13);
return x_14;
}
}
case 1:
{
lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_15 = lean_box(x_2);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
x_16 = lean_box(0);
x_17 = lean_apply_1(x_4, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_4);
x_18 = lean_box(x_1);
x_19 = lean_box(x_2);
x_20 = lean_apply_2(x_8, x_18, x_19);
return x_20;
}
}
case 2:
{
lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_box(x_2);
if (lean_obj_tag(x_21) == 2)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_22 = lean_box(0);
x_23 = lean_apply_1(x_5, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_5);
x_24 = lean_box(x_1);
x_25 = lean_box(x_2);
x_26 = lean_apply_2(x_8, x_24, x_25);
return x_26;
}
}
case 3:
{
lean_object* x_27; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = lean_box(x_2);
if (lean_obj_tag(x_27) == 3)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_8);
x_28 = lean_box(0);
x_29 = lean_apply_1(x_6, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_6);
x_30 = lean_box(x_1);
x_31 = lean_box(x_2);
x_32 = lean_apply_2(x_8, x_30, x_31);
return x_32;
}
}
default: 
{
lean_object* x_33; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_box(x_2);
if (lean_obj_tag(x_33) == 4)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
x_34 = lean_box(0);
x_35 = lean_apply_1(x_7, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_33);
lean_dec(x_7);
x_36 = lean_box(x_1);
x_37 = lean_box(x_2);
x_38 = lean_apply_2(x_8, x_36, x_37);
return x_38;
}
}
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206__match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206__match__1___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206__match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206__match__1___rarg(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206_(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; 
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
case 1:
{
lean_object* x_6; 
x_6 = lean_box(x_2);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 0;
return x_8;
}
}
case 2:
{
lean_object* x_9; 
x_9 = lean_box(x_2);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = 0;
return x_11;
}
}
case 3:
{
lean_object* x_12; 
x_12 = lean_box(x_2);
if (lean_obj_tag(x_12) == 3)
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_12);
x_14 = 0;
return x_14;
}
}
default: 
{
lean_object* x_15; 
x_15 = lean_box(x_2);
if (lean_obj_tag(x_15) == 4)
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_15);
x_17 = 0;
return x_17;
}
}
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instBEqBinderInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instBEqBinderInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instBEqBinderInfo___closed__1;
return x_1;
}
}
lean_object* l_Lean_BinderInfo_hash_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_4, x_11);
return x_12;
}
case 3:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_5, x_13);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_6, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_BinderInfo_hash_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_BinderInfo_hash_match__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_BinderInfo_hash_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_BinderInfo_hash_match__1___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
size_t l_Lean_BinderInfo_hash(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
size_t x_2; 
x_2 = 947;
return x_2;
}
case 1:
{
size_t x_3; 
x_3 = 1019;
return x_3;
}
case 2:
{
size_t x_4; 
x_4 = 1087;
return x_4;
}
case 3:
{
size_t x_5; 
x_5 = 1153;
return x_5;
}
default: 
{
size_t x_6; 
x_6 = 1229;
return x_6;
}
}
}
}
lean_object* l_Lean_BinderInfo_hash___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_BinderInfo_hash(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
lean_object* l_Lean_BinderInfo_isExplicit_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_box(x_1);
switch (lean_obj_tag(x_6)) {
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 2:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_4, x_11);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(x_1);
x_14 = lean_apply_1(x_5, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_BinderInfo_isExplicit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_BinderInfo_isExplicit_match__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_BinderInfo_isExplicit_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_BinderInfo_isExplicit_match__1___rarg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 4:
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
default: 
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = 0;
return x_5;
}
}
}
}
lean_object* l_Lean_BinderInfo_isExplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_BinderInfo_isExplicit(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instHashableBinderInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_BinderInfo_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instHashableBinderInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instHashableBinderInfo___closed__1;
return x_1;
}
}
lean_object* l_Lean_BinderInfo_isInstImplicit_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(x_1);
if (lean_obj_tag(x_4) == 3)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
lean_object* l_Lean_BinderInfo_isInstImplicit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_BinderInfo_isInstImplicit_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_BinderInfo_isInstImplicit_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_BinderInfo_isInstImplicit_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 3)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 0;
return x_4;
}
}
}
lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_BinderInfo_isInstImplicit(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_BinderInfo_isAuxDecl_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(x_1);
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
lean_object* l_Lean_BinderInfo_isAuxDecl_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_BinderInfo_isAuxDecl_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_BinderInfo_isAuxDecl_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_BinderInfo_isAuxDecl_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
uint8_t l_Lean_BinderInfo_isAuxDecl(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 4)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 0;
return x_4;
}
}
}
lean_object* l_Lean_BinderInfo_isAuxDecl___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_BinderInfo_isAuxDecl(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_MData_empty() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static uint64_t _init_l_Lean_instInhabitedData__1() {
_start:
{
uint64_t x_1; 
x_1 = l_instInhabitedUInt64;
return x_1;
}
}
size_t l_Lean_Expr_Data_hash(uint64_t x_1) {
_start:
{
uint32_t x_2; size_t x_3; 
x_2 = ((uint32_t)x_1);
x_3 = x_2;
return x_3;
}
}
lean_object* l_Lean_Expr_Data_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_hash(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
uint8_t l_Lean_instBEqData__1(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 == x_2;
return x_3;
}
}
lean_object* l_Lean_instBEqData__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lean_instBEqData__1(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint32_t x_4; 
x_2 = 40;
x_3 = x_1 >> x_2;
x_4 = ((uint32_t)x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_looseBVarRange(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
uint8_t l_Lean_Expr_Data_hasFVar(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint8_t x_6; 
x_2 = 32;
x_3 = x_1 >> x_2;
x_4 = 1;
x_5 = x_3 & x_4;
x_6 = x_5 == x_4;
return x_6;
}
}
lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_hasFVar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint8_t x_6; 
x_2 = 33;
x_3 = x_1 >> x_2;
x_4 = 1;
x_5 = x_3 & x_4;
x_6 = x_5 == x_4;
return x_6;
}
}
lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_hasExprMVar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_Expr_Data_hasLevelMVar(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint8_t x_6; 
x_2 = 34;
x_3 = x_1 >> x_2;
x_4 = 1;
x_5 = x_3 & x_4;
x_6 = x_5 == x_4;
return x_6;
}
}
lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_hasLevelMVar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint8_t x_6; 
x_2 = 35;
x_3 = x_1 >> x_2;
x_4 = 1;
x_5 = x_3 & x_4;
x_6 = x_5 == x_4;
return x_6;
}
}
lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_hasLevelParam(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_Expr_Data_nonDepLet(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint8_t x_6; 
x_2 = 36;
x_3 = x_1 >> x_2;
x_4 = 1;
x_5 = x_3 & x_4;
x_6 = x_5 == x_4;
return x_6;
}
}
lean_object* l_Lean_Expr_Data_nonDepLet___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_nonDepLet(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_Data_binderInfo___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = (uint8_t)((x_2 << 24) >> 61);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_BinderInfo_toUInt64_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_4, x_11);
return x_12;
}
case 3:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_5, x_13);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_6, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_BinderInfo_toUInt64_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_BinderInfo_toUInt64_match__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_BinderInfo_toUInt64_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_BinderInfo_toUInt64_match__1___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = (uint64_t)x_2;
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Expr.0.Lean.Expr.mkDataCore");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bound variable index is too big");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_3 = lean_unsigned_to_nat(123u);
x_4 = lean_unsigned_to_nat(44u);
x_5 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_mkDataCore___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedData__1;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
uint64_t l___private_Lean_Expr_0__Lean_Expr_mkDataCore(size_t x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Level_mkData___closed__1;
x_10 = lean_nat_dec_lt(x_9, x_2);
if (x_10 == 0)
{
uint32_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; 
x_11 = (uint32_t)x_1;
x_12 = ((uint64_t)x_11);
x_13 = (uint64_t)x_3;
x_14 = 32;
x_15 = x_13 << x_14;
x_16 = x_12 + x_15;
x_17 = (uint64_t)x_4;
x_18 = 33;
x_19 = x_17 << x_18;
x_20 = x_16 + x_19;
x_21 = (uint64_t)x_5;
x_22 = 34;
x_23 = x_21 << x_22;
x_24 = x_20 + x_23;
x_25 = (uint64_t)x_6;
x_26 = 35;
x_27 = x_25 << x_26;
x_28 = x_24 + x_27;
x_29 = (uint64_t)x_7;
x_30 = 36;
x_31 = x_29 << x_30;
x_32 = x_28 + x_31;
x_33 = (uint64_t)x_8;
x_34 = 37;
x_35 = x_33 << x_34;
x_36 = x_32 + x_35;
x_37 = lean_uint64_of_nat(x_2);
x_38 = 40;
x_39 = x_37 << x_38;
x_40 = x_36 + x_39;
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint64_t x_44; 
x_41 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__4;
x_42 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___boxed__const__1;
x_43 = lean_panic_fn(x_42, x_41);
x_44 = lean_unbox_uint64(x_43);
lean_dec(x_43);
return x_44;
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_mkDataCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint64_t x_16; lean_object* x_17; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = lean_unbox(x_7);
lean_dec(x_7);
x_15 = lean_unbox(x_8);
lean_dec(x_8);
x_16 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore(x_9, x_2, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_2);
x_17 = lean_box_uint64(x_16);
return x_17;
}
}
static uint64_t _init_l_Lean_Expr_mkData___closed__1() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 0;
x_2 = (uint64_t)x_1;
return x_2;
}
}
static uint64_t _init_l_Lean_Expr_mkData___closed__2() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 36;
x_2 = l_Lean_Expr_mkData___closed__1;
x_3 = x_2 << x_1;
return x_3;
}
}
static uint64_t _init_l_Lean_Expr_mkData___closed__3() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 0;
x_2 = (uint64_t)x_1;
return x_2;
}
}
static uint64_t _init_l_Lean_Expr_mkData___closed__4() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 37;
x_2 = l_Lean_Expr_mkData___closed__3;
x_3 = x_2 << x_1;
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_mkData___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedData__1;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
uint64_t l_Lean_Expr_mkData(size_t x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Level_mkData___closed__1;
x_8 = lean_nat_dec_lt(x_7, x_2);
if (x_8 == 0)
{
uint32_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; 
x_9 = (uint32_t)x_1;
x_10 = ((uint64_t)x_9);
x_11 = (uint64_t)x_3;
x_12 = 32;
x_13 = x_11 << x_12;
x_14 = x_10 + x_13;
x_15 = (uint64_t)x_4;
x_16 = 33;
x_17 = x_15 << x_16;
x_18 = x_14 + x_17;
x_19 = (uint64_t)x_5;
x_20 = 34;
x_21 = x_19 << x_20;
x_22 = x_18 + x_21;
x_23 = (uint64_t)x_6;
x_24 = 35;
x_25 = x_23 << x_24;
x_26 = x_22 + x_25;
x_27 = l_Lean_Expr_mkData___closed__2;
x_28 = x_26 + x_27;
x_29 = l_Lean_Expr_mkData___closed__4;
x_30 = x_28 + x_29;
x_31 = lean_uint64_of_nat(x_2);
x_32 = 40;
x_33 = x_31 << x_32;
x_34 = x_30 + x_33;
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint64_t x_38; 
x_35 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__4;
x_36 = l_Lean_Expr_mkData___boxed__const__1;
x_37 = lean_panic_fn(x_36, x_35);
x_38 = lean_unbox_uint64(x_37);
lean_dec(x_37);
return x_38;
}
}
}
lean_object* l_Lean_Expr_mkData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint64_t x_12; lean_object* x_13; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l_Lean_Expr_mkData(x_7, x_2, x_8, x_9, x_10, x_11);
lean_dec(x_2);
x_13 = lean_box_uint64(x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_Expr_mkDataForBinder___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedData__1;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
uint64_t l_Lean_Expr_mkDataForBinder(size_t x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Level_mkData___closed__1;
x_9 = lean_nat_dec_lt(x_8, x_2);
if (x_9 == 0)
{
uint32_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; 
x_10 = (uint32_t)x_1;
x_11 = ((uint64_t)x_10);
x_12 = (uint64_t)x_3;
x_13 = 32;
x_14 = x_12 << x_13;
x_15 = x_11 + x_14;
x_16 = (uint64_t)x_4;
x_17 = 33;
x_18 = x_16 << x_17;
x_19 = x_15 + x_18;
x_20 = (uint64_t)x_5;
x_21 = 34;
x_22 = x_20 << x_21;
x_23 = x_19 + x_22;
x_24 = (uint64_t)x_6;
x_25 = 35;
x_26 = x_24 << x_25;
x_27 = x_23 + x_26;
x_28 = l_Lean_Expr_mkData___closed__2;
x_29 = x_27 + x_28;
x_30 = (uint64_t)x_7;
x_31 = 37;
x_32 = x_30 << x_31;
x_33 = x_29 + x_32;
x_34 = lean_uint64_of_nat(x_2);
x_35 = 40;
x_36 = x_34 << x_35;
x_37 = x_33 + x_36;
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; 
x_38 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__4;
x_39 = l_Lean_Expr_mkDataForBinder___boxed__const__1;
x_40 = lean_panic_fn(x_39, x_38);
x_41 = lean_unbox_uint64(x_40);
lean_dec(x_40);
return x_41;
}
}
}
lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint64_t x_14; lean_object* x_15; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_Expr_mkDataForBinder(x_8, x_2, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
x_15 = lean_box_uint64(x_14);
return x_15;
}
}
static lean_object* _init_l_Lean_Expr_mkDataForLet___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedData__1;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
uint64_t l_Lean_Expr_mkDataForLet(size_t x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Level_mkData___closed__1;
x_9 = lean_nat_dec_lt(x_8, x_2);
if (x_9 == 0)
{
uint32_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; 
x_10 = (uint32_t)x_1;
x_11 = ((uint64_t)x_10);
x_12 = (uint64_t)x_3;
x_13 = 32;
x_14 = x_12 << x_13;
x_15 = x_11 + x_14;
x_16 = (uint64_t)x_4;
x_17 = 33;
x_18 = x_16 << x_17;
x_19 = x_15 + x_18;
x_20 = (uint64_t)x_5;
x_21 = 34;
x_22 = x_20 << x_21;
x_23 = x_19 + x_22;
x_24 = (uint64_t)x_6;
x_25 = 35;
x_26 = x_24 << x_25;
x_27 = x_23 + x_26;
x_28 = (uint64_t)x_7;
x_29 = 36;
x_30 = x_28 << x_29;
x_31 = x_27 + x_30;
x_32 = l_Lean_Expr_mkData___closed__4;
x_33 = x_31 + x_32;
x_34 = lean_uint64_of_nat(x_2);
x_35 = 40;
x_36 = x_34 << x_35;
x_37 = x_33 + x_36;
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; 
x_38 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__4;
x_39 = l_Lean_Expr_mkDataForLet___boxed__const__1;
x_40 = lean_panic_fn(x_39, x_38);
x_41 = lean_unbox_uint64(x_40);
lean_dec(x_40);
return x_41;
}
}
}
lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint64_t x_14; lean_object* x_15; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_Expr_mkDataForLet(x_8, x_2, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
x_15 = lean_box_uint64(x_14);
return x_15;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_instInhabitedUInt64___closed__1;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedExpr___closed__1;
return x_1;
}
}
lean_object* l_Lean_Expr_data_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
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
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_16 = lean_box_uint64(x_15);
x_17 = lean_apply_2(x_2, x_14, x_16);
return x_17;
}
case 1:
{
lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_20 = lean_box_uint64(x_19);
x_21 = lean_apply_2(x_3, x_18, x_20);
return x_21;
}
case 2:
{
lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_24 = lean_box_uint64(x_23);
x_25 = lean_apply_2(x_4, x_22, x_24);
return x_25;
}
case 3:
{
lean_object* x_26; uint64_t x_27; lean_object* x_28; lean_object* x_29; 
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
lean_dec(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_28 = lean_box_uint64(x_27);
x_29 = lean_apply_2(x_5, x_26, x_28);
return x_29;
}
case 4:
{
lean_object* x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; 
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
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_33 = lean_box_uint64(x_32);
x_34 = lean_apply_3(x_6, x_30, x_31, x_33);
return x_34;
}
case 5:
{
lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_38 = lean_box_uint64(x_37);
x_39 = lean_apply_3(x_7, x_35, x_36, x_38);
return x_39;
}
case 6:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
x_43 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_44 = lean_box_uint64(x_43);
x_45 = lean_apply_4(x_8, x_40, x_41, x_42, x_44);
return x_45;
}
case 7:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_50 = lean_box_uint64(x_49);
x_51 = lean_apply_4(x_9, x_46, x_47, x_48, x_50);
return x_51;
}
case 8:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint64_t x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_13);
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
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 3);
lean_inc(x_55);
x_56 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_57 = lean_box_uint64(x_56);
x_58 = lean_apply_5(x_10, x_52, x_53, x_54, x_55, x_57);
return x_58;
}
case 9:
{
lean_object* x_59; uint64_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
x_60 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_61 = lean_box_uint64(x_60);
x_62 = lean_apply_2(x_11, x_59, x_61);
return x_62;
}
case 10:
{
lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
x_65 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_66 = lean_box_uint64(x_65);
x_67 = lean_apply_3(x_12, x_63, x_64, x_66);
return x_67;
}
default: 
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint64_t x_71; lean_object* x_72; lean_object* x_73; 
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
lean_dec(x_2);
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_1, 2);
lean_inc(x_70);
x_71 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_72 = lean_box_uint64(x_71);
x_73 = lean_apply_4(x_13, x_68, x_69, x_70, x_72);
return x_73;
}
}
}
}
lean_object* l_Lean_Expr_data_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_data_match__1___rarg), 13, 0);
return x_2;
}
}
uint64_t l_Lean_Expr_data(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
uint64_t x_2; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
return x_2;
}
case 5:
{
uint64_t x_3; 
x_3 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
return x_3;
}
case 6:
{
uint64_t x_4; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
return x_4;
}
case 7:
{
uint64_t x_5; 
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
return x_5;
}
case 8:
{
uint64_t x_6; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
return x_6;
}
case 10:
{
uint64_t x_7; 
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
return x_7;
}
case 11:
{
uint64_t x_8; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
return x_8;
}
default: 
{
uint64_t x_9; 
x_9 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
return x_9;
}
}
}
}
lean_object* l_Lean_Expr_data___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_data(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_ctorName_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
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
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_16 = lean_box_uint64(x_15);
x_17 = lean_apply_2(x_2, x_14, x_16);
return x_17;
}
case 1:
{
lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_20 = lean_box_uint64(x_19);
x_21 = lean_apply_2(x_3, x_18, x_20);
return x_21;
}
case 2:
{
lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_24 = lean_box_uint64(x_23);
x_25 = lean_apply_2(x_4, x_22, x_24);
return x_25;
}
case 3:
{
lean_object* x_26; uint64_t x_27; lean_object* x_28; lean_object* x_29; 
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
lean_dec(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_28 = lean_box_uint64(x_27);
x_29 = lean_apply_2(x_5, x_26, x_28);
return x_29;
}
case 4:
{
lean_object* x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; 
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
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_33 = lean_box_uint64(x_32);
x_34 = lean_apply_3(x_6, x_30, x_31, x_33);
return x_34;
}
case 5:
{
lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_38 = lean_box_uint64(x_37);
x_39 = lean_apply_3(x_7, x_35, x_36, x_38);
return x_39;
}
case 6:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
x_43 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_44 = lean_box_uint64(x_43);
x_45 = lean_apply_4(x_8, x_40, x_41, x_42, x_44);
return x_45;
}
case 7:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_50 = lean_box_uint64(x_49);
x_51 = lean_apply_4(x_9, x_46, x_47, x_48, x_50);
return x_51;
}
case 8:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint64_t x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_13);
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
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 3);
lean_inc(x_55);
x_56 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_57 = lean_box_uint64(x_56);
x_58 = lean_apply_5(x_10, x_52, x_53, x_54, x_55, x_57);
return x_58;
}
case 9:
{
lean_object* x_59; uint64_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
x_60 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_61 = lean_box_uint64(x_60);
x_62 = lean_apply_2(x_11, x_59, x_61);
return x_62;
}
case 10:
{
lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
x_65 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_66 = lean_box_uint64(x_65);
x_67 = lean_apply_3(x_12, x_63, x_64, x_66);
return x_67;
}
default: 
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint64_t x_71; lean_object* x_72; lean_object* x_73; 
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
lean_dec(x_2);
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_1, 2);
lean_inc(x_70);
x_71 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_72 = lean_box_uint64(x_71);
x_73 = lean_apply_4(x_13, x_68, x_69, x_70, x_72);
return x_73;
}
}
}
}
lean_object* l_Lean_Expr_ctorName_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_ctorName_match__1___rarg), 13, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bvar");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fvar");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mvar");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("const");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lam");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("forallE");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("letE");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lit");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mdata");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("proj");
return x_1;
}
}
lean_object* l_Lean_Expr_ctorName(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_ctorName___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_ctorName___closed__2;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_ctorName___closed__3;
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1127____closed__32;
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_ctorName___closed__4;
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = l_myMacro____x40_Init_Notation___hyg_2094____closed__3;
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_ctorName___closed__5;
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_ctorName___closed__6;
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_ctorName___closed__7;
return x_10;
}
case 9:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_ctorName___closed__8;
return x_11;
}
case 10:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_ctorName___closed__9;
return x_12;
}
default: 
{
lean_object* x_13; 
x_13 = l_Lean_Expr_ctorName___closed__10;
return x_13;
}
}
}
}
lean_object* l_Lean_Expr_ctorName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_ctorName(x_1);
lean_dec(x_1);
return x_2;
}
}
size_t l_Lean_Expr_hash(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
uint64_t x_2; size_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_3 = l_Lean_Expr_Data_hash(x_2);
return x_3;
}
case 5:
{
uint64_t x_4; size_t x_5; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_5 = l_Lean_Expr_Data_hash(x_4);
return x_5;
}
case 6:
{
uint64_t x_6; size_t x_7; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_7 = l_Lean_Expr_Data_hash(x_6);
return x_7;
}
case 7:
{
uint64_t x_8; size_t x_9; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_9 = l_Lean_Expr_Data_hash(x_8);
return x_9;
}
case 8:
{
uint64_t x_10; size_t x_11; 
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_11 = l_Lean_Expr_Data_hash(x_10);
return x_11;
}
case 10:
{
uint64_t x_12; size_t x_13; 
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_13 = l_Lean_Expr_Data_hash(x_12);
return x_13;
}
case 11:
{
uint64_t x_14; size_t x_15; 
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_15 = l_Lean_Expr_Data_hash(x_14);
return x_15;
}
default: 
{
uint64_t x_16; size_t x_17; 
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_17 = l_Lean_Expr_Data_hash(x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Expr_hash___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_instHashableExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instHashableExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_instHashableExpr___closed__1;
return x_1;
}
}
uint8_t l_Lean_Expr_hasFVar(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
uint64_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_3 = l_Lean_Expr_Data_hasFVar(x_2);
return x_3;
}
case 5:
{
uint64_t x_4; uint8_t x_5; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_5 = l_Lean_Expr_Data_hasFVar(x_4);
return x_5;
}
case 6:
{
uint64_t x_6; uint8_t x_7; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_7 = l_Lean_Expr_Data_hasFVar(x_6);
return x_7;
}
case 7:
{
uint64_t x_8; uint8_t x_9; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_9 = l_Lean_Expr_Data_hasFVar(x_8);
return x_9;
}
case 8:
{
uint64_t x_10; uint8_t x_11; 
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_11 = l_Lean_Expr_Data_hasFVar(x_10);
return x_11;
}
case 10:
{
uint64_t x_12; uint8_t x_13; 
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_13 = l_Lean_Expr_Data_hasFVar(x_12);
return x_13;
}
case 11:
{
uint64_t x_14; uint8_t x_15; 
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_15 = l_Lean_Expr_Data_hasFVar(x_14);
return x_15;
}
default: 
{
uint64_t x_16; uint8_t x_17; 
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_17 = l_Lean_Expr_Data_hasFVar(x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Expr_hasFVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasFVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_hasExprMVar(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
uint64_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_3 = l_Lean_Expr_Data_hasExprMVar(x_2);
return x_3;
}
case 5:
{
uint64_t x_4; uint8_t x_5; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_5 = l_Lean_Expr_Data_hasExprMVar(x_4);
return x_5;
}
case 6:
{
uint64_t x_6; uint8_t x_7; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_7 = l_Lean_Expr_Data_hasExprMVar(x_6);
return x_7;
}
case 7:
{
uint64_t x_8; uint8_t x_9; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_9 = l_Lean_Expr_Data_hasExprMVar(x_8);
return x_9;
}
case 8:
{
uint64_t x_10; uint8_t x_11; 
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_11 = l_Lean_Expr_Data_hasExprMVar(x_10);
return x_11;
}
case 10:
{
uint64_t x_12; uint8_t x_13; 
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_13 = l_Lean_Expr_Data_hasExprMVar(x_12);
return x_13;
}
case 11:
{
uint64_t x_14; uint8_t x_15; 
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_15 = l_Lean_Expr_Data_hasExprMVar(x_14);
return x_15;
}
default: 
{
uint64_t x_16; uint8_t x_17; 
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_17 = l_Lean_Expr_Data_hasExprMVar(x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasExprMVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_hasLevelMVar(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
uint64_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_3 = l_Lean_Expr_Data_hasLevelMVar(x_2);
return x_3;
}
case 5:
{
uint64_t x_4; uint8_t x_5; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_5 = l_Lean_Expr_Data_hasLevelMVar(x_4);
return x_5;
}
case 6:
{
uint64_t x_6; uint8_t x_7; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_7 = l_Lean_Expr_Data_hasLevelMVar(x_6);
return x_7;
}
case 7:
{
uint64_t x_8; uint8_t x_9; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_9 = l_Lean_Expr_Data_hasLevelMVar(x_8);
return x_9;
}
case 8:
{
uint64_t x_10; uint8_t x_11; 
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_11 = l_Lean_Expr_Data_hasLevelMVar(x_10);
return x_11;
}
case 10:
{
uint64_t x_12; uint8_t x_13; 
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_13 = l_Lean_Expr_Data_hasLevelMVar(x_12);
return x_13;
}
case 11:
{
uint64_t x_14; uint8_t x_15; 
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_15 = l_Lean_Expr_Data_hasLevelMVar(x_14);
return x_15;
}
default: 
{
uint64_t x_16; uint8_t x_17; 
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_17 = l_Lean_Expr_Data_hasLevelMVar(x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasLevelMVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_hasMVar(lean_object* x_1) {
_start:
{
uint64_t x_2; 
switch (lean_obj_tag(x_1)) {
case 4:
{
uint64_t x_7; 
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_2 = x_7;
goto block_6;
}
case 5:
{
uint64_t x_8; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_2 = x_8;
goto block_6;
}
case 6:
{
uint64_t x_9; 
x_9 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_2 = x_9;
goto block_6;
}
case 7:
{
uint64_t x_10; 
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_2 = x_10;
goto block_6;
}
case 8:
{
uint64_t x_11; 
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_2 = x_11;
goto block_6;
}
case 10:
{
uint64_t x_12; 
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_2 = x_12;
goto block_6;
}
case 11:
{
uint64_t x_13; 
x_13 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_2 = x_13;
goto block_6;
}
default: 
{
uint64_t x_14; 
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_2 = x_14;
goto block_6;
}
}
block_6:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_Data_hasExprMVar(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Expr_Data_hasLevelMVar(x_2);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
}
}
}
lean_object* l_Lean_Expr_hasMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasMVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_hasLevelParam(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
uint64_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_3 = l_Lean_Expr_Data_hasLevelParam(x_2);
return x_3;
}
case 5:
{
uint64_t x_4; uint8_t x_5; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_5 = l_Lean_Expr_Data_hasLevelParam(x_4);
return x_5;
}
case 6:
{
uint64_t x_6; uint8_t x_7; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_7 = l_Lean_Expr_Data_hasLevelParam(x_6);
return x_7;
}
case 7:
{
uint64_t x_8; uint8_t x_9; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_9 = l_Lean_Expr_Data_hasLevelParam(x_8);
return x_9;
}
case 8:
{
uint64_t x_10; uint8_t x_11; 
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_11 = l_Lean_Expr_Data_hasLevelParam(x_10);
return x_11;
}
case 10:
{
uint64_t x_12; uint8_t x_13; 
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_13 = l_Lean_Expr_Data_hasLevelParam(x_12);
return x_13;
}
case 11:
{
uint64_t x_14; uint8_t x_15; 
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_15 = l_Lean_Expr_Data_hasLevelParam(x_14);
return x_15;
}
default: 
{
uint64_t x_16; uint8_t x_17; 
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_17 = l_Lean_Expr_Data_hasLevelParam(x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasLevelParam(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_looseBVarRange(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
uint64_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_3 = l_Lean_Expr_Data_looseBVarRange(x_2);
x_4 = lean_uint32_to_nat(x_3);
return x_4;
}
case 5:
{
uint64_t x_5; uint32_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_6 = l_Lean_Expr_Data_looseBVarRange(x_5);
x_7 = lean_uint32_to_nat(x_6);
return x_7;
}
case 6:
{
uint64_t x_8; uint32_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_9 = l_Lean_Expr_Data_looseBVarRange(x_8);
x_10 = lean_uint32_to_nat(x_9);
return x_10;
}
case 7:
{
uint64_t x_11; uint32_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_12 = l_Lean_Expr_Data_looseBVarRange(x_11);
x_13 = lean_uint32_to_nat(x_12);
return x_13;
}
case 8:
{
uint64_t x_14; uint32_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_15 = l_Lean_Expr_Data_looseBVarRange(x_14);
x_16 = lean_uint32_to_nat(x_15);
return x_16;
}
case 10:
{
uint64_t x_17; uint32_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_18 = l_Lean_Expr_Data_looseBVarRange(x_17);
x_19 = lean_uint32_to_nat(x_18);
return x_19;
}
case 11:
{
uint64_t x_20; uint32_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_21 = l_Lean_Expr_Data_looseBVarRange(x_20);
x_22 = lean_uint32_to_nat(x_21);
return x_22;
}
default: 
{
uint64_t x_23; uint32_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_24 = l_Lean_Expr_Data_looseBVarRange(x_23);
x_25 = lean_uint32_to_nat(x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_looseBVarRange(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_Expr_binderInfo(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
uint64_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_3 = (uint8_t)((x_2 << 24) >> 61);
return x_3;
}
case 5:
{
uint64_t x_4; uint8_t x_5; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_5 = (uint8_t)((x_4 << 24) >> 61);
return x_5;
}
case 6:
{
uint64_t x_6; uint8_t x_7; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_7 = (uint8_t)((x_6 << 24) >> 61);
return x_7;
}
case 7:
{
uint64_t x_8; uint8_t x_9; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_9 = (uint8_t)((x_8 << 24) >> 61);
return x_9;
}
case 8:
{
uint64_t x_10; uint8_t x_11; 
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_11 = (uint8_t)((x_10 << 24) >> 61);
return x_11;
}
case 10:
{
uint64_t x_12; uint8_t x_13; 
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_13 = (uint8_t)((x_12 << 24) >> 61);
return x_13;
}
case 11:
{
uint64_t x_14; uint8_t x_15; 
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_15 = (uint8_t)((x_14 << 24) >> 61);
return x_15;
}
default: 
{
uint64_t x_16; uint8_t x_17; 
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_17 = (uint8_t)((x_16 << 24) >> 61);
return x_17;
}
}
}
}
lean_object* l_Lean_Expr_binderInfo___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_binderInfo(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
size_t lean_expr_hash(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_hashEx___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_expr_hash(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
uint8_t lean_expr_has_fvar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_hasFVar(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_fvar(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t lean_expr_has_expr_mvar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_hasExprMVar(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_expr_mvar(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t lean_expr_has_level_mvar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_hasLevelMVar(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_level_mvar(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t lean_expr_has_mvar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_hasMVar(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_hasMVarEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_mvar(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t lean_expr_has_level_param(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_hasLevelParam(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_level_param(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint32_t lean_expr_loose_bvar_range(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
uint64_t x_2; uint32_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_looseBVarRange(x_2);
return x_3;
}
case 5:
{
uint64_t x_4; uint32_t x_5; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_5 = l_Lean_Expr_Data_looseBVarRange(x_4);
return x_5;
}
case 6:
{
uint64_t x_6; uint32_t x_7; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_7 = l_Lean_Expr_Data_looseBVarRange(x_6);
return x_7;
}
case 7:
{
uint64_t x_8; uint32_t x_9; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_9 = l_Lean_Expr_Data_looseBVarRange(x_8);
return x_9;
}
case 8:
{
uint64_t x_10; uint32_t x_11; 
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_11 = l_Lean_Expr_Data_looseBVarRange(x_10);
return x_11;
}
case 10:
{
uint64_t x_12; uint32_t x_13; 
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_13 = l_Lean_Expr_Data_looseBVarRange(x_12);
return x_13;
}
case 11:
{
uint64_t x_14; uint32_t x_15; 
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_15 = l_Lean_Expr_Data_looseBVarRange(x_14);
return x_15;
}
default: 
{
uint64_t x_16; uint32_t x_17; 
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_17 = l_Lean_Expr_Data_looseBVarRange(x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_expr_loose_bvar_range(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
uint8_t lean_expr_binder_info(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_binderInfo(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_binder_info(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_mkLit(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; size_t x_4; lean_object* x_5; uint8_t x_6; uint64_t x_7; lean_object* x_8; 
x_2 = 3;
x_3 = l_Lean_Literal_hash(x_1);
x_4 = lean_usize_mix_hash(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = l_Lean_Expr_mkData(x_4, x_5, x_6, x_6, x_6, x_6);
x_8 = lean_alloc_ctor(9, 1, 8);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set_uint64(x_8, sizeof(void*)*1, x_7);
return x_8;
}
}
lean_object* l_Lean_mkNatLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = l_Lean_mkLit(x_2);
return x_3;
}
}
lean_object* l_Lean_mkStrLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = l_Lean_mkLit(x_2);
return x_3;
}
}
size_t l_List_foldl___at_Lean_mkConst___spec__1(size_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_Level_hash(x_3);
x_6 = lean_usize_mix_hash(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
uint8_t l_List_foldr___at_Lean_mkConst___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldr___at_Lean_mkConst___spec__2(x_1, x_4);
x_6 = l_Lean_Level_hasMVar(x_3);
if (x_6 == 0)
{
return x_5;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
}
uint8_t l_List_foldr___at_Lean_mkConst___spec__3(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldr___at_Lean_mkConst___spec__3(x_1, x_4);
x_6 = l_Lean_Level_hasParam(x_3);
if (x_6 == 0)
{
return x_5;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
}
lean_object* l_Lean_mkConst(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; size_t x_6; size_t x_7; size_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; 
x_3 = 5;
x_4 = l_Lean_Name_hash(x_1);
x_5 = 7;
x_6 = l_List_foldl___at_Lean_mkConst___spec__1(x_5, x_2);
x_7 = lean_usize_mix_hash(x_4, x_6);
x_8 = lean_usize_mix_hash(x_3, x_7);
x_9 = 0;
x_10 = l_List_foldr___at_Lean_mkConst___spec__2(x_9, x_2);
x_11 = l_List_foldr___at_Lean_mkConst___spec__3(x_9, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_mkData(x_8, x_12, x_9, x_9, x_10, x_11);
x_14 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set_uint64(x_14, sizeof(void*)*2, x_13);
return x_14;
}
}
lean_object* l_List_foldl___at_Lean_mkConst___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_List_foldl___at_Lean_mkConst___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_usize(x_4);
return x_5;
}
}
lean_object* l_List_foldr___at_Lean_mkConst___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at_Lean_mkConst___spec__2(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_List_foldr___at_Lean_mkConst___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at_Lean_mkConst___spec__3(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_Literal_type_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
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
lean_object* l_Lean_Literal_type_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Literal_type_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Nat");
return x_1;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Literal_type___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Literal_type___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instQuoteSubstring___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Literal_type(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Literal_type___closed__3;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Literal_type___closed__4;
return x_3;
}
}
}
lean_object* l_Lean_Literal_type___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Literal_type(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* lean_lit_type(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Literal_type(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_mkBVar(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint64_t x_8; lean_object* x_9; 
x_2 = 7;
x_3 = lean_usize_of_nat(x_1);
x_4 = lean_usize_mix_hash(x_2, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_1, x_5);
x_7 = 0;
x_8 = l_Lean_Expr_mkData(x_4, x_6, x_7, x_7, x_7, x_7);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set_uint64(x_9, sizeof(void*)*1, x_8);
return x_9;
}
}
lean_object* l_Lean_mkSort(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; size_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; uint64_t x_9; lean_object* x_10; 
x_2 = 11;
x_3 = l_Lean_Level_hash(x_1);
x_4 = lean_usize_mix_hash(x_2, x_3);
x_5 = l_Lean_Level_hasMVar(x_1);
x_6 = l_Lean_Level_hasParam(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = 0;
x_9 = l_Lean_Expr_mkData(x_4, x_7, x_8, x_8, x_5, x_6);
x_10 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set_uint64(x_10, sizeof(void*)*1, x_9);
return x_10;
}
}
lean_object* l_Lean_mkFVar(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; size_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint64_t x_8; lean_object* x_9; 
x_2 = 13;
x_3 = l_Lean_Name_hash(x_1);
x_4 = lean_usize_mix_hash(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 1;
x_7 = 0;
x_8 = l_Lean_Expr_mkData(x_4, x_5, x_6, x_7, x_7, x_7);
x_9 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set_uint64(x_9, sizeof(void*)*1, x_8);
return x_9;
}
}
lean_object* l_Lean_mkMVar(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; size_t x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint64_t x_8; lean_object* x_9; 
x_2 = 17;
x_3 = l_Lean_Name_hash(x_1);
x_4 = lean_usize_mix_hash(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = 0;
x_7 = 1;
x_8 = l_Lean_Expr_mkData(x_4, x_5, x_6, x_7, x_6, x_6);
x_9 = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set_uint64(x_9, sizeof(void*)*1, x_8);
return x_9;
}
}
lean_object* l_Lean_mkMData(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint64_t x_11; lean_object* x_12; 
x_3 = 19;
x_4 = l_Lean_Expr_hash(x_2);
x_5 = lean_usize_mix_hash(x_3, x_4);
x_6 = l_Lean_Expr_looseBVarRange(x_2);
x_7 = l_Lean_Expr_hasFVar(x_2);
x_8 = l_Lean_Expr_hasExprMVar(x_2);
x_9 = l_Lean_Expr_hasLevelMVar(x_2);
x_10 = l_Lean_Expr_hasLevelParam(x_2);
x_11 = l_Lean_Expr_mkData(x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
x_12 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set_uint64(x_12, sizeof(void*)*2, x_11);
return x_12;
}
}
lean_object* l_Lean_mkProj(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; size_t x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint64_t x_16; lean_object* x_17; 
x_4 = 23;
x_5 = l_Lean_Name_hash(x_1);
x_6 = lean_usize_of_nat(x_2);
x_7 = l_Lean_Expr_hash(x_3);
x_8 = lean_usize_mix_hash(x_6, x_7);
x_9 = lean_usize_mix_hash(x_5, x_8);
x_10 = lean_usize_mix_hash(x_4, x_9);
x_11 = l_Lean_Expr_looseBVarRange(x_3);
x_12 = l_Lean_Expr_hasFVar(x_3);
x_13 = l_Lean_Expr_hasExprMVar(x_3);
x_14 = l_Lean_Expr_hasLevelMVar(x_3);
x_15 = l_Lean_Expr_hasLevelParam(x_3);
x_16 = l_Lean_Expr_mkData(x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_3);
lean_ctor_set_uint64(x_17, sizeof(void*)*3, x_16);
return x_17;
}
}
lean_object* l_Lean_mkApp(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_3 = 29;
x_4 = l_Lean_Expr_hash(x_1);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_usize_mix_hash(x_4, x_5);
x_7 = lean_usize_mix_hash(x_3, x_6);
x_8 = l_Lean_Expr_looseBVarRange(x_1);
x_9 = l_Lean_Expr_looseBVarRange(x_2);
x_10 = l_Nat_max(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Lean_Expr_hasFVar(x_1);
x_12 = l_Lean_Expr_hasExprMVar(x_1);
x_13 = l_Lean_Expr_hasLevelMVar(x_1);
x_14 = l_Lean_Expr_hasLevelParam(x_1);
if (x_11 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Expr_hasFVar(x_2);
if (x_12 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Expr_hasExprMVar(x_2);
if (x_13 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Expr_hasLevelMVar(x_2);
if (x_14 == 0)
{
uint8_t x_18; uint64_t x_19; lean_object* x_20; 
x_18 = l_Lean_Expr_hasLevelParam(x_2);
x_19 = l_Lean_Expr_mkData(x_7, x_10, x_15, x_16, x_17, x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set_uint64(x_20, sizeof(void*)*2, x_19);
return x_20;
}
else
{
uint8_t x_21; uint64_t x_22; lean_object* x_23; 
x_21 = 1;
x_22 = l_Lean_Expr_mkData(x_7, x_10, x_15, x_16, x_17, x_21);
lean_dec(x_10);
x_23 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set_uint64(x_23, sizeof(void*)*2, x_22);
return x_23;
}
}
else
{
if (x_14 == 0)
{
uint8_t x_24; uint8_t x_25; uint64_t x_26; lean_object* x_27; 
x_24 = l_Lean_Expr_hasLevelParam(x_2);
x_25 = 1;
x_26 = l_Lean_Expr_mkData(x_7, x_10, x_15, x_16, x_25, x_24);
lean_dec(x_10);
x_27 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set_uint64(x_27, sizeof(void*)*2, x_26);
return x_27;
}
else
{
uint8_t x_28; uint64_t x_29; lean_object* x_30; 
x_28 = 1;
x_29 = l_Lean_Expr_mkData(x_7, x_10, x_15, x_16, x_28, x_28);
lean_dec(x_10);
x_30 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set_uint64(x_30, sizeof(void*)*2, x_29);
return x_30;
}
}
}
else
{
if (x_13 == 0)
{
uint8_t x_31; 
x_31 = l_Lean_Expr_hasLevelMVar(x_2);
if (x_14 == 0)
{
uint8_t x_32; uint8_t x_33; uint64_t x_34; lean_object* x_35; 
x_32 = l_Lean_Expr_hasLevelParam(x_2);
x_33 = 1;
x_34 = l_Lean_Expr_mkData(x_7, x_10, x_15, x_33, x_31, x_32);
lean_dec(x_10);
x_35 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_2);
lean_ctor_set_uint64(x_35, sizeof(void*)*2, x_34);
return x_35;
}
else
{
uint8_t x_36; uint64_t x_37; lean_object* x_38; 
x_36 = 1;
x_37 = l_Lean_Expr_mkData(x_7, x_10, x_15, x_36, x_31, x_36);
lean_dec(x_10);
x_38 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_2);
lean_ctor_set_uint64(x_38, sizeof(void*)*2, x_37);
return x_38;
}
}
else
{
if (x_14 == 0)
{
uint8_t x_39; uint8_t x_40; uint64_t x_41; lean_object* x_42; 
x_39 = l_Lean_Expr_hasLevelParam(x_2);
x_40 = 1;
x_41 = l_Lean_Expr_mkData(x_7, x_10, x_15, x_40, x_40, x_39);
lean_dec(x_10);
x_42 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_2);
lean_ctor_set_uint64(x_42, sizeof(void*)*2, x_41);
return x_42;
}
else
{
uint8_t x_43; uint64_t x_44; lean_object* x_45; 
x_43 = 1;
x_44 = l_Lean_Expr_mkData(x_7, x_10, x_15, x_43, x_43, x_43);
lean_dec(x_10);
x_45 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_2);
lean_ctor_set_uint64(x_45, sizeof(void*)*2, x_44);
return x_45;
}
}
}
}
else
{
if (x_12 == 0)
{
uint8_t x_46; 
x_46 = l_Lean_Expr_hasExprMVar(x_2);
if (x_13 == 0)
{
uint8_t x_47; 
x_47 = l_Lean_Expr_hasLevelMVar(x_2);
if (x_14 == 0)
{
uint8_t x_48; uint8_t x_49; uint64_t x_50; lean_object* x_51; 
x_48 = l_Lean_Expr_hasLevelParam(x_2);
x_49 = 1;
x_50 = l_Lean_Expr_mkData(x_7, x_10, x_49, x_46, x_47, x_48);
lean_dec(x_10);
x_51 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_2);
lean_ctor_set_uint64(x_51, sizeof(void*)*2, x_50);
return x_51;
}
else
{
uint8_t x_52; uint64_t x_53; lean_object* x_54; 
x_52 = 1;
x_53 = l_Lean_Expr_mkData(x_7, x_10, x_52, x_46, x_47, x_52);
lean_dec(x_10);
x_54 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_2);
lean_ctor_set_uint64(x_54, sizeof(void*)*2, x_53);
return x_54;
}
}
else
{
if (x_14 == 0)
{
uint8_t x_55; uint8_t x_56; uint64_t x_57; lean_object* x_58; 
x_55 = l_Lean_Expr_hasLevelParam(x_2);
x_56 = 1;
x_57 = l_Lean_Expr_mkData(x_7, x_10, x_56, x_46, x_56, x_55);
lean_dec(x_10);
x_58 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_2);
lean_ctor_set_uint64(x_58, sizeof(void*)*2, x_57);
return x_58;
}
else
{
uint8_t x_59; uint64_t x_60; lean_object* x_61; 
x_59 = 1;
x_60 = l_Lean_Expr_mkData(x_7, x_10, x_59, x_46, x_59, x_59);
lean_dec(x_10);
x_61 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_2);
lean_ctor_set_uint64(x_61, sizeof(void*)*2, x_60);
return x_61;
}
}
}
else
{
if (x_13 == 0)
{
uint8_t x_62; 
x_62 = l_Lean_Expr_hasLevelMVar(x_2);
if (x_14 == 0)
{
uint8_t x_63; uint8_t x_64; uint64_t x_65; lean_object* x_66; 
x_63 = l_Lean_Expr_hasLevelParam(x_2);
x_64 = 1;
x_65 = l_Lean_Expr_mkData(x_7, x_10, x_64, x_64, x_62, x_63);
lean_dec(x_10);
x_66 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_2);
lean_ctor_set_uint64(x_66, sizeof(void*)*2, x_65);
return x_66;
}
else
{
uint8_t x_67; uint64_t x_68; lean_object* x_69; 
x_67 = 1;
x_68 = l_Lean_Expr_mkData(x_7, x_10, x_67, x_67, x_62, x_67);
lean_dec(x_10);
x_69 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_2);
lean_ctor_set_uint64(x_69, sizeof(void*)*2, x_68);
return x_69;
}
}
else
{
if (x_14 == 0)
{
uint8_t x_70; uint8_t x_71; uint64_t x_72; lean_object* x_73; 
x_70 = l_Lean_Expr_hasLevelParam(x_2);
x_71 = 1;
x_72 = l_Lean_Expr_mkData(x_7, x_10, x_71, x_71, x_71, x_70);
lean_dec(x_10);
x_73 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_2);
lean_ctor_set_uint64(x_73, sizeof(void*)*2, x_72);
return x_73;
}
else
{
uint8_t x_74; uint64_t x_75; lean_object* x_76; 
x_74 = 1;
x_75 = l_Lean_Expr_mkData(x_7, x_10, x_74, x_74, x_74, x_74);
lean_dec(x_10);
x_76 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_2);
lean_ctor_set_uint64(x_76, sizeof(void*)*2, x_75);
return x_76;
}
}
}
}
}
}
lean_object* l_Lean_mkLambda(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; 
x_5 = 31;
x_6 = l_Lean_Expr_hash(x_3);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = lean_usize_mix_hash(x_6, x_7);
x_9 = lean_usize_mix_hash(x_5, x_8);
x_10 = l_Lean_Expr_looseBVarRange(x_3);
x_11 = l_Lean_Expr_looseBVarRange(x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_14 = l_Nat_max(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
x_15 = l_Lean_Expr_hasFVar(x_3);
x_16 = l_Lean_Expr_hasExprMVar(x_3);
x_17 = l_Lean_Expr_hasLevelMVar(x_3);
x_18 = l_Lean_Expr_hasLevelParam(x_3);
if (x_15 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Expr_hasFVar(x_4);
if (x_16 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Expr_hasExprMVar(x_4);
if (x_17 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_18 == 0)
{
uint8_t x_22; uint64_t x_23; lean_object* x_24; 
x_22 = l_Lean_Expr_hasLevelParam(x_4);
x_23 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_19, x_20, x_21, x_22, x_2);
lean_dec(x_14);
x_24 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_4);
lean_ctor_set_uint64(x_24, sizeof(void*)*3, x_23);
return x_24;
}
else
{
uint8_t x_25; uint64_t x_26; lean_object* x_27; 
x_25 = 1;
x_26 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_19, x_20, x_21, x_25, x_2);
lean_dec(x_14);
x_27 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_3);
lean_ctor_set(x_27, 2, x_4);
lean_ctor_set_uint64(x_27, sizeof(void*)*3, x_26);
return x_27;
}
}
else
{
if (x_18 == 0)
{
uint8_t x_28; uint8_t x_29; uint64_t x_30; lean_object* x_31; 
x_28 = l_Lean_Expr_hasLevelParam(x_4);
x_29 = 1;
x_30 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_19, x_20, x_29, x_28, x_2);
lean_dec(x_14);
x_31 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 2, x_4);
lean_ctor_set_uint64(x_31, sizeof(void*)*3, x_30);
return x_31;
}
else
{
uint8_t x_32; uint64_t x_33; lean_object* x_34; 
x_32 = 1;
x_33 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_19, x_20, x_32, x_32, x_2);
lean_dec(x_14);
x_34 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_3);
lean_ctor_set(x_34, 2, x_4);
lean_ctor_set_uint64(x_34, sizeof(void*)*3, x_33);
return x_34;
}
}
}
else
{
if (x_17 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_18 == 0)
{
uint8_t x_36; uint8_t x_37; uint64_t x_38; lean_object* x_39; 
x_36 = l_Lean_Expr_hasLevelParam(x_4);
x_37 = 1;
x_38 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_19, x_37, x_35, x_36, x_2);
lean_dec(x_14);
x_39 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_3);
lean_ctor_set(x_39, 2, x_4);
lean_ctor_set_uint64(x_39, sizeof(void*)*3, x_38);
return x_39;
}
else
{
uint8_t x_40; uint64_t x_41; lean_object* x_42; 
x_40 = 1;
x_41 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_19, x_40, x_35, x_40, x_2);
lean_dec(x_14);
x_42 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_3);
lean_ctor_set(x_42, 2, x_4);
lean_ctor_set_uint64(x_42, sizeof(void*)*3, x_41);
return x_42;
}
}
else
{
if (x_18 == 0)
{
uint8_t x_43; uint8_t x_44; uint64_t x_45; lean_object* x_46; 
x_43 = l_Lean_Expr_hasLevelParam(x_4);
x_44 = 1;
x_45 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_19, x_44, x_44, x_43, x_2);
lean_dec(x_14);
x_46 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_3);
lean_ctor_set(x_46, 2, x_4);
lean_ctor_set_uint64(x_46, sizeof(void*)*3, x_45);
return x_46;
}
else
{
uint8_t x_47; uint64_t x_48; lean_object* x_49; 
x_47 = 1;
x_48 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_19, x_47, x_47, x_47, x_2);
lean_dec(x_14);
x_49 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_3);
lean_ctor_set(x_49, 2, x_4);
lean_ctor_set_uint64(x_49, sizeof(void*)*3, x_48);
return x_49;
}
}
}
}
else
{
if (x_16 == 0)
{
uint8_t x_50; 
x_50 = l_Lean_Expr_hasExprMVar(x_4);
if (x_17 == 0)
{
uint8_t x_51; 
x_51 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_18 == 0)
{
uint8_t x_52; uint8_t x_53; uint64_t x_54; lean_object* x_55; 
x_52 = l_Lean_Expr_hasLevelParam(x_4);
x_53 = 1;
x_54 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_53, x_50, x_51, x_52, x_2);
lean_dec(x_14);
x_55 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_3);
lean_ctor_set(x_55, 2, x_4);
lean_ctor_set_uint64(x_55, sizeof(void*)*3, x_54);
return x_55;
}
else
{
uint8_t x_56; uint64_t x_57; lean_object* x_58; 
x_56 = 1;
x_57 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_56, x_50, x_51, x_56, x_2);
lean_dec(x_14);
x_58 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_3);
lean_ctor_set(x_58, 2, x_4);
lean_ctor_set_uint64(x_58, sizeof(void*)*3, x_57);
return x_58;
}
}
else
{
if (x_18 == 0)
{
uint8_t x_59; uint8_t x_60; uint64_t x_61; lean_object* x_62; 
x_59 = l_Lean_Expr_hasLevelParam(x_4);
x_60 = 1;
x_61 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_60, x_50, x_60, x_59, x_2);
lean_dec(x_14);
x_62 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_3);
lean_ctor_set(x_62, 2, x_4);
lean_ctor_set_uint64(x_62, sizeof(void*)*3, x_61);
return x_62;
}
else
{
uint8_t x_63; uint64_t x_64; lean_object* x_65; 
x_63 = 1;
x_64 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_63, x_50, x_63, x_63, x_2);
lean_dec(x_14);
x_65 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_3);
lean_ctor_set(x_65, 2, x_4);
lean_ctor_set_uint64(x_65, sizeof(void*)*3, x_64);
return x_65;
}
}
}
else
{
if (x_17 == 0)
{
uint8_t x_66; 
x_66 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_18 == 0)
{
uint8_t x_67; uint8_t x_68; uint64_t x_69; lean_object* x_70; 
x_67 = l_Lean_Expr_hasLevelParam(x_4);
x_68 = 1;
x_69 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_68, x_68, x_66, x_67, x_2);
lean_dec(x_14);
x_70 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_3);
lean_ctor_set(x_70, 2, x_4);
lean_ctor_set_uint64(x_70, sizeof(void*)*3, x_69);
return x_70;
}
else
{
uint8_t x_71; uint64_t x_72; lean_object* x_73; 
x_71 = 1;
x_72 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_71, x_71, x_66, x_71, x_2);
lean_dec(x_14);
x_73 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_3);
lean_ctor_set(x_73, 2, x_4);
lean_ctor_set_uint64(x_73, sizeof(void*)*3, x_72);
return x_73;
}
}
else
{
if (x_18 == 0)
{
uint8_t x_74; uint8_t x_75; uint64_t x_76; lean_object* x_77; 
x_74 = l_Lean_Expr_hasLevelParam(x_4);
x_75 = 1;
x_76 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_75, x_75, x_75, x_74, x_2);
lean_dec(x_14);
x_77 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_3);
lean_ctor_set(x_77, 2, x_4);
lean_ctor_set_uint64(x_77, sizeof(void*)*3, x_76);
return x_77;
}
else
{
uint8_t x_78; uint64_t x_79; lean_object* x_80; 
x_78 = 1;
x_79 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_78, x_78, x_78, x_78, x_2);
lean_dec(x_14);
x_80 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_3);
lean_ctor_set(x_80, 2, x_4);
lean_ctor_set_uint64(x_80, sizeof(void*)*3, x_79);
return x_80;
}
}
}
}
}
}
lean_object* l_Lean_mkLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_mkLambda(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_mkForall(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; 
x_5 = 37;
x_6 = l_Lean_Expr_hash(x_3);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = lean_usize_mix_hash(x_6, x_7);
x_9 = lean_usize_mix_hash(x_5, x_8);
x_10 = l_Lean_Expr_looseBVarRange(x_3);
x_11 = l_Lean_Expr_looseBVarRange(x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_14 = l_Nat_max(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
x_15 = l_Lean_Expr_hasFVar(x_3);
x_16 = l_Lean_Expr_hasExprMVar(x_3);
x_17 = l_Lean_Expr_hasLevelMVar(x_3);
x_18 = l_Lean_Expr_hasLevelParam(x_3);
if (x_15 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Expr_hasFVar(x_4);
if (x_16 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Expr_hasExprMVar(x_4);
if (x_17 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_18 == 0)
{
uint8_t x_22; uint64_t x_23; lean_object* x_24; 
x_22 = l_Lean_Expr_hasLevelParam(x_4);
x_23 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_19, x_20, x_21, x_22, x_2);
lean_dec(x_14);
x_24 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_4);
lean_ctor_set_uint64(x_24, sizeof(void*)*3, x_23);
return x_24;
}
else
{
uint8_t x_25; uint64_t x_26; lean_object* x_27; 
x_25 = 1;
x_26 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_19, x_20, x_21, x_25, x_2);
lean_dec(x_14);
x_27 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_3);
lean_ctor_set(x_27, 2, x_4);
lean_ctor_set_uint64(x_27, sizeof(void*)*3, x_26);
return x_27;
}
}
else
{
if (x_18 == 0)
{
uint8_t x_28; uint8_t x_29; uint64_t x_30; lean_object* x_31; 
x_28 = l_Lean_Expr_hasLevelParam(x_4);
x_29 = 1;
x_30 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_19, x_20, x_29, x_28, x_2);
lean_dec(x_14);
x_31 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 2, x_4);
lean_ctor_set_uint64(x_31, sizeof(void*)*3, x_30);
return x_31;
}
else
{
uint8_t x_32; uint64_t x_33; lean_object* x_34; 
x_32 = 1;
x_33 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_19, x_20, x_32, x_32, x_2);
lean_dec(x_14);
x_34 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_3);
lean_ctor_set(x_34, 2, x_4);
lean_ctor_set_uint64(x_34, sizeof(void*)*3, x_33);
return x_34;
}
}
}
else
{
if (x_17 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_18 == 0)
{
uint8_t x_36; uint8_t x_37; uint64_t x_38; lean_object* x_39; 
x_36 = l_Lean_Expr_hasLevelParam(x_4);
x_37 = 1;
x_38 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_19, x_37, x_35, x_36, x_2);
lean_dec(x_14);
x_39 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_3);
lean_ctor_set(x_39, 2, x_4);
lean_ctor_set_uint64(x_39, sizeof(void*)*3, x_38);
return x_39;
}
else
{
uint8_t x_40; uint64_t x_41; lean_object* x_42; 
x_40 = 1;
x_41 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_19, x_40, x_35, x_40, x_2);
lean_dec(x_14);
x_42 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_3);
lean_ctor_set(x_42, 2, x_4);
lean_ctor_set_uint64(x_42, sizeof(void*)*3, x_41);
return x_42;
}
}
else
{
if (x_18 == 0)
{
uint8_t x_43; uint8_t x_44; uint64_t x_45; lean_object* x_46; 
x_43 = l_Lean_Expr_hasLevelParam(x_4);
x_44 = 1;
x_45 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_19, x_44, x_44, x_43, x_2);
lean_dec(x_14);
x_46 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_3);
lean_ctor_set(x_46, 2, x_4);
lean_ctor_set_uint64(x_46, sizeof(void*)*3, x_45);
return x_46;
}
else
{
uint8_t x_47; uint64_t x_48; lean_object* x_49; 
x_47 = 1;
x_48 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_19, x_47, x_47, x_47, x_2);
lean_dec(x_14);
x_49 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_3);
lean_ctor_set(x_49, 2, x_4);
lean_ctor_set_uint64(x_49, sizeof(void*)*3, x_48);
return x_49;
}
}
}
}
else
{
if (x_16 == 0)
{
uint8_t x_50; 
x_50 = l_Lean_Expr_hasExprMVar(x_4);
if (x_17 == 0)
{
uint8_t x_51; 
x_51 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_18 == 0)
{
uint8_t x_52; uint8_t x_53; uint64_t x_54; lean_object* x_55; 
x_52 = l_Lean_Expr_hasLevelParam(x_4);
x_53 = 1;
x_54 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_53, x_50, x_51, x_52, x_2);
lean_dec(x_14);
x_55 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_3);
lean_ctor_set(x_55, 2, x_4);
lean_ctor_set_uint64(x_55, sizeof(void*)*3, x_54);
return x_55;
}
else
{
uint8_t x_56; uint64_t x_57; lean_object* x_58; 
x_56 = 1;
x_57 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_56, x_50, x_51, x_56, x_2);
lean_dec(x_14);
x_58 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_3);
lean_ctor_set(x_58, 2, x_4);
lean_ctor_set_uint64(x_58, sizeof(void*)*3, x_57);
return x_58;
}
}
else
{
if (x_18 == 0)
{
uint8_t x_59; uint8_t x_60; uint64_t x_61; lean_object* x_62; 
x_59 = l_Lean_Expr_hasLevelParam(x_4);
x_60 = 1;
x_61 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_60, x_50, x_60, x_59, x_2);
lean_dec(x_14);
x_62 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_3);
lean_ctor_set(x_62, 2, x_4);
lean_ctor_set_uint64(x_62, sizeof(void*)*3, x_61);
return x_62;
}
else
{
uint8_t x_63; uint64_t x_64; lean_object* x_65; 
x_63 = 1;
x_64 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_63, x_50, x_63, x_63, x_2);
lean_dec(x_14);
x_65 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_3);
lean_ctor_set(x_65, 2, x_4);
lean_ctor_set_uint64(x_65, sizeof(void*)*3, x_64);
return x_65;
}
}
}
else
{
if (x_17 == 0)
{
uint8_t x_66; 
x_66 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_18 == 0)
{
uint8_t x_67; uint8_t x_68; uint64_t x_69; lean_object* x_70; 
x_67 = l_Lean_Expr_hasLevelParam(x_4);
x_68 = 1;
x_69 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_68, x_68, x_66, x_67, x_2);
lean_dec(x_14);
x_70 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_3);
lean_ctor_set(x_70, 2, x_4);
lean_ctor_set_uint64(x_70, sizeof(void*)*3, x_69);
return x_70;
}
else
{
uint8_t x_71; uint64_t x_72; lean_object* x_73; 
x_71 = 1;
x_72 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_71, x_71, x_66, x_71, x_2);
lean_dec(x_14);
x_73 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_3);
lean_ctor_set(x_73, 2, x_4);
lean_ctor_set_uint64(x_73, sizeof(void*)*3, x_72);
return x_73;
}
}
else
{
if (x_18 == 0)
{
uint8_t x_74; uint8_t x_75; uint64_t x_76; lean_object* x_77; 
x_74 = l_Lean_Expr_hasLevelParam(x_4);
x_75 = 1;
x_76 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_75, x_75, x_75, x_74, x_2);
lean_dec(x_14);
x_77 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_3);
lean_ctor_set(x_77, 2, x_4);
lean_ctor_set_uint64(x_77, sizeof(void*)*3, x_76);
return x_77;
}
else
{
uint8_t x_78; uint64_t x_79; lean_object* x_80; 
x_78 = 1;
x_79 = l_Lean_Expr_mkDataForBinder(x_9, x_14, x_78, x_78, x_78, x_78, x_2);
lean_dec(x_14);
x_80 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_3);
lean_ctor_set(x_80, 2, x_4);
lean_ctor_set_uint64(x_80, sizeof(void*)*3, x_79);
return x_80;
}
}
}
}
}
}
lean_object* l_Lean_mkForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_mkForall(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_myMacro____x40_Init_System_IO___hyg_2501____closed__17;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_mkSimpleThunkType(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = 0;
x_4 = l_Lean_mkSimpleThunkType___closed__1;
x_5 = l_Lean_mkForall(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_mkSimpleThunk___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_myMacro____x40_Init_Notation___hyg_11811____closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkSimpleThunk(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_mkSimpleThunk___closed__1;
x_3 = 0;
x_4 = l_Lean_mkSimpleThunkType___closed__1;
x_5 = l_Lean_mkLambda(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_mkLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
size_t x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; 
x_6 = 41;
x_7 = l_Lean_Expr_hash(x_2);
x_8 = l_Lean_Expr_hash(x_3);
x_9 = l_Lean_Expr_hash(x_4);
x_10 = lean_usize_mix_hash(x_8, x_9);
x_11 = lean_usize_mix_hash(x_7, x_10);
x_12 = lean_usize_mix_hash(x_6, x_11);
x_13 = l_Lean_Expr_looseBVarRange(x_2);
x_14 = l_Lean_Expr_looseBVarRange(x_3);
x_15 = l_Nat_max(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_16 = l_Lean_Expr_looseBVarRange(x_4);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_19 = l_Nat_max(x_15, x_18);
lean_dec(x_18);
lean_dec(x_15);
x_20 = l_Lean_Expr_hasFVar(x_2);
x_21 = l_Lean_Expr_hasExprMVar(x_2);
x_22 = l_Lean_Expr_hasLevelMVar(x_2);
x_23 = l_Lean_Expr_hasLevelParam(x_2);
if (x_20 == 0)
{
uint8_t x_88; 
x_88 = l_Lean_Expr_hasFVar(x_3);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = l_Lean_Expr_hasFVar(x_4);
x_24 = x_89;
goto block_87;
}
else
{
uint8_t x_90; 
x_90 = 1;
x_24 = x_90;
goto block_87;
}
}
else
{
uint8_t x_91; 
x_91 = 1;
x_24 = x_91;
goto block_87;
}
block_87:
{
uint8_t x_25; 
if (x_21 == 0)
{
uint8_t x_50; 
x_50 = l_Lean_Expr_hasExprMVar(x_3);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = l_Lean_Expr_hasExprMVar(x_4);
if (x_22 == 0)
{
x_25 = x_51;
goto block_49;
}
else
{
if (x_23 == 0)
{
uint8_t x_52; 
x_52 = l_Lean_Expr_hasLevelParam(x_3);
if (x_52 == 0)
{
uint8_t x_53; uint8_t x_54; uint64_t x_55; lean_object* x_56; 
x_53 = l_Lean_Expr_hasLevelParam(x_4);
x_54 = 1;
x_55 = l_Lean_Expr_mkDataForLet(x_12, x_19, x_24, x_51, x_54, x_53, x_5);
lean_dec(x_19);
x_56 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_2);
lean_ctor_set(x_56, 2, x_3);
lean_ctor_set(x_56, 3, x_4);
lean_ctor_set_uint64(x_56, sizeof(void*)*4, x_55);
return x_56;
}
else
{
uint8_t x_57; uint64_t x_58; lean_object* x_59; 
x_57 = 1;
x_58 = l_Lean_Expr_mkDataForLet(x_12, x_19, x_24, x_51, x_57, x_57, x_5);
lean_dec(x_19);
x_59 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_2);
lean_ctor_set(x_59, 2, x_3);
lean_ctor_set(x_59, 3, x_4);
lean_ctor_set_uint64(x_59, sizeof(void*)*4, x_58);
return x_59;
}
}
else
{
uint8_t x_60; uint64_t x_61; lean_object* x_62; 
x_60 = 1;
x_61 = l_Lean_Expr_mkDataForLet(x_12, x_19, x_24, x_51, x_60, x_60, x_5);
lean_dec(x_19);
x_62 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_2);
lean_ctor_set(x_62, 2, x_3);
lean_ctor_set(x_62, 3, x_4);
lean_ctor_set_uint64(x_62, sizeof(void*)*4, x_61);
return x_62;
}
}
}
else
{
if (x_22 == 0)
{
uint8_t x_63; 
x_63 = 1;
x_25 = x_63;
goto block_49;
}
else
{
if (x_23 == 0)
{
uint8_t x_64; 
x_64 = l_Lean_Expr_hasLevelParam(x_3);
if (x_64 == 0)
{
uint8_t x_65; uint8_t x_66; uint64_t x_67; lean_object* x_68; 
x_65 = l_Lean_Expr_hasLevelParam(x_4);
x_66 = 1;
x_67 = l_Lean_Expr_mkDataForLet(x_12, x_19, x_24, x_66, x_66, x_65, x_5);
lean_dec(x_19);
x_68 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_2);
lean_ctor_set(x_68, 2, x_3);
lean_ctor_set(x_68, 3, x_4);
lean_ctor_set_uint64(x_68, sizeof(void*)*4, x_67);
return x_68;
}
else
{
uint8_t x_69; uint64_t x_70; lean_object* x_71; 
x_69 = 1;
x_70 = l_Lean_Expr_mkDataForLet(x_12, x_19, x_24, x_69, x_69, x_69, x_5);
lean_dec(x_19);
x_71 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_2);
lean_ctor_set(x_71, 2, x_3);
lean_ctor_set(x_71, 3, x_4);
lean_ctor_set_uint64(x_71, sizeof(void*)*4, x_70);
return x_71;
}
}
else
{
uint8_t x_72; uint64_t x_73; lean_object* x_74; 
x_72 = 1;
x_73 = l_Lean_Expr_mkDataForLet(x_12, x_19, x_24, x_72, x_72, x_72, x_5);
lean_dec(x_19);
x_74 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_2);
lean_ctor_set(x_74, 2, x_3);
lean_ctor_set(x_74, 3, x_4);
lean_ctor_set_uint64(x_74, sizeof(void*)*4, x_73);
return x_74;
}
}
}
}
else
{
if (x_22 == 0)
{
uint8_t x_75; 
x_75 = 1;
x_25 = x_75;
goto block_49;
}
else
{
if (x_23 == 0)
{
uint8_t x_76; 
x_76 = l_Lean_Expr_hasLevelParam(x_3);
if (x_76 == 0)
{
uint8_t x_77; uint8_t x_78; uint64_t x_79; lean_object* x_80; 
x_77 = l_Lean_Expr_hasLevelParam(x_4);
x_78 = 1;
x_79 = l_Lean_Expr_mkDataForLet(x_12, x_19, x_24, x_78, x_78, x_77, x_5);
lean_dec(x_19);
x_80 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_2);
lean_ctor_set(x_80, 2, x_3);
lean_ctor_set(x_80, 3, x_4);
lean_ctor_set_uint64(x_80, sizeof(void*)*4, x_79);
return x_80;
}
else
{
uint8_t x_81; uint64_t x_82; lean_object* x_83; 
x_81 = 1;
x_82 = l_Lean_Expr_mkDataForLet(x_12, x_19, x_24, x_81, x_81, x_81, x_5);
lean_dec(x_19);
x_83 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_2);
lean_ctor_set(x_83, 2, x_3);
lean_ctor_set(x_83, 3, x_4);
lean_ctor_set_uint64(x_83, sizeof(void*)*4, x_82);
return x_83;
}
}
else
{
uint8_t x_84; uint64_t x_85; lean_object* x_86; 
x_84 = 1;
x_85 = l_Lean_Expr_mkDataForLet(x_12, x_19, x_24, x_84, x_84, x_84, x_5);
lean_dec(x_19);
x_86 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_2);
lean_ctor_set(x_86, 2, x_3);
lean_ctor_set(x_86, 3, x_4);
lean_ctor_set_uint64(x_86, sizeof(void*)*4, x_85);
return x_86;
}
}
}
block_49:
{
uint8_t x_26; 
x_26 = l_Lean_Expr_hasLevelMVar(x_3);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_23 == 0)
{
uint8_t x_28; 
x_28 = l_Lean_Expr_hasLevelParam(x_3);
if (x_28 == 0)
{
uint8_t x_29; uint64_t x_30; lean_object* x_31; 
x_29 = l_Lean_Expr_hasLevelParam(x_4);
x_30 = l_Lean_Expr_mkDataForLet(x_12, x_19, x_24, x_25, x_27, x_29, x_5);
lean_dec(x_19);
x_31 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_2);
lean_ctor_set(x_31, 2, x_3);
lean_ctor_set(x_31, 3, x_4);
lean_ctor_set_uint64(x_31, sizeof(void*)*4, x_30);
return x_31;
}
else
{
uint8_t x_32; uint64_t x_33; lean_object* x_34; 
x_32 = 1;
x_33 = l_Lean_Expr_mkDataForLet(x_12, x_19, x_24, x_25, x_27, x_32, x_5);
lean_dec(x_19);
x_34 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_2);
lean_ctor_set(x_34, 2, x_3);
lean_ctor_set(x_34, 3, x_4);
lean_ctor_set_uint64(x_34, sizeof(void*)*4, x_33);
return x_34;
}
}
else
{
uint8_t x_35; uint64_t x_36; lean_object* x_37; 
x_35 = 1;
x_36 = l_Lean_Expr_mkDataForLet(x_12, x_19, x_24, x_25, x_27, x_35, x_5);
lean_dec(x_19);
x_37 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_2);
lean_ctor_set(x_37, 2, x_3);
lean_ctor_set(x_37, 3, x_4);
lean_ctor_set_uint64(x_37, sizeof(void*)*4, x_36);
return x_37;
}
}
else
{
if (x_23 == 0)
{
uint8_t x_38; 
x_38 = l_Lean_Expr_hasLevelParam(x_3);
if (x_38 == 0)
{
uint8_t x_39; uint8_t x_40; uint64_t x_41; lean_object* x_42; 
x_39 = l_Lean_Expr_hasLevelParam(x_4);
x_40 = 1;
x_41 = l_Lean_Expr_mkDataForLet(x_12, x_19, x_24, x_25, x_40, x_39, x_5);
lean_dec(x_19);
x_42 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_2);
lean_ctor_set(x_42, 2, x_3);
lean_ctor_set(x_42, 3, x_4);
lean_ctor_set_uint64(x_42, sizeof(void*)*4, x_41);
return x_42;
}
else
{
uint8_t x_43; uint64_t x_44; lean_object* x_45; 
x_43 = 1;
x_44 = l_Lean_Expr_mkDataForLet(x_12, x_19, x_24, x_25, x_43, x_43, x_5);
lean_dec(x_19);
x_45 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_2);
lean_ctor_set(x_45, 2, x_3);
lean_ctor_set(x_45, 3, x_4);
lean_ctor_set_uint64(x_45, sizeof(void*)*4, x_44);
return x_45;
}
}
else
{
uint8_t x_46; uint64_t x_47; lean_object* x_48; 
x_46 = 1;
x_47 = l_Lean_Expr_mkDataForLet(x_12, x_19, x_24, x_25, x_46, x_46, x_5);
lean_dec(x_19);
x_48 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_2);
lean_ctor_set(x_48, 2, x_3);
lean_ctor_set(x_48, 3, x_4);
lean_ctor_set_uint64(x_48, sizeof(void*)*4, x_47);
return x_48;
}
}
}
}
}
}
lean_object* l_Lean_mkLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_mkLet(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
lean_object* lean_expr_mk_bvar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkBVar(x_1);
return x_2;
}
}
lean_object* lean_expr_mk_fvar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkFVar(x_1);
return x_2;
}
}
lean_object* lean_expr_mk_mvar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkMVar(x_1);
return x_2;
}
}
lean_object* lean_expr_mk_sort(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
lean_object* lean_expr_mk_const(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkConst(x_1, x_2);
return x_3;
}
}
lean_object* lean_expr_mk_app(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkApp(x_1, x_2);
return x_3;
}
}
lean_object* lean_expr_mk_lambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkLambda(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_mkLambdaEx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = lean_expr_mk_lambda(x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* lean_expr_mk_forall(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkForall(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_mkForallEx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = lean_expr_mk_forall(x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* lean_expr_mk_let(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = l_Lean_mkLet(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* lean_expr_mk_lit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkLit(x_1);
return x_2;
}
}
lean_object* lean_expr_mk_mdata(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkMData(x_1, x_2);
return x_3;
}
}
lean_object* lean_expr_mk_proj(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkProj(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkAppN___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_mkApp(x_4, x_6);
x_8 = 1;
x_9 = x_2 + x_8;
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
lean_object* l_Lean_mkAppN(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_mkAppN___spec__1(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkAppN___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_mkAppN___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_mkAppN___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkAppN(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_1);
if (x_5 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
x_8 = l_Lean_instInhabitedExpr;
x_9 = lean_array_get(x_8, x_2, x_3);
lean_dec(x_3);
x_10 = l_Lean_mkApp(x_4, x_9);
x_3 = x_7;
x_4 = x_10;
goto _start;
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_mkAppRange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_3, x_4, x_2, x_1);
return x_5;
}
}
lean_object* l_Lean_mkAppRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkAppRange(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_mkAppRev___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = x_2 - x_6;
x_8 = lean_array_uget(x_1, x_7);
x_9 = l_Lean_mkApp(x_4, x_8);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
lean_object* l_Lean_mkAppRev(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_7 = 0;
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_mkAppRev___spec__1(x_2, x_6, x_7, x_1);
return x_8;
}
}
}
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_mkAppRev___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at_Lean_mkAppRev___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_mkAppRev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkAppRev(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_quickLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_expr_quick_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_expr_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_eqv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Expr_instBEqExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_eqv___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instBEqExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_instBEqExpr___closed__1;
return x_1;
}
}
lean_object* l_Lean_Expr_equal___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_expr_equal(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_isSort_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Expr_isSort_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isSort_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isSort(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isSort___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isSort(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_isProp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint64_t x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_ctor_get_uint64(x_4, 0);
lean_dec(x_4);
x_7 = lean_box_uint64(x_6);
x_8 = lean_box_uint64(x_5);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_apply_1(x_3, x_1);
return x_11;
}
}
}
lean_object* l_Lean_Expr_isProp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isProp_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isProp(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
lean_object* l_Lean_Expr_isProp___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isProp(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_isBVar_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Expr_isBVar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isBVar_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isBVar(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isBVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isBVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_isMVar_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Expr_isMVar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isMVar_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isMVar(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isMVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_isFVar_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Expr_isFVar_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isFVar_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isFVar(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isFVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isFVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_isApp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
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
lean_object* l_Lean_Expr_isApp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isApp_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isApp(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isApp___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isApp(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_isProj_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 11)
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
lean_object* l_Lean_Expr_isProj_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isProj_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isProj(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isProj___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isProj(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_isConst_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Expr_isConst_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isConst_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isConst(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isConst___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isConst(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_isConstOf_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_3, x_5, x_6, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_4, x_1, x_2);
return x_10;
}
}
}
lean_object* l_Lean_Expr_isConstOf_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isConstOf_match__1___rarg), 4, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isConstOf(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_name_eq(x_3, x_2);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
lean_object* l_Lean_Expr_isConstOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_isConstOf(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_isForall_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Expr_isForall_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isForall_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isForall(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isForall___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isForall(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_isLambda_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 6)
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
lean_object* l_Lean_Expr_isLambda_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isLambda_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isLambda(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isLambda___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isLambda(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_isBinding_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_4(x_2, x_5, x_6, x_7, x_9);
return x_10;
}
case 7:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_15 = lean_box_uint64(x_14);
x_16 = lean_apply_4(x_3, x_11, x_12, x_13, x_15);
return x_16;
}
default: 
{
lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_apply_1(x_4, x_1);
return x_17;
}
}
}
}
lean_object* l_Lean_Expr_isBinding_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isBinding_match__1___rarg), 4, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isBinding(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 7:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
default: 
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
}
lean_object* l_Lean_Expr_isBinding___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isBinding(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_isLet_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_apply_1(x_3, x_1);
return x_11;
}
}
}
lean_object* l_Lean_Expr_isLet_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isLet_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isLet(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isLet___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isLet(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_isMData_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 10)
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
lean_object* l_Lean_Expr_isMData_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isMData_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isMData(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isMData___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isMData(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_isLit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Expr_isLit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isLit_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isLit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isLit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isLit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_getAppFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
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
lean_object* l_Lean_Expr_getAppFn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_getAppFn_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_getAppFn(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
x_1 = x_2;
goto _start;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_getAppNumArgsAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_3, x_5, x_6, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_4, x_1, x_2);
return x_10;
}
}
}
lean_object* l_Lean_Expr_getAppNumArgsAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_getAppNumArgsAux_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_3;
x_2 = x_5;
goto _start;
}
else
{
return x_2;
}
}
}
lean_object* l_Lean_Expr_getAppNumArgsAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppNumArgsAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_getAppNumArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Expr_getAppNumArgsAux(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAppNumArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_5(x_4, x_6, x_7, x_9, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_apply_3(x_5, x_1, x_2, x_3);
return x_11;
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_array_set(x_2, x_3, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_1 = x_4;
x_2 = x_6;
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
static lean_object* _init_l_Lean_Expr_getAppArgs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_getAppArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Expr_getAppNumArgsAux(x_1, x_2);
x_4 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_3);
x_5 = lean_mk_array(x_3, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_5, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_3, x_5, x_6, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_4, x_1, x_2);
return x_10;
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_array_push(x_2, x_4);
x_1 = x_3;
x_2 = x_5;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
lean_object* l_Lean_Expr_getAppRevArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Expr_getAppNumArgsAux(x_1, x_2);
x_4 = lean_mk_empty_array_with_capacity(x_3);
lean_dec(x_3);
x_5 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_withAppAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_5(x_4, x_6, x_7, x_9, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_apply_3(x_5, x_1, x_2, x_3);
return x_11;
}
}
}
lean_object* l_Lean_Expr_withAppAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_array_set(x_3, x_4, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_2 = x_5;
x_3 = x_7;
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_11; 
lean_dec(x_4);
x_11 = lean_apply_2(x_1, x_2, x_3);
return x_11;
}
}
}
lean_object* l_Lean_Expr_withAppAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_withApp___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Expr_getAppNumArgsAux(x_1, x_3);
x_5 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_4);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
x_9 = l_Lean_Expr_withAppAux___rarg(x_2, x_1, x_6, x_8);
return x_9;
}
}
lean_object* l_Lean_Expr_withApp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_withApp___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_3, x_5, x_6, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_4, x_1, x_2);
return x_10;
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_withAppRevAux_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_array_push(x_3, x_5);
x_2 = x_4;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_8; 
x_8 = lean_apply_2(x_1, x_2, x_3);
return x_8;
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppRev___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Expr_getAppNumArgsAux(x_1, x_3);
x_5 = lean_mk_empty_array_with_capacity(x_4);
lean_dec(x_4);
x_6 = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___rarg(x_2, x_1, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_withAppRev(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_withAppRev___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_getRevArgD_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_2, x_12);
lean_dec(x_2);
x_14 = lean_box_uint64(x_9);
x_15 = lean_apply_5(x_5, x_7, x_8, x_14, x_13, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_2);
x_16 = lean_box_uint64(x_9);
x_17 = lean_apply_4(x_4, x_7, x_8, x_16, x_3);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
x_18 = lean_apply_3(x_6, x_1, x_2, x_3);
return x_18;
}
}
}
lean_object* l_Lean_Expr_getRevArgD_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_getRevArgD_match__1___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_getRevArgD(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
x_1 = x_4;
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
lean_inc(x_5);
return x_5;
}
}
else
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
}
}
lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_getRevArgD(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Expr_getRevArg_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_2, x_11);
lean_dec(x_2);
x_13 = lean_box_uint64(x_8);
x_14 = lean_apply_4(x_4, x_6, x_7, x_13, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_box_uint64(x_8);
x_16 = lean_apply_3(x_3, x_6, x_7, x_15);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_apply_2(x_5, x_1, x_2);
return x_17;
}
}
}
lean_object* l_Lean_Expr_getRevArg_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_getRevArg_x21_match__1___rarg), 5, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.getRevArg!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_getRevArg_x21___closed__1;
x_3 = lean_unsigned_to_nat(481u);
x_4 = lean_unsigned_to_nat(22u);
x_5 = l_List_get_x21___rarg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_getRevArg_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_1 = x_3;
x_2 = x_8;
goto _start;
}
else
{
lean_dec(x_2);
lean_inc(x_4);
return x_4;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_10 = l_Lean_instInhabitedExpr;
x_11 = l_Lean_Expr_getRevArg_x21___closed__2;
x_12 = lean_panic_fn(x_10, x_11);
return x_12;
}
}
}
lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getRevArg_x21(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_getArg_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_nat_sub(x_3, x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
lean_dec(x_4);
x_7 = l_Lean_Expr_getRevArg_x21(x_1, x_6);
return x_7;
}
}
lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_getArg_x21(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Expr_getArgD(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_nat_sub(x_4, x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_8 = l_Lean_Expr_getRevArgD(x_1, x_7, x_3);
return x_8;
}
}
lean_object* l_Lean_Expr_getArgD___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_getArgD(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Expr_isAppOf_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Expr_isAppOf_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isAppOf_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isAppOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_name_eq(x_4, x_2);
lean_dec(x_4);
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
}
}
lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_isAppOf(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_isAppOfArity_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_12 = lean_apply_3(x_6, x_1, x_2, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_box_uint64(x_9);
x_14 = lean_apply_4(x_4, x_7, x_8, x_13, x_2);
return x_14;
}
}
case 5:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_4);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_3, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_1);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_3, x_20);
lean_dec(x_3);
x_22 = lean_box_uint64(x_17);
x_23 = lean_apply_5(x_5, x_15, x_16, x_22, x_2, x_21);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
x_24 = lean_apply_3(x_6, x_1, x_2, x_18);
return x_24;
}
}
default: 
{
lean_object* x_25; 
lean_dec(x_5);
lean_dec(x_4);
x_25 = lean_apply_3(x_6, x_1, x_2, x_3);
return x_25;
}
}
}
}
lean_object* l_Lean_Expr_isAppOfArity_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isAppOfArity_match__1___rarg), 6, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isAppOfArity(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
lean_dec(x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_name_eq(x_4, x_2);
return x_8;
}
}
case 5:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_3, x_12);
lean_dec(x_3);
x_1 = x_9;
x_3 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_3);
x_15 = 0;
return x_15;
}
}
default: 
{
uint8_t x_16; 
lean_dec(x_3);
x_16 = 0;
return x_16;
}
}
}
}
lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_appFn_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
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
lean_object* l_Lean_Expr_appFn_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_appFn_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.appFn!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("application expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_appFn_x21___closed__1;
x_3 = lean_unsigned_to_nat(501u);
x_4 = lean_unsigned_to_nat(17u);
x_5 = l_Lean_Expr_appFn_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_appFn_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instInhabitedExpr;
x_4 = l_Lean_Expr_appFn_x21___closed__3;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
}
}
lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_appFn_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_appArg_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
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
lean_object* l_Lean_Expr_appArg_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_appArg_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.appArg!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_appArg_x21___closed__1;
x_3 = lean_unsigned_to_nat(505u);
x_4 = lean_unsigned_to_nat(17u);
x_5 = l_Lean_Expr_appFn_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_appArg_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instInhabitedExpr;
x_4 = l_Lean_Expr_appArg_x21___closed__2;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
}
}
lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_isNatLit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint64_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_box_uint64(x_5);
x_8 = lean_apply_2(x_2, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
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
lean_object* l_Lean_Expr_isNatLit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isNatLit_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isNatLit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
lean_object* l_Lean_Expr_isNatLit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isNatLit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_natLit_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint64_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_box_uint64(x_5);
x_8 = lean_apply_2(x_2, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
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
lean_object* l_Lean_Expr_natLit_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_natLit_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_natLit_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
}
else
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
}
lean_object* l_Lean_Expr_natLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_natLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_isStringLit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_3, x_1);
return x_5;
}
else
{
uint64_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_box_uint64(x_6);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
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
lean_object* l_Lean_Expr_isStringLit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isStringLit_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isStringLit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
lean_object* l_Lean_Expr_isStringLit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isStringLit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_isCharLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Char");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_isCharLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_isCharLit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_isCharLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ofNat");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_isCharLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_isCharLit___closed__2;
x_2 = l_Lean_Expr_isCharLit___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_isCharLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_isCharLit___closed__4;
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Expr_appArg_x21(x_1);
x_7 = l_Lean_Expr_isNatLit(x_6);
lean_dec(x_6);
return x_7;
}
}
}
lean_object* l_Lean_Expr_isCharLit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isCharLit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_constName_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Expr_constName_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_constName_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.constName!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constant expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_constName_x21___closed__1;
x_3 = lean_unsigned_to_nat(524u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_Expr_constName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_constName_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instInhabitedName;
x_4 = l_Lean_Expr_constName_x21___closed__3;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
}
}
lean_object* l_Lean_Expr_constName_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_constName_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_constName_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Expr_constName_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_constName_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_constName_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
}
lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_constName_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_constLevels_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Expr_constLevels_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_constLevels_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_constLevels_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.constLevels!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_constLevels_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_constLevels_x21___closed__1;
x_3 = lean_unsigned_to_nat(532u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Expr_constName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_constLevels_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_Lean_Expr_constLevels_x21___closed__2;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
}
}
lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_constLevels_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_bvarIdx_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Expr_bvarIdx_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_bvarIdx_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.bvarIdx!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bvar expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_bvarIdx_x21___closed__1;
x_3 = lean_unsigned_to_nat(536u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Expr_bvarIdx_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_bvarIdx_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_instInhabitedNat;
x_4 = l_Lean_Expr_bvarIdx_x21___closed__3;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
}
}
lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_bvarIdx_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_fvarId_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Expr_fvarId_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_fvarId_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.fvarId!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fvar expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_fvarId_x21___closed__1;
x_3 = lean_unsigned_to_nat(540u);
x_4 = lean_unsigned_to_nat(16u);
x_5 = l_Lean_Expr_fvarId_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_fvarId_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instInhabitedName;
x_4 = l_Lean_Expr_fvarId_x21___closed__3;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
}
}
lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_fvarId_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_mvarId_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Expr_mvarId_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_mvarId_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.mvarId!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mvar expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_mvarId_x21___closed__1;
x_3 = lean_unsigned_to_nat(544u);
x_4 = lean_unsigned_to_nat(16u);
x_5 = l_Lean_Expr_mvarId_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_mvarId_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instInhabitedName;
x_4 = l_Lean_Expr_mvarId_x21___closed__3;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
}
}
lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_mvarId_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_bindingName_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
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
case 7:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_15 = lean_box_uint64(x_14);
x_16 = lean_apply_4(x_2, x_11, x_12, x_13, x_15);
return x_16;
}
default: 
{
lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_apply_1(x_4, x_1);
return x_17;
}
}
}
}
lean_object* l_Lean_Expr_bindingName_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_bindingName_x21_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.bindingName!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("binding expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_bindingName_x21___closed__1;
x_3 = lean_unsigned_to_nat(549u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Expr_bindingName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_bindingName_x21(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
case 7:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
default: 
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_instInhabitedName;
x_5 = l_Lean_Expr_bindingName_x21___closed__3;
x_6 = lean_panic_fn(x_4, x_5);
return x_6;
}
}
}
}
lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_bindingName_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_bindingDomain_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
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
case 7:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_15 = lean_box_uint64(x_14);
x_16 = lean_apply_4(x_2, x_11, x_12, x_13, x_15);
return x_16;
}
default: 
{
lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_apply_1(x_4, x_1);
return x_17;
}
}
}
}
lean_object* l_Lean_Expr_bindingDomain_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_bindingDomain_x21_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.bindingDomain!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_bindingDomain_x21___closed__1;
x_3 = lean_unsigned_to_nat(554u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Expr_bindingName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
case 7:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
return x_3;
}
default: 
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_instInhabitedExpr;
x_5 = l_Lean_Expr_bindingDomain_x21___closed__2;
x_6 = lean_panic_fn(x_4, x_5);
return x_6;
}
}
}
}
lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_bindingDomain_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_bindingBody_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
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
case 7:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_15 = lean_box_uint64(x_14);
x_16 = lean_apply_4(x_2, x_11, x_12, x_13, x_15);
return x_16;
}
default: 
{
lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_apply_1(x_4, x_1);
return x_17;
}
}
}
}
lean_object* l_Lean_Expr_bindingBody_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_bindingBody_x21_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.bindingBody!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_bindingBody_x21___closed__1;
x_3 = lean_unsigned_to_nat(559u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Expr_bindingName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_bindingBody_x21(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
case 7:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
return x_3;
}
default: 
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_instInhabitedExpr;
x_5 = l_Lean_Expr_bindingBody_x21___closed__2;
x_6 = lean_panic_fn(x_4, x_5);
return x_6;
}
}
}
}
lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_bindingBody_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_bindingInfo_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
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
case 7:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_15 = lean_box_uint64(x_14);
x_16 = lean_apply_4(x_2, x_11, x_12, x_13, x_15);
return x_16;
}
default: 
{
lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_apply_1(x_4, x_1);
return x_17;
}
}
}
}
lean_object* l_Lean_Expr_bindingInfo_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_bindingInfo_x21_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_bindingInfo_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.bindingInfo!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_bindingInfo_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_bindingInfo_x21___closed__1;
x_3 = lean_unsigned_to_nat(564u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Expr_bindingName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
uint8_t l_Lean_Expr_bindingInfo_x21(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
uint64_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_3 = (uint8_t)((x_2 << 24) >> 61);
return x_3;
}
case 7:
{
uint64_t x_4; uint8_t x_5; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_5 = (uint8_t)((x_4 << 24) >> 61);
return x_5;
}
default: 
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_instInhabitedBinderInfo;
x_7 = l_Lean_Expr_bindingInfo_x21___closed__2;
x_8 = lean_box(x_6);
x_9 = lean_panic_fn(x_8, x_7);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_bindingInfo_x21(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_letName_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_apply_1(x_3, x_1);
return x_11;
}
}
}
lean_object* l_Lean_Expr_letName_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_letName_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.letName!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("let expression expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_letName_x21___closed__1;
x_3 = lean_unsigned_to_nat(568u);
x_4 = lean_unsigned_to_nat(22u);
x_5 = l_Lean_Expr_letName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_letName_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instInhabitedName;
x_4 = l_Lean_Expr_letName_x21___closed__3;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
}
}
lean_object* l_Lean_Expr_letName_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_letName_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_consumeMData_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 10)
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
lean_object* l_Lean_Expr_consumeMData_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_consumeMData_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_consumeMData(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
x_1 = x_2;
goto _start;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l_Lean_Expr_consumeMData___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_consumeMData(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_Expr_hasLooseBVars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_looseBVarRange(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasLooseBVars(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_expr_has_loose_bvar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain_match__1___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_10 = lean_box_uint64(x_9);
x_11 = lean_box(x_3);
x_12 = lean_apply_6(x_4, x_6, x_7, x_8, x_10, x_2, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = lean_box(x_3);
x_14 = lean_apply_3(x_5, x_1, x_2, x_13);
return x_14;
}
}
}
lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_hasLooseBVarInExplicitDomain_match__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Expr_hasLooseBVarInExplicitDomain_match__1___rarg(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint8_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_7 = (uint8_t)((x_6 << 24) >> 61);
x_8 = l_Lean_BinderInfo_isExplicit(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_1 = x_5;
x_2 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = lean_expr_has_loose_bvar(x_4, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
lean_dec(x_2);
x_1 = x_5;
x_2 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_2);
x_16 = 1;
return x_16;
}
}
}
else
{
if (x_3 == 0)
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_expr_has_loose_bvar(x_1, x_2);
lean_dec(x_2);
return x_18;
}
}
}
}
lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Expr_hasLooseBVarInExplicitDomain(x_1, x_2, x_4);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_lower_loose_bvars(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_lift_loose_bvars(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Expr_inferImplicit_match__1___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_6);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
lean_dec(x_1);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_2, x_21);
lean_dec(x_2);
x_23 = lean_box_uint64(x_18);
x_24 = lean_box(x_3);
x_25 = lean_apply_6(x_4, x_15, x_16, x_17, x_23, x_22, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_26 = lean_box(x_3);
x_27 = lean_apply_2(x_5, x_1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_4);
x_28 = lean_box(0);
x_7 = x_28;
goto block_14;
}
block_14:
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_7);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_10 = lean_box(x_3);
x_11 = lean_apply_3(x_6, x_1, x_2, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_2);
x_12 = lean_box(x_3);
x_13 = lean_apply_2(x_5, x_1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Expr_inferImplicit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_inferImplicit_match__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_inferImplicit_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Expr_inferImplicit_match__1___rarg(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Expr_inferImplicit(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_2, x_10);
x_12 = l_Lean_Expr_inferImplicit(x_6, x_11, x_3);
lean_dec(x_11);
x_13 = (uint8_t)((x_7 << 24) >> 61);
x_14 = l_Lean_BinderInfo_isExplicit(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_mkForall(x_4, x_13, x_5, x_12);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = l_Lean_Expr_hasLooseBVarInExplicitDomain(x_12, x_8, x_3);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_mkForall(x_4, x_13, x_5, x_12);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; 
x_18 = 1;
x_19 = l_Lean_mkForall(x_4, x_18, x_5, x_12);
return x_19;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
}
else
{
return x_1;
}
}
}
lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Expr_inferImplicit(x_1, x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Expr_instantiate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_instantiate(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_instantiate1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_expr_instantiate_range(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_expr_instantiate_rev_range(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Expr_abstract___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_abstract(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_abstract_range(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Expr_replaceFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_mkOptionalNode___closed__2;
x_5 = lean_array_push(x_4, x_2);
x_6 = lean_expr_abstract(x_1, x_5);
lean_dec(x_5);
x_7 = lean_expr_instantiate1(x_6, x_3);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_replaceFVar(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Expr_replaceFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_mkFVar(x_2);
x_5 = l_Lean_Expr_replaceFVar(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_replaceFVarId(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Expr_replaceFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_expr_abstract(x_1, x_2);
x_5 = lean_expr_instantiate_rev(x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_replaceFVars(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Expr_instToStringExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_dbgToString___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instToStringExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_instToStringExpr___closed__1;
return x_1;
}
}
lean_object* l_Lean_Expr_isAtomic_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_11 = lean_box_uint64(x_10);
x_12 = lean_apply_2(x_4, x_9, x_11);
return x_12;
}
case 1:
{
lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_15 = lean_box_uint64(x_14);
x_16 = lean_apply_2(x_7, x_13, x_15);
return x_16;
}
case 2:
{
lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_19 = lean_box_uint64(x_18);
x_20 = lean_apply_2(x_6, x_17, x_19);
return x_20;
}
case 3:
{
lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_23 = lean_box_uint64(x_22);
x_24 = lean_apply_2(x_3, x_21, x_23);
return x_24;
}
case 4:
{
lean_object* x_25; lean_object* x_26; uint64_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_28 = lean_box_uint64(x_27);
x_29 = lean_apply_3(x_2, x_25, x_26, x_28);
return x_29;
}
case 9:
{
lean_object* x_30; uint64_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_32 = lean_box_uint64(x_31);
x_33 = lean_apply_2(x_5, x_30, x_32);
return x_33;
}
default: 
{
lean_object* x_34; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_apply_1(x_8, x_1);
return x_34;
}
}
}
}
lean_object* l_Lean_Expr_isAtomic_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isAtomic_match__1___rarg), 8, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isAtomic(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 6:
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
case 7:
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
case 8:
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
case 10:
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
case 11:
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
default: 
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_Lean_Expr_isAtomic___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isAtomic(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_mkAppB(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_mkApp(x_1, x_2);
x_5 = l_Lean_mkApp(x_4, x_3);
return x_5;
}
}
lean_object* l_Lean_mkApp2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkAppB(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_mkApp3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_mkAppB(x_1, x_2, x_3);
x_6 = l_Lean_mkApp(x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_mkApp4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_mkAppB(x_1, x_2, x_3);
x_7 = l_Lean_mkAppB(x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_mkApp5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_mkApp4(x_1, x_2, x_3, x_4, x_5);
x_8 = l_Lean_mkApp(x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_mkApp6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_mkApp4(x_1, x_2, x_3, x_4, x_5);
x_9 = l_Lean_mkAppB(x_8, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_mkApp7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_mkApp4(x_1, x_2, x_3, x_4, x_5);
x_10 = l_Lean_mkApp3(x_9, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_mkApp8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_mkApp4(x_1, x_2, x_3, x_4, x_5);
x_11 = l_Lean_mkApp4(x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_mkApp9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_mkApp4(x_1, x_2, x_3, x_4, x_5);
x_12 = l_Lean_mkApp5(x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_mkApp10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_mkApp4(x_1, x_2, x_3, x_4, x_5);
x_13 = l_Lean_mkApp6(x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Decidable");
return x_1;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkDecIsTrue___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isTrue");
return x_1;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkDecIsTrue___closed__2;
x_2 = l_Lean_mkDecIsTrue___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkDecIsTrue___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_mkDecIsTrue(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_mkDecIsTrue___closed__5;
x_4 = l_Lean_mkAppB(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isFalse");
return x_1;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkDecIsTrue___closed__2;
x_2 = l_Lean_mkDecIsFalse___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkDecIsFalse___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_mkDecIsFalse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_mkDecIsFalse___closed__3;
x_4 = l_Lean_mkAppB(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_instInhabitedExprStructEq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedExpr___closed__1;
return x_1;
}
}
lean_object* l_Lean_instCoeExprExprStructEq(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_instCoeExprExprStructEq___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instCoeExprExprStructEq(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_ExprStructEq_beq_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_ExprStructEq_beq_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ExprStructEq_beq_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_ExprStructEq_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_expr_equal(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_ExprStructEq_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_ExprStructEq_hash_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_ExprStructEq_hash_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ExprStructEq_hash_match__1___rarg), 2, 0);
return x_2;
}
}
size_t l_Lean_ExprStructEq_hash(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = l_Lean_Expr_hash(x_1);
return x_2;
}
}
lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Lean_ExprStructEq_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ExprStructEq_instBEqExprStructEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ExprStructEq_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ExprStructEq_instBEqExprStructEq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ExprStructEq_instBEqExprStructEq___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_ExprStructEq_instHashableExprStructEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ExprStructEq_hash___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ExprStructEq_instHashableExprStructEq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ExprStructEq_instHashableExprStructEq___closed__1;
return x_1;
}
}
lean_object* l_Lean_ExprStructEq_instToStringExprStructEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_dbg_to_string(x_1);
return x_2;
}
}
lean_object* l_Lean_ExprStructEq_instToStringExprStructEq___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ExprStructEq_instToStringExprStructEq(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_4, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_4, x_6);
lean_dec(x_4);
x_8 = l_Lean_instInhabitedExpr;
x_9 = lean_array_get(x_8, x_1, x_7);
x_10 = l_Lean_mkApp(x_3, x_9);
x_3 = x_10;
x_4 = x_7;
goto _start;
}
else
{
lean_dec(x_4);
return x_3;
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Expr_mkAppRevRange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(x_4, x_2, x_1, x_3);
return x_5;
}
}
lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_mkAppRevRange(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRevAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_10 = lean_box_uint64(x_9);
x_11 = lean_apply_5(x_3, x_6, x_7, x_8, x_10, x_2);
return x_11;
}
case 10:
{
lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_15 = lean_box_uint64(x_14);
x_16 = lean_apply_4(x_4, x_12, x_13, x_15, x_2);
return x_16;
}
default: 
{
lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_apply_2(x_5, x_1, x_2);
return x_17;
}
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRevAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_betaRevAux_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRevAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 6:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_8 = lean_nat_dec_lt(x_7, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_nat_sub(x_2, x_7);
lean_dec(x_7);
x_10 = lean_expr_instantiate_range(x_5, x_9, x_2, x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(x_1, x_11, x_10, x_9);
return x_12;
}
else
{
x_3 = x_5;
x_4 = x_7;
goto _start;
}
}
case 10:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_3, 1);
x_3 = x_14;
goto _start;
}
default: 
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_nat_sub(x_2, x_4);
lean_dec(x_4);
x_17 = lean_expr_instantiate_range(x_3, x_16, x_2, x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(x_1, x_18, x_17, x_16);
return x_19;
}
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRevAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Expr_0__Lean_Expr_betaRevAux(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Expr_betaRev(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l___private_Lean_Expr_0__Lean_Expr_betaRevAux(x_2, x_3, x_1, x_4);
lean_dec(x_3);
return x_6;
}
else
{
lean_dec(x_3);
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l_Lean_Expr_betaRev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_betaRev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_isHeadBetaTargetFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_4(x_2, x_5, x_6, x_7, x_9);
return x_10;
}
case 10:
{
lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_14 = lean_box_uint64(x_13);
x_15 = lean_apply_3(x_3, x_11, x_12, x_14);
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
lean_object* l_Lean_Expr_isHeadBetaTargetFn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_isHeadBetaTargetFn_match__1___rarg), 4, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_isHeadBetaTargetFn(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 10:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
x_1 = x_3;
goto _start;
}
default: 
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
}
lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isHeadBetaTargetFn(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_headBeta(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_getAppFn(x_1);
x_3 = l_Lean_Expr_isHeadBetaTargetFn(x_2);
if (x_3 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Expr_getAppNumArgsAux(x_1, x_4);
x_6 = lean_mk_empty_array_with_capacity(x_5);
lean_dec(x_5);
x_7 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_6);
x_8 = l_Lean_Expr_betaRev(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_getAppFn(x_1);
x_3 = l_Lean_Expr_isHeadBetaTargetFn(x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isHeadBetaTarget(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_7, sizeof(void*)*1);
lean_dec(x_7);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_2, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_2, x_14);
x_16 = lean_box_uint64(x_11);
x_17 = lean_box_uint64(x_9);
x_18 = lean_apply_6(x_4, x_8, x_10, x_16, x_17, x_15, x_3);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
x_19 = lean_apply_2(x_6, x_1, x_3);
return x_19;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_4);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_6);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_2, x_22);
x_24 = lean_apply_3(x_5, x_1, x_23, x_3);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_5);
x_25 = lean_apply_2(x_6, x_1, x_3);
return x_25;
}
}
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_4);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_eq(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_6);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_2, x_28);
x_30 = lean_apply_3(x_5, x_1, x_29, x_3);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_5);
x_31 = lean_apply_2(x_6, x_1, x_3);
return x_31;
}
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody_match__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody_match__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
lean_dec(x_2);
x_11 = lean_nat_dec_eq(x_6, x_3);
lean_dec(x_6);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_1 = x_5;
x_2 = x_10;
x_3 = x_13;
goto _start;
}
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_15 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_1);
x_17 = lean_box(0);
return x_17;
}
}
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_2, x_18);
lean_dec(x_2);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_1);
x_20 = lean_box(0);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
}
else
{
lean_object* x_24; uint8_t x_25; 
lean_dec(x_3);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_2, x_24);
lean_dec(x_2);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_1);
x_26 = lean_box(0);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_1);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_1);
x_29 = lean_box(0);
return x_29;
}
}
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_5(x_3, x_5, x_6, x_7, x_9, x_2);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = lean_apply_2(x_4, x_1, x_2);
return x_11;
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_3;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(x_1, x_2, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_etaExpandedStrict_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 6)
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
lean_object* l_Lean_Expr_etaExpandedStrict_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_etaExpandedStrict_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
}
}
static lean_object* _init_l_Lean_Expr_getOptParamDefault_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("optParam");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_getOptParamDefault_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_getOptParamDefault_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_getOptParamDefault_x3f___closed__2;
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Expr_appArg_x21(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getOptParamDefault_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_getAutoParamTactic_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("autoParam");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_getAutoParamTactic_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_getAutoParamTactic_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_getAutoParamTactic_x3f___closed__2;
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Expr_appArg_x21(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAutoParamTactic_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_Expr_isOptParam(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_getOptParamDefault_x3f___closed__2;
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_isOptParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isOptParam(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_isAutoParam(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_getAutoParamTactic_x3f___closed__2;
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isAutoParam(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_hasAnyFVar_visit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_12 = lean_box_uint64(x_11);
x_13 = lean_apply_3(x_8, x_1, x_10, x_12);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_17 = lean_box_uint64(x_16);
x_18 = lean_apply_3(x_6, x_14, x_15, x_17);
return x_18;
}
case 6:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_23 = lean_box_uint64(x_22);
x_24 = lean_apply_4(x_3, x_19, x_20, x_21, x_23);
return x_24;
}
case 7:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_29 = lean_box_uint64(x_28);
x_30 = lean_apply_4(x_2, x_25, x_26, x_27, x_29);
return x_30;
}
case 8:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 3);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_36 = lean_box_uint64(x_35);
x_37 = lean_apply_5(x_5, x_31, x_32, x_33, x_34, x_36);
return x_37;
}
case 10:
{
lean_object* x_38; lean_object* x_39; uint64_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
x_40 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_41 = lean_box_uint64(x_40);
x_42 = lean_apply_3(x_4, x_38, x_39, x_41);
return x_42;
}
case 11:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 2);
lean_inc(x_45);
x_46 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_47 = lean_box_uint64(x_46);
x_48 = lean_apply_4(x_7, x_43, x_44, x_45, x_47);
return x_48;
}
default: 
{
lean_object* x_49; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_apply_1(x_9, x_1);
return x_49;
}
}
}
}
lean_object* l_Lean_Expr_hasAnyFVar_visit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_hasAnyFVar_visit_match__1___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_hasAnyFVar_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasFVar(x_2);
if (x_3 == 0)
{
uint8_t x_4; lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = 0;
x_5 = lean_box(x_4);
return x_5;
}
else
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_1(x_1, x_6);
return x_7;
}
case 5:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_10 = l_Lean_Expr_hasAnyFVar_visit(x_1, x_8);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
x_2 = x_9;
goto _start;
}
else
{
uint8_t x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_1);
x_13 = 1;
x_14 = lean_box(x_13);
return x_14;
}
}
case 6:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_dec(x_2);
lean_inc(x_1);
x_17 = l_Lean_Expr_hasAnyFVar_visit(x_1, x_15);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
x_2 = x_16;
goto _start;
}
else
{
uint8_t x_20; lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_1);
x_20 = 1;
x_21 = lean_box(x_20);
return x_21;
}
}
case 7:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
lean_dec(x_2);
lean_inc(x_1);
x_24 = l_Lean_Expr_hasAnyFVar_visit(x_1, x_22);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
x_2 = x_23;
goto _start;
}
else
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_1);
x_27 = 1;
x_28 = lean_box(x_27);
return x_28;
}
}
case 8:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 3);
lean_inc(x_31);
lean_dec(x_2);
lean_inc(x_1);
x_32 = l_Lean_Expr_hasAnyFVar_visit(x_1, x_29);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
lean_inc(x_1);
x_34 = l_Lean_Expr_hasAnyFVar_visit(x_1, x_30);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
x_2 = x_31;
goto _start;
}
else
{
uint8_t x_37; lean_object* x_38; 
lean_dec(x_31);
lean_dec(x_1);
x_37 = 1;
x_38 = lean_box(x_37);
return x_38;
}
}
else
{
uint8_t x_39; lean_object* x_40; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_1);
x_39 = 1;
x_40 = lean_box(x_39);
return x_40;
}
}
case 10:
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
lean_dec(x_2);
x_2 = x_41;
goto _start;
}
case 11:
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
lean_dec(x_2);
x_2 = x_43;
goto _start;
}
default: 
{
uint8_t x_45; lean_object* x_46; 
lean_dec(x_2);
lean_dec(x_1);
x_45 = 0;
x_46 = lean_box(x_45);
return x_46;
}
}
}
}
}
lean_object* l_Lean_Expr_hasAnyFVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_hasAnyFVar_visit(x_2, x_1);
return x_3;
}
}
uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasFVar(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_name_eq(x_5, x_1);
return x_6;
}
case 5:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_1, x_7);
if (x_9 == 0)
{
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
case 6:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_1, x_12);
if (x_14 == 0)
{
x_2 = x_13;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
case 7:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
x_19 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_1, x_17);
if (x_19 == 0)
{
x_2 = x_18;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
}
case 8:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
x_25 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_1, x_22);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_1, x_23);
if (x_26 == 0)
{
x_2 = x_24;
goto _start;
}
else
{
uint8_t x_28; 
x_28 = 1;
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = 1;
return x_29;
}
}
case 10:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_2, 1);
x_2 = x_30;
goto _start;
}
case 11:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_2, 2);
x_2 = x_32;
goto _start;
}
default: 
{
uint8_t x_34; 
x_34 = 0;
return x_34;
}
}
}
}
}
uint8_t l_Lean_Expr_containsFVar(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_containsFVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_containsFVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_updateApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_expr_update_app(x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Expr_updateApp_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
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
lean_object* l_Lean_Expr_updateApp_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_updateApp_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_updateApp_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.updateApp!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_updateApp_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_updateApp_x21___closed__1;
x_3 = lean_unsigned_to_nat(845u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Expr_appFn_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_updateApp_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_expr_update_app(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_9 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set_uint64(x_9, sizeof(void*)*2, x_8);
x_10 = lean_expr_update_app(x_9, x_2, x_3);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_instInhabitedExpr;
x_12 = l_Lean_Expr_updateApp_x21___closed__2;
x_13 = lean_panic_fn(x_11, x_12);
return x_13;
}
}
}
lean_object* l_Lean_Expr_updateConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_update_const(x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Expr_updateConst_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Expr_updateConst_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_updateConst_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_updateConst_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.updateConst!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_updateConst_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_updateConst_x21___closed__1;
x_3 = lean_unsigned_to_nat(854u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Expr_constName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_updateConst_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_expr_update_const(x_1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set_uint64(x_8, sizeof(void*)*2, x_7);
x_9 = lean_expr_update_const(x_8, x_2);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_instInhabitedExpr;
x_11 = l_Lean_Expr_updateConst_x21___closed__2;
x_12 = lean_panic_fn(x_10, x_11);
return x_12;
}
}
}
lean_object* l_Lean_Expr_updateSort___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_update_sort(x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Expr_updateSort_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Expr_updateSort_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_updateSort_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_updateSort_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.updateSort!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_updateSort_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("level expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_updateSort_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_updateSort_x21___closed__1;
x_3 = lean_unsigned_to_nat(863u);
x_4 = lean_unsigned_to_nat(16u);
x_5 = l_Lean_Expr_updateSort_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_updateSort_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_expr_update_sort(x_1, x_2);
return x_4;
}
else
{
lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint64(x_7, sizeof(void*)*1, x_6);
x_8 = lean_expr_update_sort(x_7, x_2);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = l_Lean_instInhabitedExpr;
x_10 = l_Lean_Expr_updateSort_x21___closed__3;
x_11 = lean_panic_fn(x_9, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Expr_updateProj_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 11)
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
lean_object* l_Lean_Expr_updateProj_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_updateProj_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_updateProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_update_proj(x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Expr_updateMData_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 10)
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
lean_object* l_Lean_Expr_updateMData_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_updateMData_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_updateMData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_update_mdata(x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Expr_updateMData_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 10)
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
lean_object* l_Lean_Expr_updateMData_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_updateMData_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_updateMData_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.updateMData!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_updateMData_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mdata expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_updateMData_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_updateMData_x21___closed__1;
x_3 = lean_unsigned_to_nat(880u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_Expr_updateMData_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_updateMData_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_expr_update_mdata(x_1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set_uint64(x_8, sizeof(void*)*2, x_7);
x_9 = lean_expr_update_mdata(x_8, x_2);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_instInhabitedExpr;
x_11 = l_Lean_Expr_updateMData_x21___closed__3;
x_12 = lean_panic_fn(x_10, x_11);
return x_12;
}
}
}
lean_object* l_Lean_Expr_updateProj_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 11)
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
lean_object* l_Lean_Expr_updateProj_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_updateProj_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_updateProj_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.updateProj!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_updateProj_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("proj expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_updateProj_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_updateProj_x21___closed__1;
x_3 = lean_unsigned_to_nat(885u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Expr_updateProj_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_updateProj_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_expr_update_proj(x_1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set_uint64(x_9, sizeof(void*)*3, x_8);
x_10 = lean_expr_update_proj(x_9, x_2);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_instInhabitedExpr;
x_12 = l_Lean_Expr_updateProj_x21___closed__3;
x_13 = lean_panic_fn(x_11, x_12);
return x_13;
}
}
}
lean_object* l_Lean_Expr_updateForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_expr_update_forall(x_1, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l_Lean_Expr_updateForall_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Expr_updateForall_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_updateForall_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_updateForall_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.updateForall!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_updateForall_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("forall expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_updateForall_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_updateForall_x21___closed__1;
x_3 = lean_unsigned_to_nat(894u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Expr_updateForall_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_updateForall_x21(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_expr_update_forall(x_1, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_11 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set_uint64(x_11, sizeof(void*)*3, x_10);
x_12 = lean_expr_update_forall(x_11, x_2, x_3, x_4);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = l_Lean_instInhabitedExpr;
x_14 = l_Lean_Expr_updateForall_x21___closed__3;
x_15 = lean_panic_fn(x_13, x_14);
return x_15;
}
}
}
lean_object* l_Lean_Expr_updateForall_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_updateForall_x21(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Expr_updateForallE_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Expr_updateForallE_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_updateForallE_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.updateForallE!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_updateForallE_x21___closed__1;
x_3 = lean_unsigned_to_nat(899u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Expr_updateForall_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_updateForallE_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
uint64_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_6 = (uint8_t)((x_5 << 24) >> 61);
x_7 = lean_expr_update_forall(x_1, x_6, x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_12 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_10);
lean_ctor_set_uint64(x_12, sizeof(void*)*3, x_11);
x_13 = (uint8_t)((x_11 << 24) >> 61);
x_14 = lean_expr_update_forall(x_12, x_13, x_2, x_3);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_instInhabitedExpr;
x_16 = l_Lean_Expr_updateForallE_x21___closed__2;
x_17 = lean_panic_fn(x_15, x_16);
return x_17;
}
}
}
lean_object* l_Lean_Expr_updateLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_expr_update_lambda(x_1, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l_Lean_Expr_updateLambda_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 6)
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
lean_object* l_Lean_Expr_updateLambda_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_updateLambda_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_updateLambda_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.updateLambda!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_updateLambda_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lambda expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_updateLambda_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_updateLambda_x21___closed__1;
x_3 = lean_unsigned_to_nat(908u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_Expr_updateLambda_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_updateLambda_x21(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_expr_update_lambda(x_1, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_11 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set_uint64(x_11, sizeof(void*)*3, x_10);
x_12 = lean_expr_update_lambda(x_11, x_2, x_3, x_4);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = l_Lean_instInhabitedExpr;
x_14 = l_Lean_Expr_updateLambda_x21___closed__3;
x_15 = lean_panic_fn(x_13, x_14);
return x_15;
}
}
}
lean_object* l_Lean_Expr_updateLambda_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_updateLambda_x21(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Expr_updateLambdaE_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 6)
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
lean_object* l_Lean_Expr_updateLambdaE_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_updateLambdaE_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.updateLambdaE!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_updateLambdaE_x21___closed__1;
x_3 = lean_unsigned_to_nat(913u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_Expr_updateLambda_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
uint64_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_6 = (uint8_t)((x_5 << 24) >> 61);
x_7 = lean_expr_update_lambda(x_1, x_6, x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_12 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_10);
lean_ctor_set_uint64(x_12, sizeof(void*)*3, x_11);
x_13 = (uint8_t)((x_11 << 24) >> 61);
x_14 = lean_expr_update_lambda(x_12, x_13, x_2, x_3);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_instInhabitedExpr;
x_16 = l_Lean_Expr_updateLambdaE_x21___closed__2;
x_17 = lean_panic_fn(x_15, x_16);
return x_17;
}
}
}
lean_object* l_Lean_Expr_updateLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_expr_update_let(x_1, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Expr_updateLet_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_apply_1(x_3, x_1);
return x_11;
}
}
}
lean_object* l_Lean_Expr_updateLet_x21_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_updateLet_x21_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_updateLet_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.updateLet!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_updateLet_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_2 = l_Lean_Expr_updateLet_x21___closed__1;
x_3 = lean_unsigned_to_nat(922u);
x_4 = lean_unsigned_to_nat(22u);
x_5 = l_Lean_Expr_letName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_updateLet_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_expr_update_let(x_1, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_12 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_10);
lean_ctor_set_uint64(x_12, sizeof(void*)*4, x_11);
x_13 = lean_expr_update_let(x_12, x_2, x_3, x_4);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_instInhabitedExpr;
x_15 = l_Lean_Expr_updateLet_x21___closed__2;
x_16 = lean_panic_fn(x_14, x_15);
return x_16;
}
}
}
lean_object* l_Lean_Expr_updateFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_5(x_3, x_1, x_5, x_6, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_4, x_1, x_2);
return x_10;
}
}
}
lean_object* l_Lean_Expr_updateFn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_updateFn_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_updateFn(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_6 = l_Lean_Expr_updateFn(x_4, x_2);
lean_inc(x_5);
x_7 = lean_expr_update_app(x_1, x_6, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_8);
x_11 = l_Lean_Expr_updateFn(x_8, x_2);
lean_inc(x_9);
x_12 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set_uint64(x_12, sizeof(void*)*2, x_10);
x_13 = lean_expr_update_app(x_12, x_11, x_9);
return x_13;
}
}
else
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
lean_object* l_Lean_Expr_updateFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_updateFn(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_2(x_9, x_11, x_13);
return x_14;
}
case 4:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_3(x_8, x_15, x_16, x_18);
return x_19;
}
case 5:
{
lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_23 = lean_box_uint64(x_22);
x_24 = lean_apply_3(x_5, x_20, x_21, x_23);
return x_24;
}
case 6:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_29 = lean_box_uint64(x_28);
x_30 = lean_apply_4(x_2, x_25, x_26, x_27, x_29);
return x_30;
}
case 7:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
x_34 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_35 = lean_box_uint64(x_34);
x_36 = lean_apply_4(x_3, x_31, x_32, x_33, x_35);
return x_36;
}
case 8:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 3);
lean_inc(x_40);
x_41 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_42 = lean_box_uint64(x_41);
x_43 = lean_apply_5(x_4, x_37, x_38, x_39, x_40, x_42);
return x_43;
}
case 10:
{
lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_47 = lean_box_uint64(x_46);
x_48 = lean_apply_3(x_7, x_44, x_45, x_47);
return x_48;
}
case 11:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint64_t x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 2);
lean_inc(x_51);
x_52 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_53 = lean_box_uint64(x_52);
x_54 = lean_apply_4(x_6, x_49, x_50, x_51, x_53);
return x_54;
}
default: 
{
lean_object* x_55; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_apply_1(x_10, x_1);
return x_55;
}
}
}
}
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_instantiateLevelParamsCore_visit_match__1___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasLevelParam(x_2);
if (x_3 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
switch (lean_obj_tag(x_2)) {
case 3:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = l_Lean_Level_instantiateParams(x_1, x_5);
x_7 = lean_expr_update_sort(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_8);
x_10 = l_Lean_Level_instantiateParams(x_1, x_8);
x_11 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set_uint64(x_11, sizeof(void*)*1, x_9);
x_12 = lean_expr_update_sort(x_11, x_10);
return x_12;
}
}
case 4:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_alloc_closure((void*)(l_Lean_Level_instantiateParams), 2, 1);
lean_closure_set(x_15, 0, x_1);
lean_inc(x_14);
x_16 = l_List_map___rarg(x_15, x_14);
x_17 = lean_expr_update_const(x_2, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_21 = lean_alloc_closure((void*)(l_Lean_Level_instantiateParams), 2, 1);
lean_closure_set(x_21, 0, x_1);
lean_inc(x_19);
x_22 = l_List_map___rarg(x_21, x_19);
x_23 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set_uint64(x_23, sizeof(void*)*2, x_20);
x_24 = lean_expr_update_const(x_23, x_22);
return x_24;
}
}
case 5:
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_inc(x_1);
x_28 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_26);
lean_inc(x_27);
x_29 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_27);
x_30 = lean_expr_update_app(x_2, x_28, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint64_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_2, 0);
x_32 = lean_ctor_get(x_2, 1);
x_33 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_2);
lean_inc(x_31);
lean_inc(x_1);
x_34 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_31);
lean_inc(x_32);
x_35 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_32);
x_36 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set_uint64(x_36, sizeof(void*)*2, x_33);
x_37 = lean_expr_update_app(x_36, x_34, x_35);
return x_37;
}
}
case 6:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_2);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_2, 1);
x_40 = lean_ctor_get(x_2, 2);
x_41 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_39);
lean_inc(x_1);
x_42 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_39);
lean_inc(x_40);
x_43 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_40);
x_44 = (uint8_t)((x_41 << 24) >> 61);
x_45 = lean_expr_update_lambda(x_2, x_44, x_42, x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_2, 0);
x_47 = lean_ctor_get(x_2, 1);
x_48 = lean_ctor_get(x_2, 2);
x_49 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_2);
lean_inc(x_47);
lean_inc(x_1);
x_50 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_47);
lean_inc(x_48);
x_51 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_48);
x_52 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_47);
lean_ctor_set(x_52, 2, x_48);
lean_ctor_set_uint64(x_52, sizeof(void*)*3, x_49);
x_53 = (uint8_t)((x_49 << 24) >> 61);
x_54 = lean_expr_update_lambda(x_52, x_53, x_50, x_51);
return x_54;
}
}
case 7:
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_2);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint64_t x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_2, 1);
x_57 = lean_ctor_get(x_2, 2);
x_58 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_56);
lean_inc(x_1);
x_59 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_56);
lean_inc(x_57);
x_60 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_57);
x_61 = (uint8_t)((x_58 << 24) >> 61);
x_62 = lean_expr_update_forall(x_2, x_61, x_59, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint64_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_2, 0);
x_64 = lean_ctor_get(x_2, 1);
x_65 = lean_ctor_get(x_2, 2);
x_66 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_2);
lean_inc(x_64);
lean_inc(x_1);
x_67 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_64);
lean_inc(x_65);
x_68 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_65);
x_69 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_64);
lean_ctor_set(x_69, 2, x_65);
lean_ctor_set_uint64(x_69, sizeof(void*)*3, x_66);
x_70 = (uint8_t)((x_66 << 24) >> 61);
x_71 = lean_expr_update_forall(x_69, x_70, x_67, x_68);
return x_71;
}
}
case 8:
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_2);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_2, 1);
x_74 = lean_ctor_get(x_2, 2);
x_75 = lean_ctor_get(x_2, 3);
lean_inc(x_73);
lean_inc(x_1);
x_76 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_73);
lean_inc(x_74);
lean_inc(x_1);
x_77 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_74);
lean_inc(x_75);
x_78 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_75);
x_79 = lean_expr_update_let(x_2, x_76, x_77, x_78);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint64_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_2, 0);
x_81 = lean_ctor_get(x_2, 1);
x_82 = lean_ctor_get(x_2, 2);
x_83 = lean_ctor_get(x_2, 3);
x_84 = lean_ctor_get_uint64(x_2, sizeof(void*)*4);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_2);
lean_inc(x_81);
lean_inc(x_1);
x_85 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_81);
lean_inc(x_82);
lean_inc(x_1);
x_86 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_82);
lean_inc(x_83);
x_87 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_83);
x_88 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_88, 0, x_80);
lean_ctor_set(x_88, 1, x_81);
lean_ctor_set(x_88, 2, x_82);
lean_ctor_set(x_88, 3, x_83);
lean_ctor_set_uint64(x_88, sizeof(void*)*4, x_84);
x_89 = lean_expr_update_let(x_88, x_85, x_86, x_87);
return x_89;
}
}
case 10:
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_2);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_2, 1);
lean_inc(x_91);
x_92 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_91);
x_93 = lean_expr_update_mdata(x_2, x_92);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; uint64_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_2, 0);
x_95 = lean_ctor_get(x_2, 1);
x_96 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_2);
lean_inc(x_95);
x_97 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_95);
x_98 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_98, 0, x_94);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set_uint64(x_98, sizeof(void*)*2, x_96);
x_99 = lean_expr_update_mdata(x_98, x_97);
return x_99;
}
}
case 11:
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_2);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_2, 2);
lean_inc(x_101);
x_102 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_101);
x_103 = lean_expr_update_proj(x_2, x_102);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint64_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_2, 0);
x_105 = lean_ctor_get(x_2, 1);
x_106 = lean_ctor_get(x_2, 2);
x_107 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_2);
lean_inc(x_106);
x_108 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_106);
x_109 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_105);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set_uint64(x_109, sizeof(void*)*3, x_107);
x_110 = lean_expr_update_proj(x_109, x_108);
return x_110;
}
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
}
lean_object* l_Lean_Expr_instantiateLevelParamsCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubst_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_apply_3(x_5, x_1, x_2, x_3);
return x_6;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_apply_3(x_5, x_1, x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_5(x_4, x_8, x_9, x_10, x_11, x_3);
return x_12;
}
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubst_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_getParamSubst_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubst(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_name_eq(x_6, x_3);
if (x_10 == 0)
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_12; 
lean_inc(x_8);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
}
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Expr_0__Lean_Expr_getParamSubst(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_4; uint64_t x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_3, sizeof(void*)*1);
x_6 = l_Lean_Level_hasParam(x_3);
if (x_6 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_dec(x_8);
lean_inc(x_4);
x_9 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_4);
x_10 = lean_level_update_succ(x_3, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_inc(x_4);
x_11 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_4);
x_12 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set_uint64(x_12, sizeof(void*)*1, x_5);
x_13 = lean_level_update_succ(x_12, x_11);
return x_13;
}
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_17 = l_Lean_Level_hasParam(x_3);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_14);
return x_3;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_3, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 0);
lean_dec(x_20);
lean_inc(x_14);
x_21 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_14);
lean_inc(x_15);
x_22 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_15);
x_23 = lean_level_update_max(x_3, x_21, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_3);
lean_inc(x_14);
x_24 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_14);
lean_inc(x_15);
x_25 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_15);
x_26 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set_uint64(x_26, sizeof(void*)*2, x_16);
x_27 = lean_level_update_max(x_26, x_24, x_25);
return x_27;
}
}
}
case 3:
{
lean_object* x_28; lean_object* x_29; uint64_t x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_31 = l_Lean_Level_hasParam(x_3);
if (x_31 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
return x_3;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_3, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_3, 0);
lean_dec(x_34);
lean_inc(x_28);
x_35 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_28);
lean_inc(x_29);
x_36 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_29);
x_37 = lean_level_update_imax(x_3, x_35, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_3);
lean_inc(x_28);
x_38 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_28);
lean_inc(x_29);
x_39 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_29);
x_40 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_29);
lean_ctor_set_uint64(x_40, sizeof(void*)*2, x_30);
x_41 = lean_level_update_imax(x_40, x_38, x_39);
return x_41;
}
}
}
case 4:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
x_43 = l___private_Lean_Expr_0__Lean_Expr_getParamSubst(x_1, x_2, x_42);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
return x_3;
}
else
{
lean_object* x_44; 
lean_dec(x_3);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
return x_44;
}
}
default: 
{
return x_3;
}
}
}
}
lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_4; uint64_t x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_3, sizeof(void*)*1);
x_6 = l_Lean_Level_hasParam(x_3);
if (x_6 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_dec(x_8);
lean_inc(x_4);
x_9 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_4);
x_10 = lean_level_update_succ(x_3, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_inc(x_4);
x_11 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_4);
x_12 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set_uint64(x_12, sizeof(void*)*1, x_5);
x_13 = lean_level_update_succ(x_12, x_11);
return x_13;
}
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_17 = l_Lean_Level_hasParam(x_3);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_14);
return x_3;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_3, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 0);
lean_dec(x_20);
lean_inc(x_14);
x_21 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_14);
lean_inc(x_15);
x_22 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_15);
x_23 = lean_level_update_max(x_3, x_21, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_3);
lean_inc(x_14);
x_24 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_14);
lean_inc(x_15);
x_25 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_15);
x_26 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set_uint64(x_26, sizeof(void*)*2, x_16);
x_27 = lean_level_update_max(x_26, x_24, x_25);
return x_27;
}
}
}
case 3:
{
lean_object* x_28; lean_object* x_29; uint64_t x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_31 = l_Lean_Level_hasParam(x_3);
if (x_31 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
return x_3;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_3, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_3, 0);
lean_dec(x_34);
lean_inc(x_28);
x_35 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_28);
lean_inc(x_29);
x_36 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_29);
x_37 = lean_level_update_imax(x_3, x_35, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_3);
lean_inc(x_28);
x_38 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_28);
lean_inc(x_29);
x_39 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_29);
x_40 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_29);
lean_ctor_set_uint64(x_40, sizeof(void*)*2, x_30);
x_41 = lean_level_update_imax(x_40, x_38, x_39);
return x_41;
}
}
}
case 4:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
x_43 = l___private_Lean_Expr_0__Lean_Expr_getParamSubst(x_1, x_2, x_42);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
return x_3;
}
else
{
lean_object* x_44; 
lean_dec(x_3);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
return x_44;
}
}
default: 
{
return x_3;
}
}
}
}
lean_object* l_List_map___at_Lean_Expr_instantiateLevelParams___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_6);
x_9 = l_List_map___at_Lean_Expr_instantiateLevelParams___spec__4(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_10);
x_13 = l_List_map___at_Lean_Expr_instantiateLevelParams___spec__4(x_1, x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasLevelParam(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
switch (lean_obj_tag(x_3)) {
case 3:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_6);
x_8 = lean_expr_update_sort(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get_uint64(x_3, sizeof(void*)*1);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_9);
x_11 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_9);
x_12 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set_uint64(x_12, sizeof(void*)*1, x_10);
x_13 = lean_expr_update_sort(x_12, x_11);
return x_13;
}
}
case 4:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
x_16 = l_List_map___at_Lean_Expr_instantiateLevelParams___spec__4(x_1, x_2, x_15);
x_17 = lean_expr_update_const(x_3, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
lean_inc(x_19);
x_21 = l_List_map___at_Lean_Expr_instantiateLevelParams___spec__4(x_1, x_2, x_19);
x_22 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set_uint64(x_22, sizeof(void*)*2, x_20);
x_23 = lean_expr_update_const(x_22, x_21);
return x_23;
}
}
case 5:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
x_27 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_25);
lean_inc(x_26);
x_28 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_26);
x_29 = lean_expr_update_app(x_3, x_27, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_ctor_get(x_3, 1);
x_32 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_3);
lean_inc(x_30);
x_33 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_30);
lean_inc(x_31);
x_34 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_31);
x_35 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set_uint64(x_35, sizeof(void*)*2, x_32);
x_36 = lean_expr_update_app(x_35, x_33, x_34);
return x_36;
}
}
case 6:
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_3);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint64_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_3, 1);
x_39 = lean_ctor_get(x_3, 2);
x_40 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_38);
x_41 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_38);
lean_inc(x_39);
x_42 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_39);
x_43 = (uint8_t)((x_40 << 24) >> 61);
x_44 = lean_expr_update_lambda(x_3, x_43, x_41, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_3, 0);
x_46 = lean_ctor_get(x_3, 1);
x_47 = lean_ctor_get(x_3, 2);
x_48 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_3);
lean_inc(x_46);
x_49 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_46);
lean_inc(x_47);
x_50 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_47);
x_51 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_46);
lean_ctor_set(x_51, 2, x_47);
lean_ctor_set_uint64(x_51, sizeof(void*)*3, x_48);
x_52 = (uint8_t)((x_48 << 24) >> 61);
x_53 = lean_expr_update_lambda(x_51, x_52, x_49, x_50);
return x_53;
}
}
case 7:
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_3);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint64_t x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_3, 1);
x_56 = lean_ctor_get(x_3, 2);
x_57 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_55);
x_58 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_55);
lean_inc(x_56);
x_59 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_56);
x_60 = (uint8_t)((x_57 << 24) >> 61);
x_61 = lean_expr_update_forall(x_3, x_60, x_58, x_59);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_3, 0);
x_63 = lean_ctor_get(x_3, 1);
x_64 = lean_ctor_get(x_3, 2);
x_65 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_3);
lean_inc(x_63);
x_66 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_63);
lean_inc(x_64);
x_67 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_64);
x_68 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_63);
lean_ctor_set(x_68, 2, x_64);
lean_ctor_set_uint64(x_68, sizeof(void*)*3, x_65);
x_69 = (uint8_t)((x_65 << 24) >> 61);
x_70 = lean_expr_update_forall(x_68, x_69, x_66, x_67);
return x_70;
}
}
case 8:
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_3, 1);
x_73 = lean_ctor_get(x_3, 2);
x_74 = lean_ctor_get(x_3, 3);
lean_inc(x_72);
x_75 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_72);
lean_inc(x_73);
x_76 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_73);
lean_inc(x_74);
x_77 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_74);
x_78 = lean_expr_update_let(x_3, x_75, x_76, x_77);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint64_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_79 = lean_ctor_get(x_3, 0);
x_80 = lean_ctor_get(x_3, 1);
x_81 = lean_ctor_get(x_3, 2);
x_82 = lean_ctor_get(x_3, 3);
x_83 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_3);
lean_inc(x_80);
x_84 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_80);
lean_inc(x_81);
x_85 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_81);
lean_inc(x_82);
x_86 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_82);
x_87 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_80);
lean_ctor_set(x_87, 2, x_81);
lean_ctor_set(x_87, 3, x_82);
lean_ctor_set_uint64(x_87, sizeof(void*)*4, x_83);
x_88 = lean_expr_update_let(x_87, x_84, x_85, x_86);
return x_88;
}
}
case 10:
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_3);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_3, 1);
lean_inc(x_90);
x_91 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_90);
x_92 = lean_expr_update_mdata(x_3, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; uint64_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_3, 0);
x_94 = lean_ctor_get(x_3, 1);
x_95 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_3);
lean_inc(x_94);
x_96 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_94);
x_97 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set_uint64(x_97, sizeof(void*)*2, x_95);
x_98 = lean_expr_update_mdata(x_97, x_96);
return x_98;
}
}
case 11:
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_3);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_3, 2);
lean_inc(x_100);
x_101 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_100);
x_102 = lean_expr_update_proj(x_3, x_101);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint64_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_3, 0);
x_104 = lean_ctor_get(x_3, 1);
x_105 = lean_ctor_get(x_3, 2);
x_106 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_3);
lean_inc(x_105);
x_107 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_105);
x_108 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_104);
lean_ctor_set(x_108, 2, x_105);
lean_ctor_set_uint64(x_108, sizeof(void*)*3, x_106);
x_109 = lean_expr_update_proj(x_108, x_107);
return x_109;
}
}
default: 
{
return x_3;
}
}
}
}
}
lean_object* l_Lean_Expr_instantiateLevelParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___at_Lean_Expr_instantiateLevelParams___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___at_Lean_Expr_instantiateLevelParams___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Expr_instantiateLevelParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_instantiateLevelParams(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubstArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_1, x_4);
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_4, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_4);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget(x_2, x_4);
x_13 = lean_name_eq(x_8, x_3);
lean_dec(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
}
}
}
}
lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubstArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Expr_0__Lean_Expr_getParamSubstArray(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_4; uint64_t x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_3, sizeof(void*)*1);
x_6 = l_Lean_Level_hasParam(x_3);
if (x_6 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_dec(x_8);
lean_inc(x_4);
x_9 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_4);
x_10 = lean_level_update_succ(x_3, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_inc(x_4);
x_11 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_4);
x_12 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set_uint64(x_12, sizeof(void*)*1, x_5);
x_13 = lean_level_update_succ(x_12, x_11);
return x_13;
}
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_17 = l_Lean_Level_hasParam(x_3);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_14);
return x_3;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_3, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 0);
lean_dec(x_20);
lean_inc(x_14);
x_21 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_14);
lean_inc(x_15);
x_22 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_15);
x_23 = lean_level_update_max(x_3, x_21, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_3);
lean_inc(x_14);
x_24 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_14);
lean_inc(x_15);
x_25 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_15);
x_26 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set_uint64(x_26, sizeof(void*)*2, x_16);
x_27 = lean_level_update_max(x_26, x_24, x_25);
return x_27;
}
}
}
case 3:
{
lean_object* x_28; lean_object* x_29; uint64_t x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_31 = l_Lean_Level_hasParam(x_3);
if (x_31 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
return x_3;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_3, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_3, 0);
lean_dec(x_34);
lean_inc(x_28);
x_35 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_28);
lean_inc(x_29);
x_36 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_29);
x_37 = lean_level_update_imax(x_3, x_35, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_3);
lean_inc(x_28);
x_38 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_28);
lean_inc(x_29);
x_39 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_29);
x_40 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_29);
lean_ctor_set_uint64(x_40, sizeof(void*)*2, x_30);
x_41 = lean_level_update_imax(x_40, x_38, x_39);
return x_41;
}
}
}
case 4:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l___private_Lean_Expr_0__Lean_Expr_getParamSubstArray(x_1, x_2, x_42, x_43);
lean_dec(x_42);
if (lean_obj_tag(x_44) == 0)
{
return x_3;
}
else
{
lean_object* x_45; 
lean_dec(x_3);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
return x_45;
}
}
default: 
{
return x_3;
}
}
}
}
lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_4; uint64_t x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_3, sizeof(void*)*1);
x_6 = l_Lean_Level_hasParam(x_3);
if (x_6 == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_dec(x_8);
lean_inc(x_4);
x_9 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_4);
x_10 = lean_level_update_succ(x_3, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_inc(x_4);
x_11 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_4);
x_12 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set_uint64(x_12, sizeof(void*)*1, x_5);
x_13 = lean_level_update_succ(x_12, x_11);
return x_13;
}
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_17 = l_Lean_Level_hasParam(x_3);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_14);
return x_3;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_3, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_3, 0);
lean_dec(x_20);
lean_inc(x_14);
x_21 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_14);
lean_inc(x_15);
x_22 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_15);
x_23 = lean_level_update_max(x_3, x_21, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_3);
lean_inc(x_14);
x_24 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_14);
lean_inc(x_15);
x_25 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_15);
x_26 = lean_alloc_ctor(2, 2, 8);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set_uint64(x_26, sizeof(void*)*2, x_16);
x_27 = lean_level_update_max(x_26, x_24, x_25);
return x_27;
}
}
}
case 3:
{
lean_object* x_28; lean_object* x_29; uint64_t x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_31 = l_Lean_Level_hasParam(x_3);
if (x_31 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
return x_3;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_3);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_3, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_3, 0);
lean_dec(x_34);
lean_inc(x_28);
x_35 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_28);
lean_inc(x_29);
x_36 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_29);
x_37 = lean_level_update_imax(x_3, x_35, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_3);
lean_inc(x_28);
x_38 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_28);
lean_inc(x_29);
x_39 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_29);
x_40 = lean_alloc_ctor(3, 2, 8);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_29);
lean_ctor_set_uint64(x_40, sizeof(void*)*2, x_30);
x_41 = lean_level_update_imax(x_40, x_38, x_39);
return x_41;
}
}
}
case 4:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l___private_Lean_Expr_0__Lean_Expr_getParamSubstArray(x_1, x_2, x_42, x_43);
lean_dec(x_42);
if (lean_obj_tag(x_44) == 0)
{
return x_3;
}
else
{
lean_object* x_45; 
lean_dec(x_3);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
return x_45;
}
}
default: 
{
return x_3;
}
}
}
}
lean_object* l_List_map___at_Lean_Expr_instantiateLevelParamsArray___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_6);
x_9 = l_List_map___at_Lean_Expr_instantiateLevelParamsArray___spec__4(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_9);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_10);
x_13 = l_List_map___at_Lean_Expr_instantiateLevelParamsArray___spec__4(x_1, x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasLevelParam(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
switch (lean_obj_tag(x_3)) {
case 3:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_6);
x_8 = lean_expr_update_sort(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get_uint64(x_3, sizeof(void*)*1);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_9);
x_11 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_9);
x_12 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set_uint64(x_12, sizeof(void*)*1, x_10);
x_13 = lean_expr_update_sort(x_12, x_11);
return x_13;
}
}
case 4:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
x_16 = l_List_map___at_Lean_Expr_instantiateLevelParamsArray___spec__4(x_1, x_2, x_15);
x_17 = lean_expr_update_const(x_3, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
lean_inc(x_19);
x_21 = l_List_map___at_Lean_Expr_instantiateLevelParamsArray___spec__4(x_1, x_2, x_19);
x_22 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set_uint64(x_22, sizeof(void*)*2, x_20);
x_23 = lean_expr_update_const(x_22, x_21);
return x_23;
}
}
case 5:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
x_27 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_25);
lean_inc(x_26);
x_28 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_26);
x_29 = lean_expr_update_app(x_3, x_27, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_3, 0);
x_31 = lean_ctor_get(x_3, 1);
x_32 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_3);
lean_inc(x_30);
x_33 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_30);
lean_inc(x_31);
x_34 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_31);
x_35 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set_uint64(x_35, sizeof(void*)*2, x_32);
x_36 = lean_expr_update_app(x_35, x_33, x_34);
return x_36;
}
}
case 6:
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_3);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint64_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_3, 1);
x_39 = lean_ctor_get(x_3, 2);
x_40 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_38);
x_41 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_38);
lean_inc(x_39);
x_42 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_39);
x_43 = (uint8_t)((x_40 << 24) >> 61);
x_44 = lean_expr_update_lambda(x_3, x_43, x_41, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_3, 0);
x_46 = lean_ctor_get(x_3, 1);
x_47 = lean_ctor_get(x_3, 2);
x_48 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_3);
lean_inc(x_46);
x_49 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_46);
lean_inc(x_47);
x_50 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_47);
x_51 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_46);
lean_ctor_set(x_51, 2, x_47);
lean_ctor_set_uint64(x_51, sizeof(void*)*3, x_48);
x_52 = (uint8_t)((x_48 << 24) >> 61);
x_53 = lean_expr_update_lambda(x_51, x_52, x_49, x_50);
return x_53;
}
}
case 7:
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_3);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint64_t x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_3, 1);
x_56 = lean_ctor_get(x_3, 2);
x_57 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_55);
x_58 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_55);
lean_inc(x_56);
x_59 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_56);
x_60 = (uint8_t)((x_57 << 24) >> 61);
x_61 = lean_expr_update_forall(x_3, x_60, x_58, x_59);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_3, 0);
x_63 = lean_ctor_get(x_3, 1);
x_64 = lean_ctor_get(x_3, 2);
x_65 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_3);
lean_inc(x_63);
x_66 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_63);
lean_inc(x_64);
x_67 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_64);
x_68 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_63);
lean_ctor_set(x_68, 2, x_64);
lean_ctor_set_uint64(x_68, sizeof(void*)*3, x_65);
x_69 = (uint8_t)((x_65 << 24) >> 61);
x_70 = lean_expr_update_forall(x_68, x_69, x_66, x_67);
return x_70;
}
}
case 8:
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_3, 1);
x_73 = lean_ctor_get(x_3, 2);
x_74 = lean_ctor_get(x_3, 3);
lean_inc(x_72);
x_75 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_72);
lean_inc(x_73);
x_76 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_73);
lean_inc(x_74);
x_77 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_74);
x_78 = lean_expr_update_let(x_3, x_75, x_76, x_77);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint64_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_79 = lean_ctor_get(x_3, 0);
x_80 = lean_ctor_get(x_3, 1);
x_81 = lean_ctor_get(x_3, 2);
x_82 = lean_ctor_get(x_3, 3);
x_83 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_3);
lean_inc(x_80);
x_84 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_80);
lean_inc(x_81);
x_85 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_81);
lean_inc(x_82);
x_86 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_82);
x_87 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_80);
lean_ctor_set(x_87, 2, x_81);
lean_ctor_set(x_87, 3, x_82);
lean_ctor_set_uint64(x_87, sizeof(void*)*4, x_83);
x_88 = lean_expr_update_let(x_87, x_84, x_85, x_86);
return x_88;
}
}
case 10:
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_3);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_3, 1);
lean_inc(x_90);
x_91 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_90);
x_92 = lean_expr_update_mdata(x_3, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; uint64_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_3, 0);
x_94 = lean_ctor_get(x_3, 1);
x_95 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_3);
lean_inc(x_94);
x_96 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_94);
x_97 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set_uint64(x_97, sizeof(void*)*2, x_95);
x_98 = lean_expr_update_mdata(x_97, x_96);
return x_98;
}
}
case 11:
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_3);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_3, 2);
lean_inc(x_100);
x_101 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_100);
x_102 = lean_expr_update_proj(x_3, x_101);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint64_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_3, 0);
x_104 = lean_ctor_get(x_3, 1);
x_105 = lean_ctor_get(x_3, 2);
x_106 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_3);
lean_inc(x_105);
x_107 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_105);
x_108 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_104);
lean_ctor_set(x_108, 2, x_105);
lean_ctor_set_uint64(x_108, sizeof(void*)*3, x_106);
x_109 = lean_expr_update_proj(x_108, x_107);
return x_109;
}
}
default: 
{
return x_3;
}
}
}
}
}
lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___at_Lean_Expr_instantiateLevelParamsArray___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___at_Lean_Expr_instantiateLevelParamsArray___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Expr_instantiateLevelParamsArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_instantiateLevelParamsArray(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Expr_setOption___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_3(x_5, x_6, x_2, x_4);
x_8 = l_Lean_mkMData(x_7, x_1);
return x_8;
}
}
lean_object* l_Lean_Expr_setOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_setOption___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_setOption___at_Lean_Expr_setPPExplicit___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = l_Lean_KVMap_setBool(x_4, x_2, x_3);
x_6 = l_Lean_mkMData(x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_setPPExplicit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pp");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_setPPExplicit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_setPPExplicit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_setPPExplicit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_setPPExplicit___closed__2;
x_2 = l_myMacro____x40_Init_NotationExtra___hyg_3476____closed__42;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_setPPExplicit(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_setPPExplicit___closed__3;
x_4 = l_Lean_Expr_setOption___at_Lean_Expr_setPPExplicit___spec__1(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Expr_setOption___at_Lean_Expr_setPPExplicit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Expr_setOption___at_Lean_Expr_setPPExplicit___spec__1(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Expr_setPPExplicit(x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_setAppPPExplicit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
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
lean_object* l_Lean_Expr_setAppPPExplicit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_setAppPPExplicit_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicit___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = 0;
x_11 = l_Lean_Expr_setPPExplicit(x_9, x_10);
x_12 = 1;
x_13 = x_2 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_8, x_2, x_14);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_2 = l_Lean_Expr_getAppFn(x_1);
x_3 = 0;
x_4 = l_Lean_Expr_setPPExplicit(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Expr_getAppNumArgsAux(x_1, x_5);
x_7 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_6);
x_8 = lean_mk_array(x_6, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_6, x_9);
lean_dec(x_6);
x_11 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_8, x_10);
x_12 = lean_array_get_size(x_11);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = x_11;
x_16 = l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicit___spec__1(x_13, x_14, x_15);
x_17 = x_16;
x_18 = l_Lean_mkAppN(x_4, x_17);
lean_dec(x_17);
x_19 = 1;
x_20 = l_Lean_Expr_setPPExplicit(x_18, x_19);
return x_20;
}
else
{
return x_1;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicit___spec__1(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Lean_mkAnnotation(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_KVMap_empty;
x_4 = l_Lean_initFn____x40_Lean_Data_Options___hyg_487____closed__3;
x_5 = l_Lean_KVMap_insertCore(x_3, x_1, x_4);
x_6 = l_Lean_mkMData(x_5, x_2);
return x_6;
}
}
lean_object* l_Lean_annotation_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 10)
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
lean_object* l_Lean_annotation_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_annotation_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_annotation_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_List_lengthAux___rarg(x_3, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; uint8_t x_11; 
x_10 = 0;
x_11 = l_Lean_KVMap_getBool(x_3, x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
lean_inc(x_4);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
}
}
else
{
lean_object* x_14; 
x_14 = lean_box(0);
return x_14;
}
}
}
lean_object* l_Lean_annotation_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_annotation_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_mkFreshFVarId___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkFreshFVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_mkFreshMVarId___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkFreshMVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkFreshMVarId___rarg), 2, 0);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_KVMap(lean_object*);
lean_object* initialize_Lean_Level(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Expr(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_KVMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Level(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedLiteral___closed__1 = _init_l_Lean_instInhabitedLiteral___closed__1();
lean_mark_persistent(l_Lean_instInhabitedLiteral___closed__1);
l_Lean_instInhabitedLiteral = _init_l_Lean_instInhabitedLiteral();
lean_mark_persistent(l_Lean_instInhabitedLiteral);
l_Lean_instBEqLiteral___closed__1 = _init_l_Lean_instBEqLiteral___closed__1();
lean_mark_persistent(l_Lean_instBEqLiteral___closed__1);
l_Lean_instBEqLiteral = _init_l_Lean_instBEqLiteral();
lean_mark_persistent(l_Lean_instBEqLiteral);
l_Lean_instHashableLiteral___closed__1 = _init_l_Lean_instHashableLiteral___closed__1();
lean_mark_persistent(l_Lean_instHashableLiteral___closed__1);
l_Lean_instHashableLiteral = _init_l_Lean_instHashableLiteral();
lean_mark_persistent(l_Lean_instHashableLiteral);
l_Lean_instHasLessLiteral = _init_l_Lean_instHasLessLiteral();
lean_mark_persistent(l_Lean_instHasLessLiteral);
l_Lean_instInhabitedBinderInfo = _init_l_Lean_instInhabitedBinderInfo();
l_Lean_instBEqBinderInfo___closed__1 = _init_l_Lean_instBEqBinderInfo___closed__1();
lean_mark_persistent(l_Lean_instBEqBinderInfo___closed__1);
l_Lean_instBEqBinderInfo = _init_l_Lean_instBEqBinderInfo();
lean_mark_persistent(l_Lean_instBEqBinderInfo);
l_Lean_instHashableBinderInfo___closed__1 = _init_l_Lean_instHashableBinderInfo___closed__1();
lean_mark_persistent(l_Lean_instHashableBinderInfo___closed__1);
l_Lean_instHashableBinderInfo = _init_l_Lean_instHashableBinderInfo();
lean_mark_persistent(l_Lean_instHashableBinderInfo);
l_Lean_MData_empty = _init_l_Lean_MData_empty();
lean_mark_persistent(l_Lean_MData_empty);
l_Lean_instInhabitedData__1 = _init_l_Lean_instInhabitedData__1();
l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1 = _init_l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1);
l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2 = _init_l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2);
l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__3 = _init_l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__3();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__3);
l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__4 = _init_l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__4();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__4);
l___private_Lean_Expr_0__Lean_Expr_mkDataCore___boxed__const__1 = _init_l___private_Lean_Expr_0__Lean_Expr_mkDataCore___boxed__const__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_mkDataCore___boxed__const__1);
l_Lean_Expr_mkData___closed__1 = _init_l_Lean_Expr_mkData___closed__1();
l_Lean_Expr_mkData___closed__2 = _init_l_Lean_Expr_mkData___closed__2();
l_Lean_Expr_mkData___closed__3 = _init_l_Lean_Expr_mkData___closed__3();
l_Lean_Expr_mkData___closed__4 = _init_l_Lean_Expr_mkData___closed__4();
l_Lean_Expr_mkData___boxed__const__1 = _init_l_Lean_Expr_mkData___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_mkData___boxed__const__1);
l_Lean_Expr_mkDataForBinder___boxed__const__1 = _init_l_Lean_Expr_mkDataForBinder___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_mkDataForBinder___boxed__const__1);
l_Lean_Expr_mkDataForLet___boxed__const__1 = _init_l_Lean_Expr_mkDataForLet___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_mkDataForLet___boxed__const__1);
l_Lean_instInhabitedExpr___closed__1 = _init_l_Lean_instInhabitedExpr___closed__1();
lean_mark_persistent(l_Lean_instInhabitedExpr___closed__1);
l_Lean_instInhabitedExpr = _init_l_Lean_instInhabitedExpr();
lean_mark_persistent(l_Lean_instInhabitedExpr);
l_Lean_Expr_ctorName___closed__1 = _init_l_Lean_Expr_ctorName___closed__1();
lean_mark_persistent(l_Lean_Expr_ctorName___closed__1);
l_Lean_Expr_ctorName___closed__2 = _init_l_Lean_Expr_ctorName___closed__2();
lean_mark_persistent(l_Lean_Expr_ctorName___closed__2);
l_Lean_Expr_ctorName___closed__3 = _init_l_Lean_Expr_ctorName___closed__3();
lean_mark_persistent(l_Lean_Expr_ctorName___closed__3);
l_Lean_Expr_ctorName___closed__4 = _init_l_Lean_Expr_ctorName___closed__4();
lean_mark_persistent(l_Lean_Expr_ctorName___closed__4);
l_Lean_Expr_ctorName___closed__5 = _init_l_Lean_Expr_ctorName___closed__5();
lean_mark_persistent(l_Lean_Expr_ctorName___closed__5);
l_Lean_Expr_ctorName___closed__6 = _init_l_Lean_Expr_ctorName___closed__6();
lean_mark_persistent(l_Lean_Expr_ctorName___closed__6);
l_Lean_Expr_ctorName___closed__7 = _init_l_Lean_Expr_ctorName___closed__7();
lean_mark_persistent(l_Lean_Expr_ctorName___closed__7);
l_Lean_Expr_ctorName___closed__8 = _init_l_Lean_Expr_ctorName___closed__8();
lean_mark_persistent(l_Lean_Expr_ctorName___closed__8);
l_Lean_Expr_ctorName___closed__9 = _init_l_Lean_Expr_ctorName___closed__9();
lean_mark_persistent(l_Lean_Expr_ctorName___closed__9);
l_Lean_Expr_ctorName___closed__10 = _init_l_Lean_Expr_ctorName___closed__10();
lean_mark_persistent(l_Lean_Expr_ctorName___closed__10);
l_Lean_Expr_instHashableExpr___closed__1 = _init_l_Lean_Expr_instHashableExpr___closed__1();
lean_mark_persistent(l_Lean_Expr_instHashableExpr___closed__1);
l_Lean_Expr_instHashableExpr = _init_l_Lean_Expr_instHashableExpr();
lean_mark_persistent(l_Lean_Expr_instHashableExpr);
l_Lean_Literal_type___closed__1 = _init_l_Lean_Literal_type___closed__1();
lean_mark_persistent(l_Lean_Literal_type___closed__1);
l_Lean_Literal_type___closed__2 = _init_l_Lean_Literal_type___closed__2();
lean_mark_persistent(l_Lean_Literal_type___closed__2);
l_Lean_Literal_type___closed__3 = _init_l_Lean_Literal_type___closed__3();
lean_mark_persistent(l_Lean_Literal_type___closed__3);
l_Lean_Literal_type___closed__4 = _init_l_Lean_Literal_type___closed__4();
lean_mark_persistent(l_Lean_Literal_type___closed__4);
l_Lean_mkSimpleThunkType___closed__1 = _init_l_Lean_mkSimpleThunkType___closed__1();
lean_mark_persistent(l_Lean_mkSimpleThunkType___closed__1);
l_Lean_mkSimpleThunk___closed__1 = _init_l_Lean_mkSimpleThunk___closed__1();
lean_mark_persistent(l_Lean_mkSimpleThunk___closed__1);
l_Lean_Expr_instBEqExpr___closed__1 = _init_l_Lean_Expr_instBEqExpr___closed__1();
lean_mark_persistent(l_Lean_Expr_instBEqExpr___closed__1);
l_Lean_Expr_instBEqExpr = _init_l_Lean_Expr_instBEqExpr();
lean_mark_persistent(l_Lean_Expr_instBEqExpr);
l_Lean_Expr_getAppArgs___closed__1 = _init_l_Lean_Expr_getAppArgs___closed__1();
lean_mark_persistent(l_Lean_Expr_getAppArgs___closed__1);
l_Lean_Expr_getRevArg_x21___closed__1 = _init_l_Lean_Expr_getRevArg_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_getRevArg_x21___closed__1);
l_Lean_Expr_getRevArg_x21___closed__2 = _init_l_Lean_Expr_getRevArg_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_getRevArg_x21___closed__2);
l_Lean_Expr_appFn_x21___closed__1 = _init_l_Lean_Expr_appFn_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_appFn_x21___closed__1);
l_Lean_Expr_appFn_x21___closed__2 = _init_l_Lean_Expr_appFn_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_appFn_x21___closed__2);
l_Lean_Expr_appFn_x21___closed__3 = _init_l_Lean_Expr_appFn_x21___closed__3();
lean_mark_persistent(l_Lean_Expr_appFn_x21___closed__3);
l_Lean_Expr_appArg_x21___closed__1 = _init_l_Lean_Expr_appArg_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_appArg_x21___closed__1);
l_Lean_Expr_appArg_x21___closed__2 = _init_l_Lean_Expr_appArg_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_appArg_x21___closed__2);
l_Lean_Expr_isCharLit___closed__1 = _init_l_Lean_Expr_isCharLit___closed__1();
lean_mark_persistent(l_Lean_Expr_isCharLit___closed__1);
l_Lean_Expr_isCharLit___closed__2 = _init_l_Lean_Expr_isCharLit___closed__2();
lean_mark_persistent(l_Lean_Expr_isCharLit___closed__2);
l_Lean_Expr_isCharLit___closed__3 = _init_l_Lean_Expr_isCharLit___closed__3();
lean_mark_persistent(l_Lean_Expr_isCharLit___closed__3);
l_Lean_Expr_isCharLit___closed__4 = _init_l_Lean_Expr_isCharLit___closed__4();
lean_mark_persistent(l_Lean_Expr_isCharLit___closed__4);
l_Lean_Expr_constName_x21___closed__1 = _init_l_Lean_Expr_constName_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_constName_x21___closed__1);
l_Lean_Expr_constName_x21___closed__2 = _init_l_Lean_Expr_constName_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_constName_x21___closed__2);
l_Lean_Expr_constName_x21___closed__3 = _init_l_Lean_Expr_constName_x21___closed__3();
lean_mark_persistent(l_Lean_Expr_constName_x21___closed__3);
l_Lean_Expr_constLevels_x21___closed__1 = _init_l_Lean_Expr_constLevels_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_constLevels_x21___closed__1);
l_Lean_Expr_constLevels_x21___closed__2 = _init_l_Lean_Expr_constLevels_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_constLevels_x21___closed__2);
l_Lean_Expr_bvarIdx_x21___closed__1 = _init_l_Lean_Expr_bvarIdx_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_bvarIdx_x21___closed__1);
l_Lean_Expr_bvarIdx_x21___closed__2 = _init_l_Lean_Expr_bvarIdx_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_bvarIdx_x21___closed__2);
l_Lean_Expr_bvarIdx_x21___closed__3 = _init_l_Lean_Expr_bvarIdx_x21___closed__3();
lean_mark_persistent(l_Lean_Expr_bvarIdx_x21___closed__3);
l_Lean_Expr_fvarId_x21___closed__1 = _init_l_Lean_Expr_fvarId_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_fvarId_x21___closed__1);
l_Lean_Expr_fvarId_x21___closed__2 = _init_l_Lean_Expr_fvarId_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_fvarId_x21___closed__2);
l_Lean_Expr_fvarId_x21___closed__3 = _init_l_Lean_Expr_fvarId_x21___closed__3();
lean_mark_persistent(l_Lean_Expr_fvarId_x21___closed__3);
l_Lean_Expr_mvarId_x21___closed__1 = _init_l_Lean_Expr_mvarId_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_mvarId_x21___closed__1);
l_Lean_Expr_mvarId_x21___closed__2 = _init_l_Lean_Expr_mvarId_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_mvarId_x21___closed__2);
l_Lean_Expr_mvarId_x21___closed__3 = _init_l_Lean_Expr_mvarId_x21___closed__3();
lean_mark_persistent(l_Lean_Expr_mvarId_x21___closed__3);
l_Lean_Expr_bindingName_x21___closed__1 = _init_l_Lean_Expr_bindingName_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_bindingName_x21___closed__1);
l_Lean_Expr_bindingName_x21___closed__2 = _init_l_Lean_Expr_bindingName_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_bindingName_x21___closed__2);
l_Lean_Expr_bindingName_x21___closed__3 = _init_l_Lean_Expr_bindingName_x21___closed__3();
lean_mark_persistent(l_Lean_Expr_bindingName_x21___closed__3);
l_Lean_Expr_bindingDomain_x21___closed__1 = _init_l_Lean_Expr_bindingDomain_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_bindingDomain_x21___closed__1);
l_Lean_Expr_bindingDomain_x21___closed__2 = _init_l_Lean_Expr_bindingDomain_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_bindingDomain_x21___closed__2);
l_Lean_Expr_bindingBody_x21___closed__1 = _init_l_Lean_Expr_bindingBody_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_bindingBody_x21___closed__1);
l_Lean_Expr_bindingBody_x21___closed__2 = _init_l_Lean_Expr_bindingBody_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_bindingBody_x21___closed__2);
l_Lean_Expr_bindingInfo_x21___closed__1 = _init_l_Lean_Expr_bindingInfo_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_bindingInfo_x21___closed__1);
l_Lean_Expr_bindingInfo_x21___closed__2 = _init_l_Lean_Expr_bindingInfo_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_bindingInfo_x21___closed__2);
l_Lean_Expr_letName_x21___closed__1 = _init_l_Lean_Expr_letName_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_letName_x21___closed__1);
l_Lean_Expr_letName_x21___closed__2 = _init_l_Lean_Expr_letName_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_letName_x21___closed__2);
l_Lean_Expr_letName_x21___closed__3 = _init_l_Lean_Expr_letName_x21___closed__3();
lean_mark_persistent(l_Lean_Expr_letName_x21___closed__3);
l_Lean_Expr_instToStringExpr___closed__1 = _init_l_Lean_Expr_instToStringExpr___closed__1();
lean_mark_persistent(l_Lean_Expr_instToStringExpr___closed__1);
l_Lean_Expr_instToStringExpr = _init_l_Lean_Expr_instToStringExpr();
lean_mark_persistent(l_Lean_Expr_instToStringExpr);
l_Lean_mkDecIsTrue___closed__1 = _init_l_Lean_mkDecIsTrue___closed__1();
lean_mark_persistent(l_Lean_mkDecIsTrue___closed__1);
l_Lean_mkDecIsTrue___closed__2 = _init_l_Lean_mkDecIsTrue___closed__2();
lean_mark_persistent(l_Lean_mkDecIsTrue___closed__2);
l_Lean_mkDecIsTrue___closed__3 = _init_l_Lean_mkDecIsTrue___closed__3();
lean_mark_persistent(l_Lean_mkDecIsTrue___closed__3);
l_Lean_mkDecIsTrue___closed__4 = _init_l_Lean_mkDecIsTrue___closed__4();
lean_mark_persistent(l_Lean_mkDecIsTrue___closed__4);
l_Lean_mkDecIsTrue___closed__5 = _init_l_Lean_mkDecIsTrue___closed__5();
lean_mark_persistent(l_Lean_mkDecIsTrue___closed__5);
l_Lean_mkDecIsFalse___closed__1 = _init_l_Lean_mkDecIsFalse___closed__1();
lean_mark_persistent(l_Lean_mkDecIsFalse___closed__1);
l_Lean_mkDecIsFalse___closed__2 = _init_l_Lean_mkDecIsFalse___closed__2();
lean_mark_persistent(l_Lean_mkDecIsFalse___closed__2);
l_Lean_mkDecIsFalse___closed__3 = _init_l_Lean_mkDecIsFalse___closed__3();
lean_mark_persistent(l_Lean_mkDecIsFalse___closed__3);
l_Lean_instInhabitedExprStructEq = _init_l_Lean_instInhabitedExprStructEq();
lean_mark_persistent(l_Lean_instInhabitedExprStructEq);
l_Lean_ExprStructEq_instBEqExprStructEq___closed__1 = _init_l_Lean_ExprStructEq_instBEqExprStructEq___closed__1();
lean_mark_persistent(l_Lean_ExprStructEq_instBEqExprStructEq___closed__1);
l_Lean_ExprStructEq_instBEqExprStructEq = _init_l_Lean_ExprStructEq_instBEqExprStructEq();
lean_mark_persistent(l_Lean_ExprStructEq_instBEqExprStructEq);
l_Lean_ExprStructEq_instHashableExprStructEq___closed__1 = _init_l_Lean_ExprStructEq_instHashableExprStructEq___closed__1();
lean_mark_persistent(l_Lean_ExprStructEq_instHashableExprStructEq___closed__1);
l_Lean_ExprStructEq_instHashableExprStructEq = _init_l_Lean_ExprStructEq_instHashableExprStructEq();
lean_mark_persistent(l_Lean_ExprStructEq_instHashableExprStructEq);
l_Lean_Expr_getOptParamDefault_x3f___closed__1 = _init_l_Lean_Expr_getOptParamDefault_x3f___closed__1();
lean_mark_persistent(l_Lean_Expr_getOptParamDefault_x3f___closed__1);
l_Lean_Expr_getOptParamDefault_x3f___closed__2 = _init_l_Lean_Expr_getOptParamDefault_x3f___closed__2();
lean_mark_persistent(l_Lean_Expr_getOptParamDefault_x3f___closed__2);
l_Lean_Expr_getAutoParamTactic_x3f___closed__1 = _init_l_Lean_Expr_getAutoParamTactic_x3f___closed__1();
lean_mark_persistent(l_Lean_Expr_getAutoParamTactic_x3f___closed__1);
l_Lean_Expr_getAutoParamTactic_x3f___closed__2 = _init_l_Lean_Expr_getAutoParamTactic_x3f___closed__2();
lean_mark_persistent(l_Lean_Expr_getAutoParamTactic_x3f___closed__2);
l_Lean_Expr_updateApp_x21___closed__1 = _init_l_Lean_Expr_updateApp_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateApp_x21___closed__1);
l_Lean_Expr_updateApp_x21___closed__2 = _init_l_Lean_Expr_updateApp_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_updateApp_x21___closed__2);
l_Lean_Expr_updateConst_x21___closed__1 = _init_l_Lean_Expr_updateConst_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateConst_x21___closed__1);
l_Lean_Expr_updateConst_x21___closed__2 = _init_l_Lean_Expr_updateConst_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_updateConst_x21___closed__2);
l_Lean_Expr_updateSort_x21___closed__1 = _init_l_Lean_Expr_updateSort_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateSort_x21___closed__1);
l_Lean_Expr_updateSort_x21___closed__2 = _init_l_Lean_Expr_updateSort_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_updateSort_x21___closed__2);
l_Lean_Expr_updateSort_x21___closed__3 = _init_l_Lean_Expr_updateSort_x21___closed__3();
lean_mark_persistent(l_Lean_Expr_updateSort_x21___closed__3);
l_Lean_Expr_updateMData_x21___closed__1 = _init_l_Lean_Expr_updateMData_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateMData_x21___closed__1);
l_Lean_Expr_updateMData_x21___closed__2 = _init_l_Lean_Expr_updateMData_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_updateMData_x21___closed__2);
l_Lean_Expr_updateMData_x21___closed__3 = _init_l_Lean_Expr_updateMData_x21___closed__3();
lean_mark_persistent(l_Lean_Expr_updateMData_x21___closed__3);
l_Lean_Expr_updateProj_x21___closed__1 = _init_l_Lean_Expr_updateProj_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateProj_x21___closed__1);
l_Lean_Expr_updateProj_x21___closed__2 = _init_l_Lean_Expr_updateProj_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_updateProj_x21___closed__2);
l_Lean_Expr_updateProj_x21___closed__3 = _init_l_Lean_Expr_updateProj_x21___closed__3();
lean_mark_persistent(l_Lean_Expr_updateProj_x21___closed__3);
l_Lean_Expr_updateForall_x21___closed__1 = _init_l_Lean_Expr_updateForall_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateForall_x21___closed__1);
l_Lean_Expr_updateForall_x21___closed__2 = _init_l_Lean_Expr_updateForall_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_updateForall_x21___closed__2);
l_Lean_Expr_updateForall_x21___closed__3 = _init_l_Lean_Expr_updateForall_x21___closed__3();
lean_mark_persistent(l_Lean_Expr_updateForall_x21___closed__3);
l_Lean_Expr_updateForallE_x21___closed__1 = _init_l_Lean_Expr_updateForallE_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateForallE_x21___closed__1);
l_Lean_Expr_updateForallE_x21___closed__2 = _init_l_Lean_Expr_updateForallE_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_updateForallE_x21___closed__2);
l_Lean_Expr_updateLambda_x21___closed__1 = _init_l_Lean_Expr_updateLambda_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateLambda_x21___closed__1);
l_Lean_Expr_updateLambda_x21___closed__2 = _init_l_Lean_Expr_updateLambda_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_updateLambda_x21___closed__2);
l_Lean_Expr_updateLambda_x21___closed__3 = _init_l_Lean_Expr_updateLambda_x21___closed__3();
lean_mark_persistent(l_Lean_Expr_updateLambda_x21___closed__3);
l_Lean_Expr_updateLambdaE_x21___closed__1 = _init_l_Lean_Expr_updateLambdaE_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateLambdaE_x21___closed__1);
l_Lean_Expr_updateLambdaE_x21___closed__2 = _init_l_Lean_Expr_updateLambdaE_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_updateLambdaE_x21___closed__2);
l_Lean_Expr_updateLet_x21___closed__1 = _init_l_Lean_Expr_updateLet_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateLet_x21___closed__1);
l_Lean_Expr_updateLet_x21___closed__2 = _init_l_Lean_Expr_updateLet_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_updateLet_x21___closed__2);
l_Lean_Expr_setPPExplicit___closed__1 = _init_l_Lean_Expr_setPPExplicit___closed__1();
lean_mark_persistent(l_Lean_Expr_setPPExplicit___closed__1);
l_Lean_Expr_setPPExplicit___closed__2 = _init_l_Lean_Expr_setPPExplicit___closed__2();
lean_mark_persistent(l_Lean_Expr_setPPExplicit___closed__2);
l_Lean_Expr_setPPExplicit___closed__3 = _init_l_Lean_Expr_setPPExplicit___closed__3();
lean_mark_persistent(l_Lean_Expr_setPPExplicit___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
