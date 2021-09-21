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
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isImplicit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object*);
static lean_object* l_Lean_Expr_letName_x21___closed__2;
static lean_object* l_Lean_Expr_ctorName___closed__7;
static lean_object* l_Lean_mkNatLit___closed__8;
LEAN_EXPORT lean_object* l_Lean_instLTLiteral;
static lean_object* l_Lean_mkLHSGoal___closed__2;
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateSort___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__28;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_mkDecIsFalse___closed__2;
static lean_object* l_Lean_Expr_bvarIdx_x21___closed__3;
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hash___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__23;
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__1;
static lean_object* l_Lean_mkNatLit___closed__4;
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__2;
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__13;
LEAN_EXPORT uint8_t l_Lean_Expr_isNatLit(lean_object*);
static lean_object* l_Lean_Expr_replaceFVar___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__30;
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__18;
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(lean_object*);
uint8_t l_UInt64_decEq(uint64_t, uint64_t);
static lean_object* l_Lean_Expr_bindingDomain_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__5;
static lean_object* l_Lean_Expr_getRevArg_x21___closed__1;
static lean_object* l_Lean_instReprBinderInfo___closed__1;
static lean_object* l_Lean_mkNatLit___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__14;
LEAN_EXPORT lean_object* l_Lean_Expr_updateConst___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkDecIsTrue___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_mkDecIsFalse___closed__1;
static lean_object* l_Lean_mkAnd___closed__2;
uint64_t l_UInt8_toUInt64(uint8_t);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__3;
uint8_t l_USize_decEq(size_t, size_t);
static lean_object* l_Lean_mkEM___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkSimpleThunkType___closed__3;
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_object* l_Lean_Expr_instHashableExpr___closed__1;
LEAN_EXPORT uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1017_(lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkAppN___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkEM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object*);
static lean_object* l_Lean_Expr_updateLambda_x21___closed__3;
uint64_t l_UInt64_add(uint64_t, uint64_t);
static lean_object* l_Lean_Expr_bindingInfo_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instHashableExprStructEq;
uint64_t l_Bool_toUInt64(uint8_t);
static lean_object* l_Lean_Expr_updateMData_x21___closed__2;
static lean_object* l_Lean_mkNatLit___closed__9;
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRevAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__4;
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_instantiateLevelParams___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object*);
static lean_object* l_Lean_Expr_updateMData_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__5;
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Expr_Data_hash(uint64_t);
LEAN_EXPORT lean_object* l_Lean_mkLHSGoal(lean_object*);
static lean_object* l_Lean_mkDecIsTrue___closed__5;
LEAN_EXPORT lean_object* l_Lean_instFVarIdSetEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_consumeAutoOptParam(lean_object*);
size_t l_USize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Literal_type___closed__5;
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__29;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__7;
static lean_object* l_Lean_Expr_ctorName___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_constName_x21___closed__1;
static lean_object* l_Lean_Expr_mvarId_x21___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__6;
uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__24;
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
static uint64_t l_Lean_Expr_mkData___closed__3;
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForBinder(uint64_t, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object*, uint8_t);
LEAN_EXPORT uint64_t l___private_Lean_Expr_0__Lean_Expr_mkDataCore(uint64_t, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubst___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_binderInfo___boxed(lean_object*);
static lean_object* l_Lean_Expr_ctorName___closed__2;
static lean_object* l_Lean_Expr_updateApp_x21___closed__2;
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
static lean_object* l_Lean_Expr_ctorName___closed__8;
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object*);
extern lean_object* l_instInhabitedNat;
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_mvarId_x21___closed__2;
static lean_object* l_Lean_mkSimpleThunkType___closed__1;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object*);
static lean_object* l_Lean_Expr_bindingBody_x21___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__8;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toCtorIdx(uint8_t);
static lean_object* l_Lean_Expr_ctorName___closed__4;
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_mkConst___spec__2(uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
static lean_object* l_Lean_Literal_type___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLetFunAnnotation(lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object*);
static lean_object* l_Lean_ExprStructEq_instBEqExprStructEq___closed__1;
static lean_object* l_Lean_Expr_updateForall_x21___closed__1;
static lean_object* l_Lean_ExprStructEq_instHashableExprStructEq___closed__1;
static lean_object* l_Lean_Expr_appFn_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_List_foldl___at_Lean_mkConst___spec__1(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_instantiateLevelParams___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_getAppArgs___closed__1;
static lean_object* l_Lean_mkNatLit___closed__2;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__22;
uint8_t l_Lean_Level_hasParam(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_970_(lean_object*, lean_object*);
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateApp_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateForall_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_Expr_fvarId_x21___closed__2;
uint8_t lean_expr_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_letName_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___boxed(lean_object*);
static lean_object* l_Lean_Expr_updateForall_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_updateForall_x21(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_mkAppRev___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_expr_instantiate(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_bindingName_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instBEqExprStructEq;
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_UInt8_decLt(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLiteral;
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object*);
uint8_t l_UInt8_add(uint8_t, uint8_t);
static lean_object* l_Lean_Expr_setPPExplicit___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprFVarId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__3;
static lean_object* l_Lean_Expr_updateLambdaE_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object*);
static lean_object* l_Lean_mkOr___closed__1;
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_natLit_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object*, lean_object*);
static lean_object* l_Lean_mkOr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_Data_approxDepth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object*, lean_object*);
extern uint64_t l_instInhabitedUInt64;
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at_Lean_Expr_setPPExplicit___spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_letFunAnnotation_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_309____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubstArray(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBTree_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_bindingName_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqBinderInfo;
static lean_object* l_Lean_Expr_updateSort_x21___closed__3;
LEAN_EXPORT uint64_t l_Lean_BinderInfo_toUInt64(uint8_t);
static lean_object* l_Lean_Expr_letName_x21___closed__3;
static lean_object* l_Lean_mkEM___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambda_x21(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98_(lean_object*, lean_object*);
static lean_object* l_Lean_instHashableFVarId___closed__1;
static lean_object* l_Lean_Expr_updateForall_x21___closed__2;
static lean_object* l_Lean_Expr_updateLambdaE_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprFVarId___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_getOptParamDefault_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___rarg___lambda__1___boxed(lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateSort_x21(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object*, uint8_t);
static lean_object* l_Lean_Expr_constName_x21___closed__3;
static lean_object* l_Lean_Literal_type___closed__6;
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateConst_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__15;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__25;
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFVarIdSetInhabited;
LEAN_EXPORT uint8_t lean_expr_has_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object*);
static lean_object* l_Lean_mkNatLit___closed__6;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Expr_ctorName___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_BinderInfo_noConfusion___rarg___closed__1;
static lean_object* l_Lean_Expr_bindingBody_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object*);
static lean_object* l_Lean_isLHSGoal_x3f___closed__1;
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object*);
static uint64_t l_Lean_Expr_mkData___closed__2;
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_letFunAnnotation_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isStrictImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object*, lean_object*, lean_object*);
uint32_t l_UInt64_toUInt32(uint64_t);
lean_object* l_Lean_mkFreshId___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLiteral;
static lean_object* l_Lean_Expr_instToStringExpr___closed__1;
LEAN_EXPORT uint64_t l_Lean_Expr_data(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubstArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__10;
LEAN_EXPORT lean_object* l_Lean_Expr_updateProj_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkDecIsTrue___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instDecidableLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__12;
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicitForExposingMVars___spec__1(size_t, size_t, lean_object*);
uint64_t l_Lean_Name_hash(lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasFVar(uint64_t);
static lean_object* l_Lean_Expr_instBEqExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVarEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_approxDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object*);
static lean_object* l_Lean_Expr_fvarId_x21___closed__1;
static lean_object* l_Lean_Expr_updateConst_x21___closed__2;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__20;
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instHashableExpr;
static lean_object* l_Lean_mkDecIsTrue___closed__2;
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l_Lean_Expr_mvarId_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object*);
static lean_object* l_Lean_Literal_type___closed__1;
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_bindingDomain_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object*);
static lean_object* l_Lean_Expr_getRevArg_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ctorName___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_isLHSGoal_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_natLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_isCharLit___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_970____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_mkEM___closed__5;
static lean_object* l_Lean_mkOr___closed__2;
static lean_object* l_Lean_Expr_mdataExpr_x21___closed__3;
static lean_object* l_Lean_Literal_type___closed__4;
static lean_object* l_Lean_mkDecIsTrue___closed__4;
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateMData_x21(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelMVar(uint64_t);
lean_object* lean_expr_dbg_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_updateConst_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForLet(uint64_t, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
static lean_object* l_Lean_mkSimpleThunk___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_updateProj_x21___closed__3;
static lean_object* l_Lean_Literal_type___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_205_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_30_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLetFun___boxed(lean_object*);
static lean_object* l_Lean_mkSimpleThunk___closed__1;
static lean_object* l_Lean_Expr_appFn_x21___closed__1;
static lean_object* l_Lean_Expr_updateApp_x21___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_fvarId_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isLetFun(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqData__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isAuxDecl(uint8_t);
static lean_object* l_Lean_Expr_bindingName_x21___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_nonDepLet(uint64_t);
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint64_t l_UInt64_land(uint64_t, uint64_t);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__11;
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_constName_x21___closed__2;
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object*, lean_object*);
uint8_t lean_expr_quick_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object*);
static lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__1;
LEAN_EXPORT uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_MData_empty;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object*);
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object*);
static lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__2;
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object*);
static lean_object* l_Lean_instInhabitedLiteral___closed__1;
static lean_object* l_Lean_Expr_updateSort_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object*);
static lean_object* l_Lean_Expr_setPPExplicit___closed__1;
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_setPPExplicit___closed__2;
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object*);
static lean_object* l_Lean_Expr_updateProj_x21___closed__2;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__16;
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRevAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ctorName___closed__9;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkNatLit___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324_(uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedBinderInfo;
static lean_object* l_Lean_Expr_updateLambda_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_instBEqFVarId;
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarId;
static lean_object* l_Lean_Expr_updateProj_x21___closed__1;
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__4;
static lean_object* l_Lean_mkNatLit___closed__3;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__26;
extern lean_object* l_Lean_instInhabitedMVarId;
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object*);
static lean_object* l_Lean_Expr_updateLambda_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateMData___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object*);
static lean_object* l_Lean_instHashableBinderInfo___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkDataCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object*);
static lean_object* l_Lean_Expr_ctorName___closed__10;
static lean_object* l_Lean_Expr_constLevels_x21___closed__1;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_mkAnd___closed__3;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_mkAppRev___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Expr_getOptParamDefault_x3f___closed__1;
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object*);
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_UInt64_toUInt8(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_setPPExplicit___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object*);
static lean_object* l_Lean_Expr_constLevels_x21___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkDataCore___boxed__const__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__27;
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgsAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Literal_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_instInhabitedData__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__9;
static lean_object* l_Lean_instBEqLiteral___closed__1;
LEAN_EXPORT lean_object* l_Lean_instHashableBinderInfo;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object*);
extern lean_object* l_Lean_KVMap_empty;
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_instantiateLevelParamsArray___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
static lean_object* l_Lean_Expr_updateMData_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed__const__1;
static lean_object* l_Lean_Expr_bvarIdx_x21___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isStrictImplicit___boxed(lean_object*);
static lean_object* l_Lean_mkNatLit___closed__10;
static lean_object* l_Lean_mkAnd___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubst(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedExpr___closed__2;
uint64_t l_UInt64_shiftLeft(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object*);
static uint64_t l_Lean_instInhabitedExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Literal_lt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_insertCore(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
static lean_object* l_Lean_Expr_appArg_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambda_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_30____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_appFn_x21___closed__2;
static lean_object* l_Lean_mkNatLit___closed__5;
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__5;
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo;
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_bvarIdx_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_appArg_x21___closed__1;
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instToStringExpr;
static lean_object* l_Lean_mkEM___closed__4;
uint64_t l_UInt32_toUInt64(uint32_t);
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instToStringExprStructEq___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkSimpleThunkType___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicit___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isAuxDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_mkConst___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_instantiateLevelParamsArray___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l_Lean_Expr_setPPUniverses___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object*);
static lean_object* l_Lean_Expr_updateLet_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
static uint64_t l_Lean_Expr_mkData___closed__4;
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_hash___boxed(lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__19;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__21;
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object*);
static lean_object* l_Lean_instHashableLiteral___closed__1;
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicitForExposingMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFVarIdHashSetInhabited;
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_instForInFVarIdSetFVarId___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_updateProj___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object*);
LEAN_EXPORT uint64_t lean_expr_hash(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFVarIdHashSetEmptyCollection;
static lean_object* l_Lean_instReprLiteral___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_309_(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableFVarId;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableLiteral;
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ctorName___closed__12;
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instForInFVarIdSetFVarId___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_instBEqExpr;
LEAN_EXPORT lean_object* l_Lean_instInhabitedExprStructEq;
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_mkConst___spec__3(uint8_t, lean_object*);
static lean_object* l_Lean_Expr_ctorName___closed__6;
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object*, lean_object*);
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_instBEqFVarId___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqData__1(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkAppN___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instToStringExprStructEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isExplicit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
static uint64_t l_Lean_Expr_mkData___closed__1;
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_mkConst___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object*);
static lean_object* l_Lean_mkDecIsFalse___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object*);
static lean_object* l_Lean_Expr_updateLet_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at_Lean_Expr_setPPExplicit___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_nonDepLet___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Level_instantiateParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ctorName___closed__11;
static lean_object* l_Lean_mkNot___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__6;
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicit___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkLHSGoal___closed__1;
uint64_t l_UInt64_shiftRight(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_lit_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqLiteral;
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instDecidableLt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__8;
static lean_object* l_Lean_mkLetFunAnnotation___closed__2;
static lean_object* l_Lean_instBEqBinderInfo___closed__1;
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__17;
static lean_object* l_Lean_Expr_isCharLit___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_BinderInfo_hash(uint8_t);
static lean_object* l_Lean_Expr_setPPUniverses___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_approxDepth(uint64_t);
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_mdataExpr_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkNot___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateLet_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Literal_lt(lean_object*, lean_object*);
static lean_object* l_Lean_mkLetFunAnnotation___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_updateForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object*);
static lean_object* l_Lean_mkNot___closed__2;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object*);
static lean_object* l_Lean_Expr_updateForallE_x21___closed__2;
lean_object* lean_expr_instantiate_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Expr_getRevArg_x21___closed__2;
static lean_object* l_Lean_Expr_updateForallE_x21___closed__1;
static lean_object* l_Lean_instFVarIdHashSetInhabited___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit(lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_updateSort_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object*);
static lean_object* l_Lean_Expr_mdataExpr_x21___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__2;
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isNatLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____boxed(lean_object*, lean_object*);
lean_object* l_List_mapTRAux___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__3;
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_mkConst___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object*);
static lean_object* l_Lean_Expr_bindingInfo_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1017____boxed(lean_object*);
static lean_object* l_Lean_Expr_isCharLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
static lean_object* l_Lean_mkAnnotation___closed__1;
LEAN_EXPORT uint64_t l_Lean_Expr_mkData(uint64_t, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__1;
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
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_30_(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_30____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_30_(x_1, x_2);
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
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_30____boxed), 2, 0);
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
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Literal.natVal");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__2;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Literal.strVal");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__7;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98_(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_unsigned_to_nat(1024u);
x_5 = lean_nat_dec_le(x_4, x_2);
x_6 = l_Nat_repr(x_3);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__3;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
if (x_5 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__4;
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = 0;
x_13 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = l_Repr_addAppParen(x_13, x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__5;
x_16 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
x_17 = 0;
x_18 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = l_Repr_addAppParen(x_18, x_2);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_unsigned_to_nat(1024u);
x_22 = lean_nat_dec_le(x_21, x_2);
x_23 = l_String_quote(x_20);
lean_dec(x_20);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__8;
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
if (x_22 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__4;
x_28 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = 0;
x_30 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = l_Repr_addAppParen(x_30, x_2);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_32 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__5;
x_33 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
x_34 = 0;
x_35 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = l_Repr_addAppParen(x_35, x_2);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprLiteral___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprLiteral() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instReprLiteral___closed__1;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Literal_hash(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint64_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_uint64_of_nat(x_2);
return x_3;
}
else
{
lean_object* x_4; uint64_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_string_hash(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Literal_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
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
LEAN_EXPORT uint8_t l_Lean_Literal_lt(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Literal_lt___boxed(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_instLTLiteral() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_instDecidableLt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Literal_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_instDecidableLt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_BinderInfo_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_BinderInfo_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_BinderInfo_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_BinderInfo_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_BinderInfo_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_BinderInfo_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_BinderInfo_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
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
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_309_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_BinderInfo_toCtorIdx(x_1);
x_4 = l_Lean_BinderInfo_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_309____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_309_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instBEqBinderInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_309____boxed), 2, 0);
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
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.BinderInfo.default");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__4;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__2;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__5;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__2;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__5;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.BinderInfo.implicit");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__4;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__8;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__10() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__9;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__5;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__8;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.BinderInfo.strictImplicit");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__4;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__14;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__16() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__15;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__5;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__14;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__18() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__17;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.BinderInfo.instImplicit");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__4;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__20;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__22() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__21;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__5;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__20;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__24() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__23;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.BinderInfo.auxDecl");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__25;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__4;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__26;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__28() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__27;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__5;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__26;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__30() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__29;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324_(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__4;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__6;
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
case 1:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1024u);
x_10 = lean_nat_dec_le(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__10;
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__12;
x_14 = l_Repr_addAppParen(x_13, x_2);
return x_14;
}
}
case 2:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_nat_dec_le(x_15, x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__16;
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__18;
x_20 = l_Repr_addAppParen(x_19, x_2);
return x_20;
}
}
case 3:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(1024u);
x_22 = lean_nat_dec_le(x_21, x_2);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__22;
x_24 = l_Repr_addAppParen(x_23, x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__24;
x_26 = l_Repr_addAppParen(x_25, x_2);
return x_26;
}
}
default: 
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_unsigned_to_nat(1024u);
x_28 = lean_nat_dec_le(x_27, x_2);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__28;
x_30 = l_Repr_addAppParen(x_29, x_2);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__30;
x_32 = l_Repr_addAppParen(x_31, x_2);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_instReprBinderInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprBinderInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instReprBinderInfo___closed__1;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_BinderInfo_hash(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
uint64_t x_2; 
x_2 = 947;
return x_2;
}
case 1:
{
uint64_t x_3; 
x_3 = 1019;
return x_3;
}
case 2:
{
uint64_t x_4; 
x_4 = 1087;
return x_4;
}
case 3:
{
uint64_t x_5; 
x_5 = 1153;
return x_5;
}
default: 
{
uint64_t x_6; 
x_6 = 1229;
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_BinderInfo_hash___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_BinderInfo_hash(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isExplicit(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isExplicit___boxed(lean_object* x_1) {
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
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object* x_1) {
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
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isImplicit(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 1)
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
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isImplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_BinderInfo_isImplicit(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isStrictImplicit(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 2)
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
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isStrictImplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_BinderInfo_isStrictImplicit(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isAuxDecl(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isAuxDecl___boxed(lean_object* x_1) {
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
LEAN_EXPORT uint64_t l_Lean_Expr_Data_hash(uint64_t x_1) {
_start:
{
uint32_t x_2; uint64_t x_3; 
x_2 = ((uint32_t)x_1);
x_3 = ((uint64_t)x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_hash(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqData__1(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 == x_2;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqData__1___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Lean_Expr_Data_approxDepth(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint8_t x_6; 
x_2 = 40;
x_3 = x_1 >> x_2 % 64;
x_4 = 255;
x_5 = x_3 & x_4;
x_6 = ((uint8_t)x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_approxDepth___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_approxDepth(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint32_t x_4; 
x_2 = 48;
x_3 = x_1 >> x_2 % 64;
x_4 = ((uint32_t)x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object* x_1) {
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
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasFVar(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint8_t x_6; 
x_2 = 32;
x_3 = x_1 >> x_2 % 64;
x_4 = 1;
x_5 = x_3 & x_4;
x_6 = x_5 == x_4;
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object* x_1) {
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
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint8_t x_6; 
x_2 = 33;
x_3 = x_1 >> x_2 % 64;
x_4 = 1;
x_5 = x_3 & x_4;
x_6 = x_5 == x_4;
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object* x_1) {
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
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelMVar(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint8_t x_6; 
x_2 = 34;
x_3 = x_1 >> x_2 % 64;
x_4 = 1;
x_5 = x_3 & x_4;
x_6 = x_5 == x_4;
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object* x_1) {
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
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint8_t x_6; 
x_2 = 35;
x_3 = x_1 >> x_2 % 64;
x_4 = 1;
x_5 = x_3 & x_4;
x_6 = x_5 == x_4;
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object* x_1) {
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
LEAN_EXPORT uint8_t l_Lean_Expr_Data_nonDepLet(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint8_t x_6; 
x_2 = 36;
x_3 = x_1 >> x_2 % 64;
x_4 = 1;
x_5 = x_3 & x_4;
x_6 = x_5 == x_4;
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_Data_nonDepLet___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_Data_binderInfo___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object* x_1) {
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(16777216u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Expr.0.Lean.Expr.mkDataCore");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bound variable index is too big");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__3;
x_3 = lean_unsigned_to_nat(135u);
x_4 = lean_unsigned_to_nat(44u);
x_5 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__4;
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
LEAN_EXPORT uint64_t l___private_Lean_Expr_0__Lean_Expr_mkDataCore(uint64_t x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8, uint8_t x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_11 = lean_nat_dec_lt(x_10, x_2);
if (x_11 == 0)
{
uint32_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; 
x_12 = ((uint32_t)x_1);
x_13 = ((uint64_t)x_12);
x_14 = (uint64_t)x_4;
x_15 = 32;
x_16 = x_14 << x_15 % 64;
x_17 = x_13 + x_16;
x_18 = (uint64_t)x_5;
x_19 = 33;
x_20 = x_18 << x_19 % 64;
x_21 = x_17 + x_20;
x_22 = (uint64_t)x_6;
x_23 = 34;
x_24 = x_22 << x_23 % 64;
x_25 = x_21 + x_24;
x_26 = (uint64_t)x_7;
x_27 = 35;
x_28 = x_26 << x_27 % 64;
x_29 = x_25 + x_28;
x_30 = (uint64_t)x_8;
x_31 = 36;
x_32 = x_30 << x_31 % 64;
x_33 = x_29 + x_32;
x_34 = (uint64_t)x_9;
x_35 = 37;
x_36 = x_34 << x_35 % 64;
x_37 = x_33 + x_36;
x_38 = ((uint64_t)x_3);
x_39 = 40;
x_40 = x_38 << x_39 % 64;
x_41 = x_37 + x_40;
x_42 = lean_uint64_of_nat(x_2);
x_43 = 48;
x_44 = x_42 << x_43 % 64;
x_45 = x_41 + x_44;
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; 
x_46 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__5;
x_47 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___boxed__const__1;
x_48 = lean_panic_fn(x_47, x_46);
x_49 = lean_unbox_uint64(x_48);
lean_dec(x_48);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkDataCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint64_t x_18; lean_object* x_19; 
x_10 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = lean_unbox(x_7);
lean_dec(x_7);
x_16 = lean_unbox(x_8);
lean_dec(x_8);
x_17 = lean_unbox(x_9);
lean_dec(x_9);
x_18 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore(x_10, x_2, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_2);
x_19 = lean_box_uint64(x_18);
return x_19;
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
x_3 = x_2 << x_1 % 64;
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
x_3 = x_2 << x_1 % 64;
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
LEAN_EXPORT uint64_t l_Lean_Expr_mkData(uint64_t x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_9 = lean_nat_dec_lt(x_8, x_2);
if (x_9 == 0)
{
uint32_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; 
x_10 = ((uint32_t)x_1);
x_11 = ((uint64_t)x_10);
x_12 = (uint64_t)x_4;
x_13 = 32;
x_14 = x_12 << x_13 % 64;
x_15 = x_11 + x_14;
x_16 = (uint64_t)x_5;
x_17 = 33;
x_18 = x_16 << x_17 % 64;
x_19 = x_15 + x_18;
x_20 = (uint64_t)x_6;
x_21 = 34;
x_22 = x_20 << x_21 % 64;
x_23 = x_19 + x_22;
x_24 = (uint64_t)x_7;
x_25 = 35;
x_26 = x_24 << x_25 % 64;
x_27 = x_23 + x_26;
x_28 = l_Lean_Expr_mkData___closed__2;
x_29 = x_27 + x_28;
x_30 = l_Lean_Expr_mkData___closed__4;
x_31 = x_29 + x_30;
x_32 = ((uint64_t)x_3);
x_33 = 40;
x_34 = x_32 << x_33 % 64;
x_35 = x_31 + x_34;
x_36 = lean_uint64_of_nat(x_2);
x_37 = 48;
x_38 = x_36 << x_37 % 64;
x_39 = x_35 + x_38;
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; 
x_40 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__5;
x_41 = l_Lean_Expr_mkData___boxed__const__1;
x_42 = lean_panic_fn(x_41, x_40);
x_43 = lean_unbox_uint64(x_42);
lean_dec(x_42);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint64_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint64_t x_14; lean_object* x_15; 
x_8 = lean_unbox_uint64(x_1);
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
x_14 = l_Lean_Expr_mkData(x_8, x_2, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
x_15 = lean_box_uint64(x_14);
return x_15;
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
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForBinder(uint64_t x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_10 = lean_nat_dec_lt(x_9, x_2);
if (x_10 == 0)
{
uint32_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; 
x_11 = ((uint32_t)x_1);
x_12 = ((uint64_t)x_11);
x_13 = (uint64_t)x_4;
x_14 = 32;
x_15 = x_13 << x_14 % 64;
x_16 = x_12 + x_15;
x_17 = (uint64_t)x_5;
x_18 = 33;
x_19 = x_17 << x_18 % 64;
x_20 = x_16 + x_19;
x_21 = (uint64_t)x_6;
x_22 = 34;
x_23 = x_21 << x_22 % 64;
x_24 = x_20 + x_23;
x_25 = (uint64_t)x_7;
x_26 = 35;
x_27 = x_25 << x_26 % 64;
x_28 = x_24 + x_27;
x_29 = l_Lean_Expr_mkData___closed__2;
x_30 = x_28 + x_29;
x_31 = (uint64_t)x_8;
x_32 = 37;
x_33 = x_31 << x_32 % 64;
x_34 = x_30 + x_33;
x_35 = ((uint64_t)x_3);
x_36 = 40;
x_37 = x_35 << x_36 % 64;
x_38 = x_34 + x_37;
x_39 = lean_uint64_of_nat(x_2);
x_40 = 48;
x_41 = x_39 << x_40 % 64;
x_42 = x_38 + x_41;
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; 
x_43 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__5;
x_44 = l_Lean_Expr_mkDataForBinder___boxed__const__1;
x_45 = lean_panic_fn(x_44, x_43);
x_46 = lean_unbox_uint64(x_45);
lean_dec(x_45);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint64_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint64_t x_16; lean_object* x_17; 
x_9 = lean_unbox_uint64(x_1);
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
x_16 = l_Lean_Expr_mkDataForBinder(x_9, x_2, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_2);
x_17 = lean_box_uint64(x_16);
return x_17;
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
LEAN_EXPORT uint64_t l_Lean_Expr_mkDataForLet(uint64_t x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__1;
x_10 = lean_nat_dec_lt(x_9, x_2);
if (x_10 == 0)
{
uint32_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; 
x_11 = ((uint32_t)x_1);
x_12 = ((uint64_t)x_11);
x_13 = (uint64_t)x_4;
x_14 = 32;
x_15 = x_13 << x_14 % 64;
x_16 = x_12 + x_15;
x_17 = (uint64_t)x_5;
x_18 = 33;
x_19 = x_17 << x_18 % 64;
x_20 = x_16 + x_19;
x_21 = (uint64_t)x_6;
x_22 = 34;
x_23 = x_21 << x_22 % 64;
x_24 = x_20 + x_23;
x_25 = (uint64_t)x_7;
x_26 = 35;
x_27 = x_25 << x_26 % 64;
x_28 = x_24 + x_27;
x_29 = (uint64_t)x_8;
x_30 = 36;
x_31 = x_29 << x_30 % 64;
x_32 = x_28 + x_31;
x_33 = l_Lean_Expr_mkData___closed__4;
x_34 = x_32 + x_33;
x_35 = ((uint64_t)x_3);
x_36 = 40;
x_37 = x_35 << x_36 % 64;
x_38 = x_34 + x_37;
x_39 = lean_uint64_of_nat(x_2);
x_40 = 48;
x_41 = x_39 << x_40 % 64;
x_42 = x_38 + x_41;
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; 
x_43 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__5;
x_44 = l_Lean_Expr_mkDataForLet___boxed__const__1;
x_45 = lean_panic_fn(x_44, x_43);
x_46 = lean_unbox_uint64(x_45);
lean_dec(x_45);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint64_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint64_t x_16; lean_object* x_17; 
x_9 = lean_unbox_uint64(x_1);
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
x_16 = l_Lean_Expr_mkDataForLet(x_9, x_2, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_2);
x_17 = lean_box_uint64(x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_instInhabitedFVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_970_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_970____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_970_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqFVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_970____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instBEqFVarId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instBEqFVarId___closed__1;
return x_1;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1017_(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; 
x_2 = 0;
x_3 = l_Lean_Name_hash(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1017____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1017_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableFVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1017____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instHashableFVarId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instHashableFVarId___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprFVarId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Name_reprPrec(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprFVarId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instReprFVarId(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instFVarIdSetInhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_instFVarIdSetEmptyCollection() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_instForInFVarIdSetFVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instForInFVarIdSetFVarId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instForInFVarIdSetFVarId___closed__1;
x_2 = lean_alloc_closure((void*)(l_Std_RBTree_forIn___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
lean_closure_set(x_2, 2, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instForInFVarIdSetFVarId___closed__2;
return x_2;
}
}
static lean_object* _init_l_Lean_instFVarIdHashSetInhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instFVarIdHashSetInhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instFVarIdHashSetInhabited___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_instFVarIdHashSetEmptyCollection() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instFVarIdHashSetInhabited___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static uint64_t _init_l_Lean_instInhabitedExpr___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_instInhabitedExpr___closed__1;
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
x_1 = l_Lean_instInhabitedExpr___closed__2;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_data(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_data(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
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
x_1 = lean_mk_string("sort");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("const");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("app");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lam");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("forallE");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("letE");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lit");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mdata");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("proj");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object* x_1) {
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
x_5 = l_Lean_Expr_ctorName___closed__4;
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_ctorName___closed__5;
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_ctorName___closed__6;
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_ctorName___closed__7;
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_ctorName___closed__8;
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_ctorName___closed__9;
return x_10;
}
case 9:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_ctorName___closed__10;
return x_11;
}
case 10:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_ctorName___closed__11;
return x_12;
}
default: 
{
lean_object* x_13; 
x_13 = l_Lean_Expr_ctorName___closed__12;
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_ctorName(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
uint64_t x_2; uint64_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_3 = l_Lean_Expr_Data_hash(x_2);
return x_3;
}
case 5:
{
uint64_t x_4; uint64_t x_5; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_5 = l_Lean_Expr_Data_hash(x_4);
return x_5;
}
case 6:
{
uint64_t x_6; uint64_t x_7; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_7 = l_Lean_Expr_Data_hash(x_6);
return x_7;
}
case 7:
{
uint64_t x_8; uint64_t x_9; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_9 = l_Lean_Expr_Data_hash(x_8);
return x_9;
}
case 8:
{
uint64_t x_10; uint64_t x_11; 
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_11 = l_Lean_Expr_Data_hash(x_10);
return x_11;
}
case 10:
{
uint64_t x_12; uint64_t x_13; 
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_13 = l_Lean_Expr_Data_hash(x_12);
return x_13;
}
case 11:
{
uint64_t x_14; uint64_t x_15; 
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_15 = l_Lean_Expr_Data_hash(x_14);
return x_15;
}
default: 
{
uint64_t x_16; uint64_t x_17; 
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_17 = l_Lean_Expr_Data_hash(x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
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
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasFVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasExprMVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasLevelMVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasMVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasLevelParam(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_approxDepth(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
uint64_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_3 = l_Lean_Expr_Data_approxDepth(x_2);
return x_3;
}
case 5:
{
uint64_t x_4; uint8_t x_5; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_5 = l_Lean_Expr_Data_approxDepth(x_4);
return x_5;
}
case 6:
{
uint64_t x_6; uint8_t x_7; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_7 = l_Lean_Expr_Data_approxDepth(x_6);
return x_7;
}
case 7:
{
uint64_t x_8; uint8_t x_9; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_9 = l_Lean_Expr_Data_approxDepth(x_8);
return x_9;
}
case 8:
{
uint64_t x_10; uint8_t x_11; 
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_11 = l_Lean_Expr_Data_approxDepth(x_10);
return x_11;
}
case 10:
{
uint64_t x_12; uint8_t x_13; 
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_13 = l_Lean_Expr_Data_approxDepth(x_12);
return x_13;
}
case 11:
{
uint64_t x_14; uint8_t x_15; 
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_15 = l_Lean_Expr_Data_approxDepth(x_14);
return x_15;
}
default: 
{
uint64_t x_16; uint8_t x_17; 
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_17 = l_Lean_Expr_Data_approxDepth(x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_approxDepth(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_looseBVarRange(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_binderInfo(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t lean_expr_hash(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = l_Lean_Expr_hash(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_expr_hash(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_hasFVar(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_fvar(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_hasExprMVar(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_expr_mvar(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_hasLevelMVar(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_level_mvar(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_expr_has_mvar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_hasMVar(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVarEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_mvar(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_hasLevelParam(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_level_param(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_expr_loose_bvar_range(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_binderInfo(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_binder_info(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_List_foldl___at_Lean_mkConst___spec__1(uint64_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_Level_hash(x_3);
x_6 = lean_uint64_mix_hash(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_mkConst___spec__2(uint8_t x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_mkConst___spec__3(uint8_t x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; 
x_3 = 5;
x_4 = l_Lean_Name_hash(x_1);
x_5 = 7;
x_6 = l_List_foldl___at_Lean_mkConst___spec__1(x_5, x_2);
x_7 = lean_uint64_mix_hash(x_4, x_6);
x_8 = lean_uint64_mix_hash(x_3, x_7);
x_9 = 0;
x_10 = 0;
x_11 = l_List_foldr___at_Lean_mkConst___spec__2(x_10, x_2);
x_12 = l_List_foldr___at_Lean_mkConst___spec__3(x_10, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Expr_mkData(x_8, x_13, x_9, x_10, x_10, x_11, x_12);
x_15 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set_uint64(x_15, sizeof(void*)*2, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_mkConst___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_List_foldl___at_Lean_mkConst___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_mkConst___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_mkConst___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_1; 
x_1 = lean_mk_string("String");
return x_1;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Literal_type___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Literal_type___closed__5;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object* x_1) {
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
x_3 = l_Lean_Literal_type___closed__6;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Literal_type(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_lit_type(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Literal_type(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint64_t x_9; lean_object* x_10; 
x_2 = 7;
x_3 = lean_uint64_of_nat(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_1, x_5);
x_7 = 0;
x_8 = 0;
x_9 = l_Lean_Expr_mkData(x_4, x_6, x_7, x_8, x_8, x_8, x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set_uint64(x_10, sizeof(void*)*1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; uint64_t x_10; lean_object* x_11; 
x_2 = 11;
x_3 = l_Lean_Level_hash(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
x_5 = 0;
x_6 = l_Lean_Level_hasMVar(x_1);
x_7 = l_Lean_Level_hasParam(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = 0;
x_10 = l_Lean_Expr_mkData(x_4, x_8, x_5, x_9, x_9, x_6, x_7);
x_11 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set_uint64(x_11, sizeof(void*)*1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint64_t x_9; lean_object* x_10; 
x_2 = 13;
x_3 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1017_(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
x_5 = 0;
x_6 = lean_unsigned_to_nat(0u);
x_7 = 1;
x_8 = 0;
x_9 = l_Lean_Expr_mkData(x_4, x_6, x_5, x_7, x_8, x_8, x_8);
x_10 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set_uint64(x_10, sizeof(void*)*1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint64_t x_9; lean_object* x_10; 
x_2 = 17;
x_3 = l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_205_(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
x_5 = 0;
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = 1;
x_9 = l_Lean_Expr_mkData(x_4, x_6, x_5, x_7, x_8, x_7, x_7);
x_10 = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set_uint64(x_10, sizeof(void*)*1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint64_t x_14; lean_object* x_15; 
x_3 = l_Lean_Expr_approxDepth(x_2);
x_4 = 1;
x_5 = x_3 + x_4;
x_6 = ((uint64_t)x_5);
x_7 = l_Lean_Expr_hash(x_2);
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = l_Lean_Expr_looseBVarRange(x_2);
x_10 = l_Lean_Expr_hasFVar(x_2);
x_11 = l_Lean_Expr_hasExprMVar(x_2);
x_12 = l_Lean_Expr_hasLevelMVar(x_2);
x_13 = l_Lean_Expr_hasLevelParam(x_2);
x_14 = l_Lean_Expr_mkData(x_8, x_9, x_5, x_10, x_11, x_12, x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set_uint64(x_15, sizeof(void*)*2, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint64_t x_19; lean_object* x_20; 
x_4 = l_Lean_Expr_approxDepth(x_3);
x_5 = 1;
x_6 = x_4 + x_5;
x_7 = ((uint64_t)x_6);
x_8 = l_Lean_Name_hash(x_1);
x_9 = lean_uint64_of_nat(x_2);
x_10 = l_Lean_Expr_hash(x_3);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = lean_uint64_mix_hash(x_8, x_11);
x_13 = lean_uint64_mix_hash(x_7, x_12);
x_14 = l_Lean_Expr_looseBVarRange(x_3);
x_15 = l_Lean_Expr_hasFVar(x_3);
x_16 = l_Lean_Expr_hasExprMVar(x_3);
x_17 = l_Lean_Expr_hasLevelMVar(x_3);
x_18 = l_Lean_Expr_hasLevelParam(x_3);
x_19 = l_Lean_Expr_mkData(x_13, x_14, x_6, x_15, x_16, x_17, x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_3);
lean_ctor_set_uint64(x_20, sizeof(void*)*3, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; 
x_3 = l_Lean_Expr_approxDepth(x_1);
x_4 = l_Lean_Expr_approxDepth(x_2);
x_5 = x_4 < x_3;
x_6 = 1;
x_7 = l_Lean_Expr_hash(x_1);
x_8 = l_Lean_Expr_hash(x_2);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = l_Lean_Expr_looseBVarRange(x_1);
x_11 = l_Lean_Expr_looseBVarRange(x_2);
x_12 = lean_nat_dec_lt(x_11, x_10);
x_13 = l_Lean_Expr_hasFVar(x_1);
x_14 = l_Lean_Expr_hasExprMVar(x_1);
x_15 = l_Lean_Expr_hasLevelMVar(x_1);
x_16 = l_Lean_Expr_hasLevelParam(x_1);
if (x_5 == 0)
{
x_17 = x_4;
goto block_87;
}
else
{
x_17 = x_3;
goto block_87;
}
block_87:
{
uint8_t x_18; uint64_t x_19; uint64_t x_20; lean_object* x_21; lean_object* x_54; 
x_18 = x_17 + x_6;
x_19 = ((uint64_t)x_18);
x_20 = lean_uint64_mix_hash(x_19, x_9);
if (x_12 == 0)
{
lean_dec(x_10);
if (x_13 == 0)
{
x_21 = x_11;
goto block_53;
}
else
{
x_54 = x_11;
goto block_86;
}
}
else
{
lean_dec(x_11);
if (x_13 == 0)
{
x_21 = x_10;
goto block_53;
}
else
{
x_54 = x_10;
goto block_86;
}
}
block_53:
{
uint8_t x_22; 
x_22 = l_Lean_Expr_hasFVar(x_2);
if (x_14 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Expr_hasExprMVar(x_2);
if (x_15 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Expr_hasLevelMVar(x_2);
if (x_16 == 0)
{
uint8_t x_25; uint64_t x_26; lean_object* x_27; 
x_25 = l_Lean_Expr_hasLevelParam(x_2);
x_26 = l_Lean_Expr_mkData(x_20, x_21, x_18, x_22, x_23, x_24, x_25);
lean_dec(x_21);
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
x_29 = l_Lean_Expr_mkData(x_20, x_21, x_18, x_22, x_23, x_24, x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set_uint64(x_30, sizeof(void*)*2, x_29);
return x_30;
}
}
else
{
if (x_16 == 0)
{
uint8_t x_31; uint8_t x_32; uint64_t x_33; lean_object* x_34; 
x_31 = l_Lean_Expr_hasLevelParam(x_2);
x_32 = 1;
x_33 = l_Lean_Expr_mkData(x_20, x_21, x_18, x_22, x_23, x_32, x_31);
lean_dec(x_21);
x_34 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_2);
lean_ctor_set_uint64(x_34, sizeof(void*)*2, x_33);
return x_34;
}
else
{
uint8_t x_35; uint64_t x_36; lean_object* x_37; 
x_35 = 1;
x_36 = l_Lean_Expr_mkData(x_20, x_21, x_18, x_22, x_23, x_35, x_35);
lean_dec(x_21);
x_37 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_2);
lean_ctor_set_uint64(x_37, sizeof(void*)*2, x_36);
return x_37;
}
}
}
else
{
if (x_15 == 0)
{
uint8_t x_38; 
x_38 = l_Lean_Expr_hasLevelMVar(x_2);
if (x_16 == 0)
{
uint8_t x_39; uint8_t x_40; uint64_t x_41; lean_object* x_42; 
x_39 = l_Lean_Expr_hasLevelParam(x_2);
x_40 = 1;
x_41 = l_Lean_Expr_mkData(x_20, x_21, x_18, x_22, x_40, x_38, x_39);
lean_dec(x_21);
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
x_44 = l_Lean_Expr_mkData(x_20, x_21, x_18, x_22, x_43, x_38, x_43);
lean_dec(x_21);
x_45 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_2);
lean_ctor_set_uint64(x_45, sizeof(void*)*2, x_44);
return x_45;
}
}
else
{
if (x_16 == 0)
{
uint8_t x_46; uint8_t x_47; uint64_t x_48; lean_object* x_49; 
x_46 = l_Lean_Expr_hasLevelParam(x_2);
x_47 = 1;
x_48 = l_Lean_Expr_mkData(x_20, x_21, x_18, x_22, x_47, x_47, x_46);
lean_dec(x_21);
x_49 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_2);
lean_ctor_set_uint64(x_49, sizeof(void*)*2, x_48);
return x_49;
}
else
{
uint8_t x_50; uint64_t x_51; lean_object* x_52; 
x_50 = 1;
x_51 = l_Lean_Expr_mkData(x_20, x_21, x_18, x_22, x_50, x_50, x_50);
lean_dec(x_21);
x_52 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_2);
lean_ctor_set_uint64(x_52, sizeof(void*)*2, x_51);
return x_52;
}
}
}
}
block_86:
{
if (x_14 == 0)
{
uint8_t x_55; 
x_55 = l_Lean_Expr_hasExprMVar(x_2);
if (x_15 == 0)
{
uint8_t x_56; 
x_56 = l_Lean_Expr_hasLevelMVar(x_2);
if (x_16 == 0)
{
uint8_t x_57; uint8_t x_58; uint64_t x_59; lean_object* x_60; 
x_57 = l_Lean_Expr_hasLevelParam(x_2);
x_58 = 1;
x_59 = l_Lean_Expr_mkData(x_20, x_54, x_18, x_58, x_55, x_56, x_57);
lean_dec(x_54);
x_60 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_2);
lean_ctor_set_uint64(x_60, sizeof(void*)*2, x_59);
return x_60;
}
else
{
uint8_t x_61; uint64_t x_62; lean_object* x_63; 
x_61 = 1;
x_62 = l_Lean_Expr_mkData(x_20, x_54, x_18, x_61, x_55, x_56, x_61);
lean_dec(x_54);
x_63 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_2);
lean_ctor_set_uint64(x_63, sizeof(void*)*2, x_62);
return x_63;
}
}
else
{
if (x_16 == 0)
{
uint8_t x_64; uint8_t x_65; uint64_t x_66; lean_object* x_67; 
x_64 = l_Lean_Expr_hasLevelParam(x_2);
x_65 = 1;
x_66 = l_Lean_Expr_mkData(x_20, x_54, x_18, x_65, x_55, x_65, x_64);
lean_dec(x_54);
x_67 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_2);
lean_ctor_set_uint64(x_67, sizeof(void*)*2, x_66);
return x_67;
}
else
{
uint8_t x_68; uint64_t x_69; lean_object* x_70; 
x_68 = 1;
x_69 = l_Lean_Expr_mkData(x_20, x_54, x_18, x_68, x_55, x_68, x_68);
lean_dec(x_54);
x_70 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_2);
lean_ctor_set_uint64(x_70, sizeof(void*)*2, x_69);
return x_70;
}
}
}
else
{
if (x_15 == 0)
{
uint8_t x_71; 
x_71 = l_Lean_Expr_hasLevelMVar(x_2);
if (x_16 == 0)
{
uint8_t x_72; uint8_t x_73; uint64_t x_74; lean_object* x_75; 
x_72 = l_Lean_Expr_hasLevelParam(x_2);
x_73 = 1;
x_74 = l_Lean_Expr_mkData(x_20, x_54, x_18, x_73, x_73, x_71, x_72);
lean_dec(x_54);
x_75 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_2);
lean_ctor_set_uint64(x_75, sizeof(void*)*2, x_74);
return x_75;
}
else
{
uint8_t x_76; uint64_t x_77; lean_object* x_78; 
x_76 = 1;
x_77 = l_Lean_Expr_mkData(x_20, x_54, x_18, x_76, x_76, x_71, x_76);
lean_dec(x_54);
x_78 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_2);
lean_ctor_set_uint64(x_78, sizeof(void*)*2, x_77);
return x_78;
}
}
else
{
if (x_16 == 0)
{
uint8_t x_79; uint8_t x_80; uint64_t x_81; lean_object* x_82; 
x_79 = l_Lean_Expr_hasLevelParam(x_2);
x_80 = 1;
x_81 = l_Lean_Expr_mkData(x_20, x_54, x_18, x_80, x_80, x_80, x_79);
lean_dec(x_54);
x_82 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_2);
lean_ctor_set_uint64(x_82, sizeof(void*)*2, x_81);
return x_82;
}
else
{
uint8_t x_83; uint64_t x_84; lean_object* x_85; 
x_83 = 1;
x_84 = l_Lean_Expr_mkData(x_20, x_54, x_18, x_83, x_83, x_83, x_83);
lean_dec(x_54);
x_85 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_2);
lean_ctor_set_uint64(x_85, sizeof(void*)*2, x_84);
return x_85;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; 
x_5 = l_Lean_Expr_approxDepth(x_3);
x_6 = l_Lean_Expr_approxDepth(x_4);
x_7 = x_6 < x_5;
x_8 = 1;
x_9 = l_Lean_Expr_hash(x_3);
x_10 = l_Lean_Expr_hash(x_4);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = l_Lean_Expr_looseBVarRange(x_3);
x_13 = l_Lean_Expr_looseBVarRange(x_4);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_nat_dec_lt(x_15, x_12);
x_17 = l_Lean_Expr_hasFVar(x_3);
x_18 = l_Lean_Expr_hasExprMVar(x_3);
x_19 = l_Lean_Expr_hasLevelMVar(x_3);
x_20 = l_Lean_Expr_hasLevelParam(x_3);
if (x_7 == 0)
{
x_21 = x_6;
goto block_91;
}
else
{
x_21 = x_5;
goto block_91;
}
block_91:
{
uint8_t x_22; uint64_t x_23; uint64_t x_24; lean_object* x_25; lean_object* x_58; 
x_22 = x_21 + x_8;
x_23 = ((uint64_t)x_22);
x_24 = lean_uint64_mix_hash(x_23, x_11);
if (x_16 == 0)
{
lean_dec(x_12);
if (x_17 == 0)
{
x_25 = x_15;
goto block_57;
}
else
{
x_58 = x_15;
goto block_90;
}
}
else
{
lean_dec(x_15);
if (x_17 == 0)
{
x_25 = x_12;
goto block_57;
}
else
{
x_58 = x_12;
goto block_90;
}
}
block_57:
{
uint8_t x_26; 
x_26 = l_Lean_Expr_hasFVar(x_4);
if (x_18 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Expr_hasExprMVar(x_4);
if (x_19 == 0)
{
uint8_t x_28; 
x_28 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_20 == 0)
{
uint8_t x_29; uint64_t x_30; lean_object* x_31; 
x_29 = l_Lean_Expr_hasLevelParam(x_4);
x_30 = l_Lean_Expr_mkDataForBinder(x_24, x_25, x_22, x_26, x_27, x_28, x_29, x_2);
lean_dec(x_25);
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
x_33 = l_Lean_Expr_mkDataForBinder(x_24, x_25, x_22, x_26, x_27, x_28, x_32, x_2);
lean_dec(x_25);
x_34 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_3);
lean_ctor_set(x_34, 2, x_4);
lean_ctor_set_uint64(x_34, sizeof(void*)*3, x_33);
return x_34;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_35; uint8_t x_36; uint64_t x_37; lean_object* x_38; 
x_35 = l_Lean_Expr_hasLevelParam(x_4);
x_36 = 1;
x_37 = l_Lean_Expr_mkDataForBinder(x_24, x_25, x_22, x_26, x_27, x_36, x_35, x_2);
lean_dec(x_25);
x_38 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set(x_38, 2, x_4);
lean_ctor_set_uint64(x_38, sizeof(void*)*3, x_37);
return x_38;
}
else
{
uint8_t x_39; uint64_t x_40; lean_object* x_41; 
x_39 = 1;
x_40 = l_Lean_Expr_mkDataForBinder(x_24, x_25, x_22, x_26, x_27, x_39, x_39, x_2);
lean_dec(x_25);
x_41 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_3);
lean_ctor_set(x_41, 2, x_4);
lean_ctor_set_uint64(x_41, sizeof(void*)*3, x_40);
return x_41;
}
}
}
else
{
if (x_19 == 0)
{
uint8_t x_42; 
x_42 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_20 == 0)
{
uint8_t x_43; uint8_t x_44; uint64_t x_45; lean_object* x_46; 
x_43 = l_Lean_Expr_hasLevelParam(x_4);
x_44 = 1;
x_45 = l_Lean_Expr_mkDataForBinder(x_24, x_25, x_22, x_26, x_44, x_42, x_43, x_2);
lean_dec(x_25);
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
x_48 = l_Lean_Expr_mkDataForBinder(x_24, x_25, x_22, x_26, x_47, x_42, x_47, x_2);
lean_dec(x_25);
x_49 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_3);
lean_ctor_set(x_49, 2, x_4);
lean_ctor_set_uint64(x_49, sizeof(void*)*3, x_48);
return x_49;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_50; uint8_t x_51; uint64_t x_52; lean_object* x_53; 
x_50 = l_Lean_Expr_hasLevelParam(x_4);
x_51 = 1;
x_52 = l_Lean_Expr_mkDataForBinder(x_24, x_25, x_22, x_26, x_51, x_51, x_50, x_2);
lean_dec(x_25);
x_53 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_3);
lean_ctor_set(x_53, 2, x_4);
lean_ctor_set_uint64(x_53, sizeof(void*)*3, x_52);
return x_53;
}
else
{
uint8_t x_54; uint64_t x_55; lean_object* x_56; 
x_54 = 1;
x_55 = l_Lean_Expr_mkDataForBinder(x_24, x_25, x_22, x_26, x_54, x_54, x_54, x_2);
lean_dec(x_25);
x_56 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_4);
lean_ctor_set_uint64(x_56, sizeof(void*)*3, x_55);
return x_56;
}
}
}
}
block_90:
{
if (x_18 == 0)
{
uint8_t x_59; 
x_59 = l_Lean_Expr_hasExprMVar(x_4);
if (x_19 == 0)
{
uint8_t x_60; 
x_60 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_20 == 0)
{
uint8_t x_61; uint8_t x_62; uint64_t x_63; lean_object* x_64; 
x_61 = l_Lean_Expr_hasLevelParam(x_4);
x_62 = 1;
x_63 = l_Lean_Expr_mkDataForBinder(x_24, x_58, x_22, x_62, x_59, x_60, x_61, x_2);
lean_dec(x_58);
x_64 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_3);
lean_ctor_set(x_64, 2, x_4);
lean_ctor_set_uint64(x_64, sizeof(void*)*3, x_63);
return x_64;
}
else
{
uint8_t x_65; uint64_t x_66; lean_object* x_67; 
x_65 = 1;
x_66 = l_Lean_Expr_mkDataForBinder(x_24, x_58, x_22, x_65, x_59, x_60, x_65, x_2);
lean_dec(x_58);
x_67 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_3);
lean_ctor_set(x_67, 2, x_4);
lean_ctor_set_uint64(x_67, sizeof(void*)*3, x_66);
return x_67;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_68; uint8_t x_69; uint64_t x_70; lean_object* x_71; 
x_68 = l_Lean_Expr_hasLevelParam(x_4);
x_69 = 1;
x_70 = l_Lean_Expr_mkDataForBinder(x_24, x_58, x_22, x_69, x_59, x_69, x_68, x_2);
lean_dec(x_58);
x_71 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_3);
lean_ctor_set(x_71, 2, x_4);
lean_ctor_set_uint64(x_71, sizeof(void*)*3, x_70);
return x_71;
}
else
{
uint8_t x_72; uint64_t x_73; lean_object* x_74; 
x_72 = 1;
x_73 = l_Lean_Expr_mkDataForBinder(x_24, x_58, x_22, x_72, x_59, x_72, x_72, x_2);
lean_dec(x_58);
x_74 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_3);
lean_ctor_set(x_74, 2, x_4);
lean_ctor_set_uint64(x_74, sizeof(void*)*3, x_73);
return x_74;
}
}
}
else
{
if (x_19 == 0)
{
uint8_t x_75; 
x_75 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_20 == 0)
{
uint8_t x_76; uint8_t x_77; uint64_t x_78; lean_object* x_79; 
x_76 = l_Lean_Expr_hasLevelParam(x_4);
x_77 = 1;
x_78 = l_Lean_Expr_mkDataForBinder(x_24, x_58, x_22, x_77, x_77, x_75, x_76, x_2);
lean_dec(x_58);
x_79 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_3);
lean_ctor_set(x_79, 2, x_4);
lean_ctor_set_uint64(x_79, sizeof(void*)*3, x_78);
return x_79;
}
else
{
uint8_t x_80; uint64_t x_81; lean_object* x_82; 
x_80 = 1;
x_81 = l_Lean_Expr_mkDataForBinder(x_24, x_58, x_22, x_80, x_80, x_75, x_80, x_2);
lean_dec(x_58);
x_82 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_3);
lean_ctor_set(x_82, 2, x_4);
lean_ctor_set_uint64(x_82, sizeof(void*)*3, x_81);
return x_82;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_83; uint8_t x_84; uint64_t x_85; lean_object* x_86; 
x_83 = l_Lean_Expr_hasLevelParam(x_4);
x_84 = 1;
x_85 = l_Lean_Expr_mkDataForBinder(x_24, x_58, x_22, x_84, x_84, x_84, x_83, x_2);
lean_dec(x_58);
x_86 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_3);
lean_ctor_set(x_86, 2, x_4);
lean_ctor_set_uint64(x_86, sizeof(void*)*3, x_85);
return x_86;
}
else
{
uint8_t x_87; uint64_t x_88; lean_object* x_89; 
x_87 = 1;
x_88 = l_Lean_Expr_mkDataForBinder(x_24, x_58, x_22, x_87, x_87, x_87, x_87, x_2);
lean_dec(x_58);
x_89 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_3);
lean_ctor_set(x_89, 2, x_4);
lean_ctor_set_uint64(x_89, sizeof(void*)*3, x_88);
return x_89;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_mkLambda(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; 
x_5 = l_Lean_Expr_approxDepth(x_3);
x_6 = l_Lean_Expr_approxDepth(x_4);
x_7 = x_6 < x_5;
x_8 = 1;
x_9 = l_Lean_Expr_hash(x_3);
x_10 = l_Lean_Expr_hash(x_4);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = l_Lean_Expr_looseBVarRange(x_3);
x_13 = l_Lean_Expr_looseBVarRange(x_4);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_nat_dec_lt(x_15, x_12);
x_17 = l_Lean_Expr_hasFVar(x_3);
x_18 = l_Lean_Expr_hasExprMVar(x_3);
x_19 = l_Lean_Expr_hasLevelMVar(x_3);
x_20 = l_Lean_Expr_hasLevelParam(x_3);
if (x_7 == 0)
{
x_21 = x_6;
goto block_91;
}
else
{
x_21 = x_5;
goto block_91;
}
block_91:
{
uint8_t x_22; uint64_t x_23; uint64_t x_24; lean_object* x_25; lean_object* x_58; 
x_22 = x_21 + x_8;
x_23 = ((uint64_t)x_22);
x_24 = lean_uint64_mix_hash(x_23, x_11);
if (x_16 == 0)
{
lean_dec(x_12);
if (x_17 == 0)
{
x_25 = x_15;
goto block_57;
}
else
{
x_58 = x_15;
goto block_90;
}
}
else
{
lean_dec(x_15);
if (x_17 == 0)
{
x_25 = x_12;
goto block_57;
}
else
{
x_58 = x_12;
goto block_90;
}
}
block_57:
{
uint8_t x_26; 
x_26 = l_Lean_Expr_hasFVar(x_4);
if (x_18 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Expr_hasExprMVar(x_4);
if (x_19 == 0)
{
uint8_t x_28; 
x_28 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_20 == 0)
{
uint8_t x_29; uint64_t x_30; lean_object* x_31; 
x_29 = l_Lean_Expr_hasLevelParam(x_4);
x_30 = l_Lean_Expr_mkDataForBinder(x_24, x_25, x_22, x_26, x_27, x_28, x_29, x_2);
lean_dec(x_25);
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
x_33 = l_Lean_Expr_mkDataForBinder(x_24, x_25, x_22, x_26, x_27, x_28, x_32, x_2);
lean_dec(x_25);
x_34 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_3);
lean_ctor_set(x_34, 2, x_4);
lean_ctor_set_uint64(x_34, sizeof(void*)*3, x_33);
return x_34;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_35; uint8_t x_36; uint64_t x_37; lean_object* x_38; 
x_35 = l_Lean_Expr_hasLevelParam(x_4);
x_36 = 1;
x_37 = l_Lean_Expr_mkDataForBinder(x_24, x_25, x_22, x_26, x_27, x_36, x_35, x_2);
lean_dec(x_25);
x_38 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set(x_38, 2, x_4);
lean_ctor_set_uint64(x_38, sizeof(void*)*3, x_37);
return x_38;
}
else
{
uint8_t x_39; uint64_t x_40; lean_object* x_41; 
x_39 = 1;
x_40 = l_Lean_Expr_mkDataForBinder(x_24, x_25, x_22, x_26, x_27, x_39, x_39, x_2);
lean_dec(x_25);
x_41 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_3);
lean_ctor_set(x_41, 2, x_4);
lean_ctor_set_uint64(x_41, sizeof(void*)*3, x_40);
return x_41;
}
}
}
else
{
if (x_19 == 0)
{
uint8_t x_42; 
x_42 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_20 == 0)
{
uint8_t x_43; uint8_t x_44; uint64_t x_45; lean_object* x_46; 
x_43 = l_Lean_Expr_hasLevelParam(x_4);
x_44 = 1;
x_45 = l_Lean_Expr_mkDataForBinder(x_24, x_25, x_22, x_26, x_44, x_42, x_43, x_2);
lean_dec(x_25);
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
x_48 = l_Lean_Expr_mkDataForBinder(x_24, x_25, x_22, x_26, x_47, x_42, x_47, x_2);
lean_dec(x_25);
x_49 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_3);
lean_ctor_set(x_49, 2, x_4);
lean_ctor_set_uint64(x_49, sizeof(void*)*3, x_48);
return x_49;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_50; uint8_t x_51; uint64_t x_52; lean_object* x_53; 
x_50 = l_Lean_Expr_hasLevelParam(x_4);
x_51 = 1;
x_52 = l_Lean_Expr_mkDataForBinder(x_24, x_25, x_22, x_26, x_51, x_51, x_50, x_2);
lean_dec(x_25);
x_53 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_3);
lean_ctor_set(x_53, 2, x_4);
lean_ctor_set_uint64(x_53, sizeof(void*)*3, x_52);
return x_53;
}
else
{
uint8_t x_54; uint64_t x_55; lean_object* x_56; 
x_54 = 1;
x_55 = l_Lean_Expr_mkDataForBinder(x_24, x_25, x_22, x_26, x_54, x_54, x_54, x_2);
lean_dec(x_25);
x_56 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_4);
lean_ctor_set_uint64(x_56, sizeof(void*)*3, x_55);
return x_56;
}
}
}
}
block_90:
{
if (x_18 == 0)
{
uint8_t x_59; 
x_59 = l_Lean_Expr_hasExprMVar(x_4);
if (x_19 == 0)
{
uint8_t x_60; 
x_60 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_20 == 0)
{
uint8_t x_61; uint8_t x_62; uint64_t x_63; lean_object* x_64; 
x_61 = l_Lean_Expr_hasLevelParam(x_4);
x_62 = 1;
x_63 = l_Lean_Expr_mkDataForBinder(x_24, x_58, x_22, x_62, x_59, x_60, x_61, x_2);
lean_dec(x_58);
x_64 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_3);
lean_ctor_set(x_64, 2, x_4);
lean_ctor_set_uint64(x_64, sizeof(void*)*3, x_63);
return x_64;
}
else
{
uint8_t x_65; uint64_t x_66; lean_object* x_67; 
x_65 = 1;
x_66 = l_Lean_Expr_mkDataForBinder(x_24, x_58, x_22, x_65, x_59, x_60, x_65, x_2);
lean_dec(x_58);
x_67 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_3);
lean_ctor_set(x_67, 2, x_4);
lean_ctor_set_uint64(x_67, sizeof(void*)*3, x_66);
return x_67;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_68; uint8_t x_69; uint64_t x_70; lean_object* x_71; 
x_68 = l_Lean_Expr_hasLevelParam(x_4);
x_69 = 1;
x_70 = l_Lean_Expr_mkDataForBinder(x_24, x_58, x_22, x_69, x_59, x_69, x_68, x_2);
lean_dec(x_58);
x_71 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_3);
lean_ctor_set(x_71, 2, x_4);
lean_ctor_set_uint64(x_71, sizeof(void*)*3, x_70);
return x_71;
}
else
{
uint8_t x_72; uint64_t x_73; lean_object* x_74; 
x_72 = 1;
x_73 = l_Lean_Expr_mkDataForBinder(x_24, x_58, x_22, x_72, x_59, x_72, x_72, x_2);
lean_dec(x_58);
x_74 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_3);
lean_ctor_set(x_74, 2, x_4);
lean_ctor_set_uint64(x_74, sizeof(void*)*3, x_73);
return x_74;
}
}
}
else
{
if (x_19 == 0)
{
uint8_t x_75; 
x_75 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_20 == 0)
{
uint8_t x_76; uint8_t x_77; uint64_t x_78; lean_object* x_79; 
x_76 = l_Lean_Expr_hasLevelParam(x_4);
x_77 = 1;
x_78 = l_Lean_Expr_mkDataForBinder(x_24, x_58, x_22, x_77, x_77, x_75, x_76, x_2);
lean_dec(x_58);
x_79 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_3);
lean_ctor_set(x_79, 2, x_4);
lean_ctor_set_uint64(x_79, sizeof(void*)*3, x_78);
return x_79;
}
else
{
uint8_t x_80; uint64_t x_81; lean_object* x_82; 
x_80 = 1;
x_81 = l_Lean_Expr_mkDataForBinder(x_24, x_58, x_22, x_80, x_80, x_75, x_80, x_2);
lean_dec(x_58);
x_82 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_3);
lean_ctor_set(x_82, 2, x_4);
lean_ctor_set_uint64(x_82, sizeof(void*)*3, x_81);
return x_82;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_83; uint8_t x_84; uint64_t x_85; lean_object* x_86; 
x_83 = l_Lean_Expr_hasLevelParam(x_4);
x_84 = 1;
x_85 = l_Lean_Expr_mkDataForBinder(x_24, x_58, x_22, x_84, x_84, x_84, x_83, x_2);
lean_dec(x_58);
x_86 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_3);
lean_ctor_set(x_86, 2, x_4);
lean_ctor_set_uint64(x_86, sizeof(void*)*3, x_85);
return x_86;
}
else
{
uint8_t x_87; uint64_t x_88; lean_object* x_89; 
x_87 = 1;
x_88 = l_Lean_Expr_mkDataForBinder(x_24, x_58, x_22, x_87, x_87, x_87, x_87, x_2);
lean_dec(x_58);
x_89 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_3);
lean_ctor_set(x_89, 2, x_4);
lean_ctor_set_uint64(x_89, sizeof(void*)*3, x_88);
return x_89;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_1; 
x_1 = lean_mk_string("Unit");
return x_1;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkSimpleThunkType___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkSimpleThunkType___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = 0;
x_4 = l_Lean_mkSimpleThunkType___closed__3;
x_5 = l_Lean_mkForall(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_mkSimpleThunk___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_");
return x_1;
}
}
static lean_object* _init_l_Lean_mkSimpleThunk___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkSimpleThunk___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_mkSimpleThunk___closed__2;
x_3 = 0;
x_4 = l_Lean_mkSimpleThunkType___closed__3;
x_5 = l_Lean_mkLambda(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; 
x_6 = l_Lean_Expr_approxDepth(x_2);
x_7 = l_Lean_Expr_approxDepth(x_3);
x_8 = x_7 < x_6;
x_9 = l_Lean_Expr_approxDepth(x_4);
x_10 = 1;
x_11 = l_Lean_Expr_hash(x_2);
x_12 = l_Lean_Expr_hash(x_3);
x_13 = l_Lean_Expr_hash(x_4);
x_14 = lean_uint64_mix_hash(x_12, x_13);
x_15 = lean_uint64_mix_hash(x_11, x_14);
x_16 = l_Lean_Expr_looseBVarRange(x_2);
x_17 = l_Lean_Expr_looseBVarRange(x_3);
x_18 = lean_nat_dec_lt(x_17, x_16);
x_19 = l_Lean_Expr_looseBVarRange(x_4);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_19, x_20);
lean_dec(x_19);
x_22 = l_Lean_Expr_hasFVar(x_2);
x_23 = l_Lean_Expr_hasExprMVar(x_2);
x_24 = l_Lean_Expr_hasLevelMVar(x_2);
x_25 = l_Lean_Expr_hasLevelParam(x_2);
if (x_8 == 0)
{
uint8_t x_103; 
x_103 = x_9 < x_7;
if (x_103 == 0)
{
x_26 = x_9;
goto block_102;
}
else
{
x_26 = x_7;
goto block_102;
}
}
else
{
uint8_t x_104; 
x_104 = x_9 < x_6;
if (x_104 == 0)
{
x_26 = x_9;
goto block_102;
}
else
{
x_26 = x_6;
goto block_102;
}
}
block_102:
{
uint8_t x_27; uint64_t x_28; uint64_t x_29; lean_object* x_30; 
x_27 = x_26 + x_10;
x_28 = ((uint64_t)x_27);
x_29 = lean_uint64_mix_hash(x_28, x_15);
if (x_18 == 0)
{
uint8_t x_100; 
lean_dec(x_16);
x_100 = lean_nat_dec_lt(x_21, x_17);
if (x_100 == 0)
{
lean_dec(x_17);
x_30 = x_21;
goto block_99;
}
else
{
lean_dec(x_21);
x_30 = x_17;
goto block_99;
}
}
else
{
uint8_t x_101; 
lean_dec(x_17);
x_101 = lean_nat_dec_lt(x_21, x_16);
if (x_101 == 0)
{
lean_dec(x_16);
x_30 = x_21;
goto block_99;
}
else
{
lean_dec(x_21);
x_30 = x_16;
goto block_99;
}
}
block_99:
{
uint8_t x_31; 
if (x_22 == 0)
{
uint8_t x_95; 
x_95 = l_Lean_Expr_hasFVar(x_3);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = l_Lean_Expr_hasFVar(x_4);
x_31 = x_96;
goto block_94;
}
else
{
uint8_t x_97; 
x_97 = 1;
x_31 = x_97;
goto block_94;
}
}
else
{
uint8_t x_98; 
x_98 = 1;
x_31 = x_98;
goto block_94;
}
block_94:
{
uint8_t x_32; 
if (x_23 == 0)
{
uint8_t x_57; 
x_57 = l_Lean_Expr_hasExprMVar(x_3);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = l_Lean_Expr_hasExprMVar(x_4);
if (x_24 == 0)
{
x_32 = x_58;
goto block_56;
}
else
{
if (x_25 == 0)
{
uint8_t x_59; 
x_59 = l_Lean_Expr_hasLevelParam(x_3);
if (x_59 == 0)
{
uint8_t x_60; uint8_t x_61; uint64_t x_62; lean_object* x_63; 
x_60 = l_Lean_Expr_hasLevelParam(x_4);
x_61 = 1;
x_62 = l_Lean_Expr_mkDataForLet(x_29, x_30, x_27, x_31, x_58, x_61, x_60, x_5);
lean_dec(x_30);
x_63 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_2);
lean_ctor_set(x_63, 2, x_3);
lean_ctor_set(x_63, 3, x_4);
lean_ctor_set_uint64(x_63, sizeof(void*)*4, x_62);
return x_63;
}
else
{
uint8_t x_64; uint64_t x_65; lean_object* x_66; 
x_64 = 1;
x_65 = l_Lean_Expr_mkDataForLet(x_29, x_30, x_27, x_31, x_58, x_64, x_64, x_5);
lean_dec(x_30);
x_66 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_2);
lean_ctor_set(x_66, 2, x_3);
lean_ctor_set(x_66, 3, x_4);
lean_ctor_set_uint64(x_66, sizeof(void*)*4, x_65);
return x_66;
}
}
else
{
uint8_t x_67; uint64_t x_68; lean_object* x_69; 
x_67 = 1;
x_68 = l_Lean_Expr_mkDataForLet(x_29, x_30, x_27, x_31, x_58, x_67, x_67, x_5);
lean_dec(x_30);
x_69 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_2);
lean_ctor_set(x_69, 2, x_3);
lean_ctor_set(x_69, 3, x_4);
lean_ctor_set_uint64(x_69, sizeof(void*)*4, x_68);
return x_69;
}
}
}
else
{
if (x_24 == 0)
{
uint8_t x_70; 
x_70 = 1;
x_32 = x_70;
goto block_56;
}
else
{
if (x_25 == 0)
{
uint8_t x_71; 
x_71 = l_Lean_Expr_hasLevelParam(x_3);
if (x_71 == 0)
{
uint8_t x_72; uint8_t x_73; uint64_t x_74; lean_object* x_75; 
x_72 = l_Lean_Expr_hasLevelParam(x_4);
x_73 = 1;
x_74 = l_Lean_Expr_mkDataForLet(x_29, x_30, x_27, x_31, x_73, x_73, x_72, x_5);
lean_dec(x_30);
x_75 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_2);
lean_ctor_set(x_75, 2, x_3);
lean_ctor_set(x_75, 3, x_4);
lean_ctor_set_uint64(x_75, sizeof(void*)*4, x_74);
return x_75;
}
else
{
uint8_t x_76; uint64_t x_77; lean_object* x_78; 
x_76 = 1;
x_77 = l_Lean_Expr_mkDataForLet(x_29, x_30, x_27, x_31, x_76, x_76, x_76, x_5);
lean_dec(x_30);
x_78 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_2);
lean_ctor_set(x_78, 2, x_3);
lean_ctor_set(x_78, 3, x_4);
lean_ctor_set_uint64(x_78, sizeof(void*)*4, x_77);
return x_78;
}
}
else
{
uint8_t x_79; uint64_t x_80; lean_object* x_81; 
x_79 = 1;
x_80 = l_Lean_Expr_mkDataForLet(x_29, x_30, x_27, x_31, x_79, x_79, x_79, x_5);
lean_dec(x_30);
x_81 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_2);
lean_ctor_set(x_81, 2, x_3);
lean_ctor_set(x_81, 3, x_4);
lean_ctor_set_uint64(x_81, sizeof(void*)*4, x_80);
return x_81;
}
}
}
}
else
{
if (x_24 == 0)
{
uint8_t x_82; 
x_82 = 1;
x_32 = x_82;
goto block_56;
}
else
{
if (x_25 == 0)
{
uint8_t x_83; 
x_83 = l_Lean_Expr_hasLevelParam(x_3);
if (x_83 == 0)
{
uint8_t x_84; uint8_t x_85; uint64_t x_86; lean_object* x_87; 
x_84 = l_Lean_Expr_hasLevelParam(x_4);
x_85 = 1;
x_86 = l_Lean_Expr_mkDataForLet(x_29, x_30, x_27, x_31, x_85, x_85, x_84, x_5);
lean_dec(x_30);
x_87 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_2);
lean_ctor_set(x_87, 2, x_3);
lean_ctor_set(x_87, 3, x_4);
lean_ctor_set_uint64(x_87, sizeof(void*)*4, x_86);
return x_87;
}
else
{
uint8_t x_88; uint64_t x_89; lean_object* x_90; 
x_88 = 1;
x_89 = l_Lean_Expr_mkDataForLet(x_29, x_30, x_27, x_31, x_88, x_88, x_88, x_5);
lean_dec(x_30);
x_90 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_2);
lean_ctor_set(x_90, 2, x_3);
lean_ctor_set(x_90, 3, x_4);
lean_ctor_set_uint64(x_90, sizeof(void*)*4, x_89);
return x_90;
}
}
else
{
uint8_t x_91; uint64_t x_92; lean_object* x_93; 
x_91 = 1;
x_92 = l_Lean_Expr_mkDataForLet(x_29, x_30, x_27, x_31, x_91, x_91, x_91, x_5);
lean_dec(x_30);
x_93 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_2);
lean_ctor_set(x_93, 2, x_3);
lean_ctor_set(x_93, 3, x_4);
lean_ctor_set_uint64(x_93, sizeof(void*)*4, x_92);
return x_93;
}
}
}
block_56:
{
uint8_t x_33; 
x_33 = l_Lean_Expr_hasLevelMVar(x_3);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_25 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Expr_hasLevelParam(x_3);
if (x_35 == 0)
{
uint8_t x_36; uint64_t x_37; lean_object* x_38; 
x_36 = l_Lean_Expr_hasLevelParam(x_4);
x_37 = l_Lean_Expr_mkDataForLet(x_29, x_30, x_27, x_31, x_32, x_34, x_36, x_5);
lean_dec(x_30);
x_38 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_2);
lean_ctor_set(x_38, 2, x_3);
lean_ctor_set(x_38, 3, x_4);
lean_ctor_set_uint64(x_38, sizeof(void*)*4, x_37);
return x_38;
}
else
{
uint8_t x_39; uint64_t x_40; lean_object* x_41; 
x_39 = 1;
x_40 = l_Lean_Expr_mkDataForLet(x_29, x_30, x_27, x_31, x_32, x_34, x_39, x_5);
lean_dec(x_30);
x_41 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_2);
lean_ctor_set(x_41, 2, x_3);
lean_ctor_set(x_41, 3, x_4);
lean_ctor_set_uint64(x_41, sizeof(void*)*4, x_40);
return x_41;
}
}
else
{
uint8_t x_42; uint64_t x_43; lean_object* x_44; 
x_42 = 1;
x_43 = l_Lean_Expr_mkDataForLet(x_29, x_30, x_27, x_31, x_32, x_34, x_42, x_5);
lean_dec(x_30);
x_44 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_2);
lean_ctor_set(x_44, 2, x_3);
lean_ctor_set(x_44, 3, x_4);
lean_ctor_set_uint64(x_44, sizeof(void*)*4, x_43);
return x_44;
}
}
else
{
if (x_25 == 0)
{
uint8_t x_45; 
x_45 = l_Lean_Expr_hasLevelParam(x_3);
if (x_45 == 0)
{
uint8_t x_46; uint8_t x_47; uint64_t x_48; lean_object* x_49; 
x_46 = l_Lean_Expr_hasLevelParam(x_4);
x_47 = 1;
x_48 = l_Lean_Expr_mkDataForLet(x_29, x_30, x_27, x_31, x_32, x_47, x_46, x_5);
lean_dec(x_30);
x_49 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_2);
lean_ctor_set(x_49, 2, x_3);
lean_ctor_set(x_49, 3, x_4);
lean_ctor_set_uint64(x_49, sizeof(void*)*4, x_48);
return x_49;
}
else
{
uint8_t x_50; uint64_t x_51; lean_object* x_52; 
x_50 = 1;
x_51 = l_Lean_Expr_mkDataForLet(x_29, x_30, x_27, x_31, x_32, x_50, x_50, x_5);
lean_dec(x_30);
x_52 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set(x_52, 1, x_2);
lean_ctor_set(x_52, 2, x_3);
lean_ctor_set(x_52, 3, x_4);
lean_ctor_set_uint64(x_52, sizeof(void*)*4, x_51);
return x_52;
}
}
else
{
uint8_t x_53; uint64_t x_54; lean_object* x_55; 
x_53 = 1;
x_54 = l_Lean_Expr_mkDataForLet(x_29, x_30, x_27, x_31, x_32, x_53, x_53, x_5);
lean_dec(x_30);
x_55 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_2);
lean_ctor_set(x_55, 2, x_3);
lean_ctor_set(x_55, 3, x_4);
lean_ctor_set_uint64(x_55, sizeof(void*)*4, x_54);
return x_55;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_mkLet(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_mkApp(x_1, x_2);
x_5 = l_Lean_mkApp(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkAppB(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_mkAppB(x_1, x_2, x_3);
x_6 = l_Lean_mkApp(x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_mkAppB(x_1, x_2, x_3);
x_7 = l_Lean_mkAppB(x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_mkApp4(x_1, x_2, x_3, x_4, x_5);
x_8 = l_Lean_mkApp(x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_mkApp4(x_1, x_2, x_3, x_4, x_5);
x_9 = l_Lean_mkAppB(x_8, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_mkApp4(x_1, x_2, x_3, x_4, x_5);
x_10 = l_Lean_mkApp3(x_9, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_mkApp4(x_1, x_2, x_3, x_4, x_5);
x_11 = l_Lean_mkApp4(x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_mkApp4(x_1, x_2, x_3, x_4, x_5);
x_12 = l_Lean_mkApp5(x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_mkApp4(x_1, x_2, x_3, x_4, x_5);
x_13 = l_Lean_mkApp6(x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; uint64_t x_8; lean_object* x_9; 
x_2 = 3;
x_3 = l_Lean_Literal_hash(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
x_5 = 0;
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = l_Lean_Expr_mkData(x_4, x_6, x_5, x_7, x_7, x_7, x_7);
x_9 = lean_alloc_ctor(9, 1, 8);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set_uint64(x_9, sizeof(void*)*1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = l_Lean_mkLit(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkNatLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("OfNat");
return x_1;
}
}
static lean_object* _init_l_Lean_mkNatLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkNatLit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkNatLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ofNat");
return x_1;
}
}
static lean_object* _init_l_Lean_mkNatLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkNatLit___closed__2;
x_2 = l_Lean_mkNatLit___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkNatLit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelZero;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_mkNatLit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkNatLit___closed__4;
x_2 = l_Lean_mkNatLit___closed__5;
x_3 = l_Lean_mkConst(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkNatLit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Literal_type___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_mkNatLit___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("instOfNatNat");
return x_1;
}
}
static lean_object* _init_l_Lean_mkNatLit___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkNatLit___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkNatLit___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkNatLit___closed__9;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_mkRawNatLit(x_1);
x_3 = l_Lean_mkNatLit___closed__10;
lean_inc(x_2);
x_4 = l_Lean_mkApp(x_3, x_2);
x_5 = l_Lean_mkNatLit___closed__6;
x_6 = l_Lean_mkNatLit___closed__7;
x_7 = l_Lean_mkApp3(x_5, x_6, x_2, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = l_Lean_mkLit(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkBVar(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkFVar(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mvar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkMVar(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkConst(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkApp(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkLambda(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = lean_expr_mk_lambda(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkForall(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = lean_expr_mk_forall(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = l_Lean_mkLet(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkLit(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkMData(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkProj(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkAppN___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_mkAppN___spec__1(x_2, x_7, x_8, x_1);
lean_dec(x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkAppN___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_3, x_4, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkAppRange(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_mkAppRev___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_7 = 0;
x_8 = l_Array_foldrMUnsafe_fold___at_Lean_mkAppRev___spec__1(x_2, x_6, x_7, x_1);
lean_dec(x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_mkAppRev___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isSort(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isProp(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isBVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isMVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isFVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isApp(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isProj(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isConst(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isForall(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isLambda(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isBinding___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isBinding(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isLet(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isMData(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isLit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
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
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getForallBody(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgsAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppNumArgsAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Expr_getAppNumArgsAux(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAppNumArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_withApp___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_withAppRev___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_getRevArgD(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
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
lean_object* x_1; 
x_1 = lean_mk_string("invalid index");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_getRevArg_x21___closed__1;
x_3 = lean_unsigned_to_nat(545u);
x_4 = lean_unsigned_to_nat(22u);
x_5 = l_Lean_Expr_getRevArg_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object* x_1, lean_object* x_2) {
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
x_11 = l_Lean_Expr_getRevArg_x21___closed__3;
x_12 = lean_panic_fn(x_10, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getRevArg_x21(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_appFn_x21___closed__1;
x_3 = lean_unsigned_to_nat(565u);
x_4 = lean_unsigned_to_nat(17u);
x_5 = l_Lean_Expr_appFn_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_appFn_x21(x_1);
lean_dec(x_1);
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_appArg_x21___closed__1;
x_3 = lean_unsigned_to_nat(569u);
x_4 = lean_unsigned_to_nat(17u);
x_5 = l_Lean_Expr_appFn_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isNatLit(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isNatLit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isNatLit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_natLit_x3f(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_natLit_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_natLit_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object* x_1) {
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_isCharLit___closed__2;
x_2 = l_Lean_mkNatLit___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_isCharLit___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isCharLit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_constName_x21___closed__1;
x_3 = lean_unsigned_to_nat(588u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_Expr_constName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_constName_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_constName_x3f(x_1);
lean_dec(x_1);
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_constLevels_x21___closed__1;
x_3 = lean_unsigned_to_nat(596u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Expr_constName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_constLevels_x21(x_1);
lean_dec(x_1);
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_bvarIdx_x21___closed__1;
x_3 = lean_unsigned_to_nat(600u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Expr_bvarIdx_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_bvarIdx_x21(x_1);
lean_dec(x_1);
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_fvarId_x21___closed__1;
x_3 = lean_unsigned_to_nat(604u);
x_4 = lean_unsigned_to_nat(16u);
x_5 = l_Lean_Expr_fvarId_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object* x_1) {
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
x_3 = l_Lean_instInhabitedFVarId;
x_4 = l_Lean_Expr_fvarId_x21___closed__3;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_fvarId_x21(x_1);
lean_dec(x_1);
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_mvarId_x21___closed__1;
x_3 = lean_unsigned_to_nat(608u);
x_4 = lean_unsigned_to_nat(16u);
x_5 = l_Lean_Expr_mvarId_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object* x_1) {
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
x_3 = l_Lean_instInhabitedMVarId;
x_4 = l_Lean_Expr_mvarId_x21___closed__3;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_mvarId_x21(x_1);
lean_dec(x_1);
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_bindingName_x21___closed__1;
x_3 = lean_unsigned_to_nat(613u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Expr_bindingName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_bindingName_x21(x_1);
lean_dec(x_1);
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_bindingDomain_x21___closed__1;
x_3 = lean_unsigned_to_nat(618u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Expr_bindingName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_bindingDomain_x21(x_1);
lean_dec(x_1);
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_bindingBody_x21___closed__1;
x_3 = lean_unsigned_to_nat(623u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Expr_bindingName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_bindingBody_x21(x_1);
lean_dec(x_1);
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_bindingInfo_x21___closed__1;
x_3 = lean_unsigned_to_nat(628u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Expr_bindingName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_bindingInfo_x21(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_bindingInfo_x21(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_letName_x21___closed__1;
x_3 = lean_unsigned_to_nat(632u);
x_4 = lean_unsigned_to_nat(22u);
x_5 = l_Lean_Expr_letName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_letName_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_consumeMData(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.mdataExpr!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mdata expression expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_mdataExpr_x21___closed__1;
x_3 = lean_unsigned_to_nat(640u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_Expr_mdataExpr_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 10)
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
x_4 = l_Lean_Expr_mdataExpr_x21___closed__3;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_mdataExpr_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasLooseBVars(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_Lean_Expr_hasLooseBVars(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isArrow(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_instantiate(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_instantiate1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_abstract(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lean_Expr_replaceFVar___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Expr_replaceFVar___closed__1;
x_5 = lean_array_push(x_4, x_2);
x_6 = lean_expr_abstract(x_1, x_5);
lean_dec(x_5);
x_7 = lean_expr_instantiate1(x_6, x_3);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_replaceFVar(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_mkFVar(x_2);
x_5 = l_Lean_Expr_replaceFVar(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_replaceFVarId(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_expr_abstract(x_1, x_2);
x_5 = lean_expr_instantiate_rev(x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isAtomic(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object* x_1, lean_object* x_2) {
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
x_1 = l_Lean_instInhabitedExpr___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instCoeExprExprStructEq(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_expr_equal(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = l_Lean_Expr_hash(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_ExprStructEq_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
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
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instToStringExprStructEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_dbg_to_string(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instToStringExprStructEq___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ExprStructEq_instToStringExprStructEq(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(x_4, x_2, x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_mkAppRevRange(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRevAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRevAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_betaRev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isHeadBetaTargetFn(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object* x_1) {
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
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_getAppFn(x_1);
x_3 = l_Lean_Expr_isHeadBetaTargetFn(x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isHeadBetaTarget(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAutoParamTactic_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_getOptParamDefault_x3f___closed__2;
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isOptParam(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_getAutoParamTactic_x3f___closed__2;
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isAutoParam(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_consumeAutoOptParam(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_isOptParam(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isAutoParam(x_1);
if (x_3 == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_appFn_x21(x_1);
lean_dec(x_1);
x_5 = l_Lean_Expr_appArg_x21(x_4);
lean_dec(x_4);
x_1 = x_5;
goto _start;
}
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Expr_appFn_x21(x_1);
lean_dec(x_1);
x_8 = l_Lean_Expr_appArg_x21(x_7);
lean_dec(x_7);
x_1 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_hasAnyFVar_visit(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_updateApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_expr_update_app(x_1, x_2, x_3);
return x_5;
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_updateApp_x21___closed__1;
x_3 = lean_unsigned_to_nat(914u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Expr_appFn_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateApp_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_updateConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_update_const(x_1, x_2);
return x_4;
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_updateConst_x21___closed__1;
x_3 = lean_unsigned_to_nat(923u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Expr_constName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateConst_x21(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_updateSort___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_update_sort(x_1, x_2);
return x_4;
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_updateSort_x21___closed__1;
x_3 = lean_unsigned_to_nat(932u);
x_4 = lean_unsigned_to_nat(16u);
x_5 = l_Lean_Expr_updateSort_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateSort_x21(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_updateProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_update_proj(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_update_mdata(x_1, x_2);
return x_4;
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_updateMData_x21___closed__1;
x_3 = lean_unsigned_to_nat(949u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_Expr_updateMData_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateMData_x21(lean_object* x_1, lean_object* x_2) {
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_updateProj_x21___closed__1;
x_3 = lean_unsigned_to_nat(954u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Expr_updateProj_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateProj_x21(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_updateForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_expr_update_forall(x_1, x_6, x_3, x_4);
return x_7;
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_updateForall_x21___closed__1;
x_3 = lean_unsigned_to_nat(963u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Expr_updateForall_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForall_x21(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_updateForall_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_updateForall_x21(x_1, x_5, x_3, x_4);
return x_6;
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_updateForallE_x21___closed__1;
x_3 = lean_unsigned_to_nat(968u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Expr_updateForall_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_expr_update_lambda(x_1, x_6, x_3, x_4);
return x_7;
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_updateLambda_x21___closed__1;
x_3 = lean_unsigned_to_nat(977u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_Expr_updateLambda_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambda_x21(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambda_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_updateLambda_x21(x_1, x_5, x_3, x_4);
return x_6;
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_updateLambdaE_x21___closed__1;
x_3 = lean_unsigned_to_nat(982u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_Expr_updateLambda_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_updateLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_expr_update_let(x_1, x_2, x_3, x_4);
return x_6;
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
x_1 = l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__2;
x_2 = l_Lean_Expr_updateLet_x21___closed__1;
x_3 = lean_unsigned_to_nat(991u);
x_4 = lean_unsigned_to_nat(22u);
x_5 = l_Lean_Expr_letName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLet_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_updateFn(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_5);
x_7 = l_Lean_Expr_eta(x_5);
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; 
lean_dec(x_9);
lean_inc(x_4);
x_13 = (uint8_t)((x_6 << 24) >> 61);
x_14 = lean_expr_update_lambda(x_1, x_13, x_4, x_7);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_expr_has_loose_bvar(x_9, x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
lean_free_object(x_1);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_expr_lower_loose_bvars(x_9, x_16, x_16);
lean_dec(x_9);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; 
lean_dec(x_9);
lean_inc(x_4);
x_18 = (uint8_t)((x_6 << 24) >> 61);
x_19 = lean_expr_update_lambda(x_1, x_18, x_4, x_7);
return x_19;
}
}
}
case 6:
{
uint8_t x_20; 
lean_free_object(x_1);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_8, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_8, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_8, 0);
lean_dec(x_23);
lean_inc(x_4);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set_uint64(x_8, sizeof(void*)*3, x_6);
x_24 = (uint8_t)((x_6 << 24) >> 61);
x_25 = lean_expr_update_lambda(x_8, x_24, x_4, x_7);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_dec(x_8);
lean_inc(x_4);
x_26 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_5);
lean_ctor_set_uint64(x_26, sizeof(void*)*3, x_6);
x_27 = (uint8_t)((x_6 << 24) >> 61);
x_28 = lean_expr_update_lambda(x_26, x_27, x_4, x_7);
return x_28;
}
}
case 7:
{
uint8_t x_29; 
lean_free_object(x_1);
x_29 = !lean_is_exclusive(x_8);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_8, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_8, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_8, 0);
lean_dec(x_32);
lean_inc(x_4);
lean_ctor_set_tag(x_8, 6);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set_uint64(x_8, sizeof(void*)*3, x_6);
x_33 = (uint8_t)((x_6 << 24) >> 61);
x_34 = lean_expr_update_lambda(x_8, x_33, x_4, x_7);
return x_34;
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; 
lean_dec(x_8);
lean_inc(x_4);
x_35 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_35, 0, x_3);
lean_ctor_set(x_35, 1, x_4);
lean_ctor_set(x_35, 2, x_5);
lean_ctor_set_uint64(x_35, sizeof(void*)*3, x_6);
x_36 = (uint8_t)((x_6 << 24) >> 61);
x_37 = lean_expr_update_lambda(x_35, x_36, x_4, x_7);
return x_37;
}
}
case 11:
{
uint8_t x_38; 
lean_free_object(x_1);
x_38 = !lean_is_exclusive(x_8);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_8, 2);
lean_dec(x_39);
x_40 = lean_ctor_get(x_8, 1);
lean_dec(x_40);
x_41 = lean_ctor_get(x_8, 0);
lean_dec(x_41);
lean_inc(x_4);
lean_ctor_set_tag(x_8, 6);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set_uint64(x_8, sizeof(void*)*3, x_6);
x_42 = (uint8_t)((x_6 << 24) >> 61);
x_43 = lean_expr_update_lambda(x_8, x_42, x_4, x_7);
return x_43;
}
else
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; 
lean_dec(x_8);
lean_inc(x_4);
x_44 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_44, 0, x_3);
lean_ctor_set(x_44, 1, x_4);
lean_ctor_set(x_44, 2, x_5);
lean_ctor_set_uint64(x_44, sizeof(void*)*3, x_6);
x_45 = (uint8_t)((x_6 << 24) >> 61);
x_46 = lean_expr_update_lambda(x_44, x_45, x_4, x_7);
return x_46;
}
}
default: 
{
uint8_t x_47; lean_object* x_48; 
lean_dec(x_8);
lean_inc(x_4);
x_47 = (uint8_t)((x_6 << 24) >> 61);
x_48 = lean_expr_update_lambda(x_1, x_47, x_4, x_7);
return x_48;
}
}
}
else
{
uint8_t x_49; lean_object* x_50; 
lean_inc(x_4);
x_49 = (uint8_t)((x_6 << 24) >> 61);
x_50 = lean_expr_update_lambda(x_1, x_49, x_4, x_7);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_1, 0);
x_52 = lean_ctor_get(x_1, 1);
x_53 = lean_ctor_get(x_1, 2);
x_54 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_1);
lean_inc(x_53);
x_55 = l_Lean_Expr_eta(x_53);
if (lean_obj_tag(x_55) == 5)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
switch (lean_obj_tag(x_56)) {
case 0:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_nat_dec_eq(x_58, x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; lean_object* x_63; 
lean_dec(x_57);
lean_inc(x_52);
x_61 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_61, 0, x_51);
lean_ctor_set(x_61, 1, x_52);
lean_ctor_set(x_61, 2, x_53);
lean_ctor_set_uint64(x_61, sizeof(void*)*3, x_54);
x_62 = (uint8_t)((x_54 << 24) >> 61);
x_63 = lean_expr_update_lambda(x_61, x_62, x_52, x_55);
return x_63;
}
else
{
uint8_t x_64; 
x_64 = lean_expr_has_loose_bvar(x_57, x_59);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_expr_lower_loose_bvars(x_57, x_65, x_65);
lean_dec(x_57);
return x_66;
}
else
{
lean_object* x_67; uint8_t x_68; lean_object* x_69; 
lean_dec(x_57);
lean_inc(x_52);
x_67 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_67, 0, x_51);
lean_ctor_set(x_67, 1, x_52);
lean_ctor_set(x_67, 2, x_53);
lean_ctor_set_uint64(x_67, sizeof(void*)*3, x_54);
x_68 = (uint8_t)((x_54 << 24) >> 61);
x_69 = lean_expr_update_lambda(x_67, x_68, x_52, x_55);
return x_69;
}
}
}
case 6:
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 x_70 = x_56;
} else {
 lean_dec_ref(x_56);
 x_70 = lean_box(0);
}
lean_inc(x_52);
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(6, 3, 8);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_51);
lean_ctor_set(x_71, 1, x_52);
lean_ctor_set(x_71, 2, x_53);
lean_ctor_set_uint64(x_71, sizeof(void*)*3, x_54);
x_72 = (uint8_t)((x_54 << 24) >> 61);
x_73 = lean_expr_update_lambda(x_71, x_72, x_52, x_55);
return x_73;
}
case 7:
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 x_74 = x_56;
} else {
 lean_dec_ref(x_56);
 x_74 = lean_box(0);
}
lean_inc(x_52);
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(6, 3, 8);
} else {
 x_75 = x_74;
 lean_ctor_set_tag(x_75, 6);
}
lean_ctor_set(x_75, 0, x_51);
lean_ctor_set(x_75, 1, x_52);
lean_ctor_set(x_75, 2, x_53);
lean_ctor_set_uint64(x_75, sizeof(void*)*3, x_54);
x_76 = (uint8_t)((x_54 << 24) >> 61);
x_77 = lean_expr_update_lambda(x_75, x_76, x_52, x_55);
return x_77;
}
case 11:
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 x_78 = x_56;
} else {
 lean_dec_ref(x_56);
 x_78 = lean_box(0);
}
lean_inc(x_52);
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(6, 3, 8);
} else {
 x_79 = x_78;
 lean_ctor_set_tag(x_79, 6);
}
lean_ctor_set(x_79, 0, x_51);
lean_ctor_set(x_79, 1, x_52);
lean_ctor_set(x_79, 2, x_53);
lean_ctor_set_uint64(x_79, sizeof(void*)*3, x_54);
x_80 = (uint8_t)((x_54 << 24) >> 61);
x_81 = lean_expr_update_lambda(x_79, x_80, x_52, x_55);
return x_81;
}
default: 
{
lean_object* x_82; uint8_t x_83; lean_object* x_84; 
lean_dec(x_56);
lean_inc(x_52);
x_82 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_82, 0, x_51);
lean_ctor_set(x_82, 1, x_52);
lean_ctor_set(x_82, 2, x_53);
lean_ctor_set_uint64(x_82, sizeof(void*)*3, x_54);
x_83 = (uint8_t)((x_54 << 24) >> 61);
x_84 = lean_expr_update_lambda(x_82, x_83, x_52, x_55);
return x_84;
}
}
}
else
{
lean_object* x_85; uint8_t x_86; lean_object* x_87; 
lean_inc(x_52);
x_85 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_85, 0, x_51);
lean_ctor_set(x_85, 1, x_52);
lean_ctor_set(x_85, 2, x_53);
lean_ctor_set_uint64(x_85, sizeof(void*)*3, x_54);
x_86 = (uint8_t)((x_54 << 24) >> 61);
x_87 = lean_expr_update_lambda(x_85, x_86, x_52, x_55);
return x_87;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_alloc_closure((void*)(l_Lean_Level_instantiateParams), 2, 1);
lean_closure_set(x_15, 0, x_1);
x_16 = lean_box(0);
lean_inc(x_14);
x_17 = l_List_mapTRAux___rarg(x_15, x_14, x_16);
x_18 = lean_expr_update_const(x_2, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
x_22 = lean_alloc_closure((void*)(l_Lean_Level_instantiateParams), 2, 1);
lean_closure_set(x_22, 0, x_1);
x_23 = lean_box(0);
lean_inc(x_20);
x_24 = l_List_mapTRAux___rarg(x_22, x_20, x_23);
x_25 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set_uint64(x_25, sizeof(void*)*2, x_21);
x_26 = lean_expr_update_const(x_25, x_24);
return x_26;
}
}
case 5:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_inc(x_1);
x_30 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_28);
lean_inc(x_29);
x_31 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_29);
x_32 = lean_expr_update_app(x_2, x_30, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
x_35 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
lean_inc(x_33);
lean_inc(x_1);
x_36 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_33);
lean_inc(x_34);
x_37 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_34);
x_38 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set_uint64(x_38, sizeof(void*)*2, x_35);
x_39 = lean_expr_update_app(x_38, x_36, x_37);
return x_39;
}
}
case 6:
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_2);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_2, 1);
x_42 = lean_ctor_get(x_2, 2);
x_43 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_41);
lean_inc(x_1);
x_44 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_41);
lean_inc(x_42);
x_45 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_42);
x_46 = (uint8_t)((x_43 << 24) >> 61);
x_47 = lean_expr_update_lambda(x_2, x_46, x_44, x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_2, 0);
x_49 = lean_ctor_get(x_2, 1);
x_50 = lean_ctor_get(x_2, 2);
x_51 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_2);
lean_inc(x_49);
lean_inc(x_1);
x_52 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_49);
lean_inc(x_50);
x_53 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_50);
x_54 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_49);
lean_ctor_set(x_54, 2, x_50);
lean_ctor_set_uint64(x_54, sizeof(void*)*3, x_51);
x_55 = (uint8_t)((x_51 << 24) >> 61);
x_56 = lean_expr_update_lambda(x_54, x_55, x_52, x_53);
return x_56;
}
}
case 7:
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_2);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint64_t x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_2, 1);
x_59 = lean_ctor_get(x_2, 2);
x_60 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_58);
lean_inc(x_1);
x_61 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_58);
lean_inc(x_59);
x_62 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_59);
x_63 = (uint8_t)((x_60 << 24) >> 61);
x_64 = lean_expr_update_forall(x_2, x_63, x_61, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_2, 0);
x_66 = lean_ctor_get(x_2, 1);
x_67 = lean_ctor_get(x_2, 2);
x_68 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_2);
lean_inc(x_66);
lean_inc(x_1);
x_69 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_66);
lean_inc(x_67);
x_70 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_67);
x_71 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_66);
lean_ctor_set(x_71, 2, x_67);
lean_ctor_set_uint64(x_71, sizeof(void*)*3, x_68);
x_72 = (uint8_t)((x_68 << 24) >> 61);
x_73 = lean_expr_update_forall(x_71, x_72, x_69, x_70);
return x_73;
}
}
case 8:
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_2);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_ctor_get(x_2, 1);
x_76 = lean_ctor_get(x_2, 2);
x_77 = lean_ctor_get(x_2, 3);
lean_inc(x_75);
lean_inc(x_1);
x_78 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_75);
lean_inc(x_76);
lean_inc(x_1);
x_79 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_76);
lean_inc(x_77);
x_80 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_77);
x_81 = lean_expr_update_let(x_2, x_78, x_79, x_80);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_82 = lean_ctor_get(x_2, 0);
x_83 = lean_ctor_get(x_2, 1);
x_84 = lean_ctor_get(x_2, 2);
x_85 = lean_ctor_get(x_2, 3);
x_86 = lean_ctor_get_uint64(x_2, sizeof(void*)*4);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_2);
lean_inc(x_83);
lean_inc(x_1);
x_87 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_83);
lean_inc(x_84);
lean_inc(x_1);
x_88 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_84);
lean_inc(x_85);
x_89 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_85);
x_90 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_90, 0, x_82);
lean_ctor_set(x_90, 1, x_83);
lean_ctor_set(x_90, 2, x_84);
lean_ctor_set(x_90, 3, x_85);
lean_ctor_set_uint64(x_90, sizeof(void*)*4, x_86);
x_91 = lean_expr_update_let(x_90, x_87, x_88, x_89);
return x_91;
}
}
case 10:
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_2);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_2, 1);
lean_inc(x_93);
x_94 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_93);
x_95 = lean_expr_update_mdata(x_2, x_94);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; uint64_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_ctor_get(x_2, 0);
x_97 = lean_ctor_get(x_2, 1);
x_98 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_2);
lean_inc(x_97);
x_99 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_97);
x_100 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_100, 0, x_96);
lean_ctor_set(x_100, 1, x_97);
lean_ctor_set_uint64(x_100, sizeof(void*)*2, x_98);
x_101 = lean_expr_update_mdata(x_100, x_99);
return x_101;
}
}
case 11:
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_2);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_2, 2);
lean_inc(x_103);
x_104 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_103);
x_105 = lean_expr_update_proj(x_2, x_104);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint64_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_106 = lean_ctor_get(x_2, 0);
x_107 = lean_ctor_get(x_2, 1);
x_108 = lean_ctor_get(x_2, 2);
x_109 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_2);
lean_inc(x_108);
x_110 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_108);
x_111 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_107);
lean_ctor_set(x_111, 2, x_108);
lean_ctor_set_uint64(x_111, sizeof(void*)*3, x_109);
x_112 = lean_expr_update_proj(x_111, x_110);
return x_112;
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
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubst(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_instantiateLevelParams___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_9);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_box(0);
lean_inc(x_15);
x_17 = l_List_mapTRAux___at_Lean_Expr_instantiateLevelParams___spec__4(x_1, x_2, x_15, x_16);
x_18 = lean_expr_update_const(x_3, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_22 = lean_box(0);
lean_inc(x_20);
x_23 = l_List_mapTRAux___at_Lean_Expr_instantiateLevelParams___spec__4(x_1, x_2, x_20, x_22);
x_24 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set_uint64(x_24, sizeof(void*)*2, x_21);
x_25 = lean_expr_update_const(x_24, x_23);
return x_25;
}
}
case 5:
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
x_29 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_27);
lean_inc(x_28);
x_30 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_28);
x_31 = lean_expr_update_app(x_3, x_29, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_3, 0);
x_33 = lean_ctor_get(x_3, 1);
x_34 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_3);
lean_inc(x_32);
x_35 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_32);
lean_inc(x_33);
x_36 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_33);
x_37 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set_uint64(x_37, sizeof(void*)*2, x_34);
x_38 = lean_expr_update_app(x_37, x_35, x_36);
return x_38;
}
}
case 6:
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_3);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_3, 1);
x_41 = lean_ctor_get(x_3, 2);
x_42 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_40);
x_43 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_40);
lean_inc(x_41);
x_44 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_41);
x_45 = (uint8_t)((x_42 << 24) >> 61);
x_46 = lean_expr_update_lambda(x_3, x_45, x_43, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint64_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_ctor_get(x_3, 1);
x_49 = lean_ctor_get(x_3, 2);
x_50 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_3);
lean_inc(x_48);
x_51 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_48);
lean_inc(x_49);
x_52 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_49);
x_53 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set_uint64(x_53, sizeof(void*)*3, x_50);
x_54 = (uint8_t)((x_50 << 24) >> 61);
x_55 = lean_expr_update_lambda(x_53, x_54, x_51, x_52);
return x_55;
}
}
case 7:
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_3);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint64_t x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_3, 1);
x_58 = lean_ctor_get(x_3, 2);
x_59 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_57);
x_60 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_57);
lean_inc(x_58);
x_61 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_58);
x_62 = (uint8_t)((x_59 << 24) >> 61);
x_63 = lean_expr_update_forall(x_3, x_62, x_60, x_61);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint64_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_3, 0);
x_65 = lean_ctor_get(x_3, 1);
x_66 = lean_ctor_get(x_3, 2);
x_67 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_3);
lean_inc(x_65);
x_68 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_65);
lean_inc(x_66);
x_69 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_66);
x_70 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_65);
lean_ctor_set(x_70, 2, x_66);
lean_ctor_set_uint64(x_70, sizeof(void*)*3, x_67);
x_71 = (uint8_t)((x_67 << 24) >> 61);
x_72 = lean_expr_update_forall(x_70, x_71, x_68, x_69);
return x_72;
}
}
case 8:
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_3);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_3, 1);
x_75 = lean_ctor_get(x_3, 2);
x_76 = lean_ctor_get(x_3, 3);
lean_inc(x_74);
x_77 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_74);
lean_inc(x_75);
x_78 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_75);
lean_inc(x_76);
x_79 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_76);
x_80 = lean_expr_update_let(x_3, x_77, x_78, x_79);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint64_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_81 = lean_ctor_get(x_3, 0);
x_82 = lean_ctor_get(x_3, 1);
x_83 = lean_ctor_get(x_3, 2);
x_84 = lean_ctor_get(x_3, 3);
x_85 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_3);
lean_inc(x_82);
x_86 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_82);
lean_inc(x_83);
x_87 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_83);
lean_inc(x_84);
x_88 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_84);
x_89 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_89, 0, x_81);
lean_ctor_set(x_89, 1, x_82);
lean_ctor_set(x_89, 2, x_83);
lean_ctor_set(x_89, 3, x_84);
lean_ctor_set_uint64(x_89, sizeof(void*)*4, x_85);
x_90 = lean_expr_update_let(x_89, x_86, x_87, x_88);
return x_90;
}
}
case 10:
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_3);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_3, 1);
lean_inc(x_92);
x_93 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_92);
x_94 = lean_expr_update_mdata(x_3, x_93);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; uint64_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_3, 0);
x_96 = lean_ctor_get(x_3, 1);
x_97 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_3);
lean_inc(x_96);
x_98 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_96);
x_99 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_96);
lean_ctor_set_uint64(x_99, sizeof(void*)*2, x_97);
x_100 = lean_expr_update_mdata(x_99, x_98);
return x_100;
}
}
case 11:
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_3);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_3, 2);
lean_inc(x_102);
x_103 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_102);
x_104 = lean_expr_update_proj(x_3, x_103);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint64_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_105 = lean_ctor_get(x_3, 0);
x_106 = lean_ctor_get(x_3, 1);
x_107 = lean_ctor_get(x_3, 2);
x_108 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_3);
lean_inc(x_107);
x_109 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_107);
x_110 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_110, 0, x_105);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set(x_110, 2, x_107);
lean_ctor_set_uint64(x_110, sizeof(void*)*3, x_108);
x_111 = lean_expr_update_proj(x_110, x_109);
return x_111;
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
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_2, x_3, x_1);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_instantiateLevelParams___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTRAux___at_Lean_Expr_instantiateLevelParams___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubstArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubstArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_instantiateLevelParamsArray___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_9);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_box(0);
lean_inc(x_15);
x_17 = l_List_mapTRAux___at_Lean_Expr_instantiateLevelParamsArray___spec__4(x_1, x_2, x_15, x_16);
x_18 = lean_expr_update_const(x_3, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_22 = lean_box(0);
lean_inc(x_20);
x_23 = l_List_mapTRAux___at_Lean_Expr_instantiateLevelParamsArray___spec__4(x_1, x_2, x_20, x_22);
x_24 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set_uint64(x_24, sizeof(void*)*2, x_21);
x_25 = lean_expr_update_const(x_24, x_23);
return x_25;
}
}
case 5:
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
x_29 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_27);
lean_inc(x_28);
x_30 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_28);
x_31 = lean_expr_update_app(x_3, x_29, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_3, 0);
x_33 = lean_ctor_get(x_3, 1);
x_34 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_3);
lean_inc(x_32);
x_35 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_32);
lean_inc(x_33);
x_36 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_33);
x_37 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set_uint64(x_37, sizeof(void*)*2, x_34);
x_38 = lean_expr_update_app(x_37, x_35, x_36);
return x_38;
}
}
case 6:
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_3);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_3, 1);
x_41 = lean_ctor_get(x_3, 2);
x_42 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_40);
x_43 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_40);
lean_inc(x_41);
x_44 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_41);
x_45 = (uint8_t)((x_42 << 24) >> 61);
x_46 = lean_expr_update_lambda(x_3, x_45, x_43, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint64_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_ctor_get(x_3, 1);
x_49 = lean_ctor_get(x_3, 2);
x_50 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_3);
lean_inc(x_48);
x_51 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_48);
lean_inc(x_49);
x_52 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_49);
x_53 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set_uint64(x_53, sizeof(void*)*3, x_50);
x_54 = (uint8_t)((x_50 << 24) >> 61);
x_55 = lean_expr_update_lambda(x_53, x_54, x_51, x_52);
return x_55;
}
}
case 7:
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_3);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint64_t x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_3, 1);
x_58 = lean_ctor_get(x_3, 2);
x_59 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_57);
x_60 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_57);
lean_inc(x_58);
x_61 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_58);
x_62 = (uint8_t)((x_59 << 24) >> 61);
x_63 = lean_expr_update_forall(x_3, x_62, x_60, x_61);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint64_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_3, 0);
x_65 = lean_ctor_get(x_3, 1);
x_66 = lean_ctor_get(x_3, 2);
x_67 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_3);
lean_inc(x_65);
x_68 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_65);
lean_inc(x_66);
x_69 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_66);
x_70 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_65);
lean_ctor_set(x_70, 2, x_66);
lean_ctor_set_uint64(x_70, sizeof(void*)*3, x_67);
x_71 = (uint8_t)((x_67 << 24) >> 61);
x_72 = lean_expr_update_forall(x_70, x_71, x_68, x_69);
return x_72;
}
}
case 8:
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_3);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_3, 1);
x_75 = lean_ctor_get(x_3, 2);
x_76 = lean_ctor_get(x_3, 3);
lean_inc(x_74);
x_77 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_74);
lean_inc(x_75);
x_78 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_75);
lean_inc(x_76);
x_79 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_76);
x_80 = lean_expr_update_let(x_3, x_77, x_78, x_79);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint64_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_81 = lean_ctor_get(x_3, 0);
x_82 = lean_ctor_get(x_3, 1);
x_83 = lean_ctor_get(x_3, 2);
x_84 = lean_ctor_get(x_3, 3);
x_85 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_3);
lean_inc(x_82);
x_86 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_82);
lean_inc(x_83);
x_87 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_83);
lean_inc(x_84);
x_88 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_84);
x_89 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_89, 0, x_81);
lean_ctor_set(x_89, 1, x_82);
lean_ctor_set(x_89, 2, x_83);
lean_ctor_set(x_89, 3, x_84);
lean_ctor_set_uint64(x_89, sizeof(void*)*4, x_85);
x_90 = lean_expr_update_let(x_89, x_86, x_87, x_88);
return x_90;
}
}
case 10:
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_3);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_3, 1);
lean_inc(x_92);
x_93 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_92);
x_94 = lean_expr_update_mdata(x_3, x_93);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; uint64_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_3, 0);
x_96 = lean_ctor_get(x_3, 1);
x_97 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_3);
lean_inc(x_96);
x_98 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_96);
x_99 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_96);
lean_ctor_set_uint64(x_99, sizeof(void*)*2, x_97);
x_100 = lean_expr_update_mdata(x_99, x_98);
return x_100;
}
}
case 11:
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_3);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_3, 2);
lean_inc(x_102);
x_103 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_102);
x_104 = lean_expr_update_proj(x_3, x_103);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint64_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_105 = lean_ctor_get(x_3, 0);
x_106 = lean_ctor_get(x_3, 1);
x_107 = lean_ctor_get(x_3, 2);
x_108 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_3);
lean_inc(x_107);
x_109 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_107);
x_110 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_110, 0, x_105);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set(x_110, 2, x_107);
lean_ctor_set_uint64(x_110, sizeof(void*)*3, x_108);
x_111 = lean_expr_update_proj(x_110, x_109);
return x_111;
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
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_2, x_3, x_1);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_instantiateLevelParamsArray___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTRAux___at_Lean_Expr_instantiateLevelParamsArray___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_5, x_4);
x_7 = lean_box(0);
x_8 = l_Lean_KVMap_insertCore(x_7, x_2, x_6);
x_9 = l_Lean_mkMData(x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_setOption___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at_Lean_Expr_setPPExplicit___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_4, 0, x_3);
x_5 = lean_box(0);
x_6 = l_Lean_KVMap_insertCore(x_5, x_2, x_4);
x_7 = l_Lean_mkMData(x_6, x_1);
return x_7;
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
lean_object* x_1; 
x_1 = lean_mk_string("explicit");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_setPPExplicit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_setPPExplicit___closed__2;
x_2 = l_Lean_Expr_setPPExplicit___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_setPPExplicit___closed__4;
x_4 = l_Lean_Expr_setOption___at_Lean_Expr_setPPExplicit___spec__1(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at_Lean_Expr_setPPExplicit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Expr_setOption___at_Lean_Expr_setPPExplicit___spec__1(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Expr_setPPExplicit(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Expr_setPPUniverses___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("universes");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_setPPUniverses___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_setPPExplicit___closed__2;
x_2 = l_Lean_Expr_setPPUniverses___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_setPPUniverses___closed__2;
x_4 = l_Lean_Expr_setOption___at_Lean_Expr_setPPExplicit___spec__1(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Expr_setPPUniverses(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicit___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicitForExposingMVars___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l_Lean_Expr_hasMVar(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
if (x_10 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 0;
x_14 = l_Lean_Expr_setPPExplicit(x_9, x_13);
x_15 = x_14;
x_16 = lean_array_uset(x_8, x_2, x_15);
x_2 = x_12;
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = x_9;
x_19 = lean_array_uset(x_8, x_2, x_18);
x_2 = x_12;
x_3 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object* x_1) {
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
x_16 = l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicitForExposingMVars___spec__1(x_13, x_14, x_15);
x_17 = x_16;
x_18 = l_Lean_mkAppN(x_4, x_17);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicitForExposingMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicitForExposingMVars___spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_mkAnnotation___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_KVMap_empty;
x_4 = l_Lean_mkAnnotation___closed__1;
x_5 = l_Lean_KVMap_insertCore(x_3, x_1, x_4);
x_6 = l_Lean_mkMData(x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_List_lengthTRAux___rarg(x_3, x_5);
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
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_annotation_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_mkLetFunAnnotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("let_fun");
return x_1;
}
}
static lean_object* _init_l_Lean_mkLetFunAnnotation___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkLetFunAnnotation___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLetFunAnnotation(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkLetFunAnnotation___closed__2;
x_3 = l_Lean_mkAnnotation(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_letFunAnnotation_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkLetFunAnnotation___closed__2;
x_3 = l_Lean_annotation_x3f(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_letFunAnnotation_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_letFunAnnotation_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_isLetFun(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_letFunAnnotation_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Expr_isApp(x_4);
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
x_7 = l_Lean_Expr_appFn_x21(x_4);
lean_dec(x_4);
x_8 = l_Lean_Expr_isLambda(x_7);
lean_dec(x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLetFun___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_isLetFun(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkLHSGoal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_lhsGoal");
return x_1;
}
}
static lean_object* _init_l_Lean_mkLHSGoal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkLHSGoal___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLHSGoal(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkLHSGoal___closed__2;
x_3 = l_Lean_mkAnnotation(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_isLHSGoal_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Eq");
return x_1;
}
}
static lean_object* _init_l_Lean_isLHSGoal_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_isLHSGoal_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkLHSGoal___closed__2;
x_3 = l_Lean_annotation_x3f(x_2, x_1);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = l_Lean_isLHSGoal_x3f___closed__2;
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Expr_isAppOfArity(x_6, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_free_object(x_3);
lean_dec(x_6);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Expr_appFn_x21(x_6);
lean_dec(x_6);
x_12 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = l_Lean_isLHSGoal_x3f___closed__2;
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Expr_isAppOfArity(x_13, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l_Lean_Expr_appFn_x21(x_13);
lean_dec(x_13);
x_19 = l_Lean_Expr_appArg_x21(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_isLHSGoal_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_2(x_4, lean_box(0), x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_inc(x_1);
x_4 = l_Lean_mkFreshId___rarg(x_1, x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___rarg___lambda__1), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_inc(x_1);
x_4 = l_Lean_mkFreshId___rarg(x_1, x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_mkFreshFVarId___rarg___lambda__1), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkFreshMVarId___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_mkNot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Not");
return x_1;
}
}
static lean_object* _init_l_Lean_mkNot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkNot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkNot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkNot___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkNot___closed__3;
x_3 = l_Lean_mkApp(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_mkOr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Or");
return x_1;
}
}
static lean_object* _init_l_Lean_mkOr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkOr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkOr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkOr___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_mkOr___closed__3;
x_4 = l_Lean_mkAppB(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("And");
return x_1;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkAnd___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkAnd___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_mkAnd___closed__3;
x_4 = l_Lean_mkAppB(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_mkEM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Classical");
return x_1;
}
}
static lean_object* _init_l_Lean_mkEM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkEM___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkEM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("em");
return x_1;
}
}
static lean_object* _init_l_Lean_mkEM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkEM___closed__2;
x_2 = l_Lean_mkEM___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkEM___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkEM___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkEM___closed__5;
x_3 = l_Lean_mkApp(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_KVMap(lean_object*);
lean_object* initialize_Lean_Level(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Expr(lean_object* w) {
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
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__1 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__1);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__2 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__2);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__3 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__3();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__3);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__4 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__4();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__4);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__5 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__5();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__5);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__6 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__6();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__6);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__7 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__7();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__7);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__8 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__8();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_98____closed__8);
l_Lean_instReprLiteral___closed__1 = _init_l_Lean_instReprLiteral___closed__1();
lean_mark_persistent(l_Lean_instReprLiteral___closed__1);
l_Lean_instReprLiteral = _init_l_Lean_instReprLiteral();
lean_mark_persistent(l_Lean_instReprLiteral);
l_Lean_instHashableLiteral___closed__1 = _init_l_Lean_instHashableLiteral___closed__1();
lean_mark_persistent(l_Lean_instHashableLiteral___closed__1);
l_Lean_instHashableLiteral = _init_l_Lean_instHashableLiteral();
lean_mark_persistent(l_Lean_instHashableLiteral);
l_Lean_instLTLiteral = _init_l_Lean_instLTLiteral();
lean_mark_persistent(l_Lean_instLTLiteral);
l_Lean_BinderInfo_noConfusion___rarg___closed__1 = _init_l_Lean_BinderInfo_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_BinderInfo_noConfusion___rarg___closed__1);
l_Lean_instInhabitedBinderInfo = _init_l_Lean_instInhabitedBinderInfo();
l_Lean_instBEqBinderInfo___closed__1 = _init_l_Lean_instBEqBinderInfo___closed__1();
lean_mark_persistent(l_Lean_instBEqBinderInfo___closed__1);
l_Lean_instBEqBinderInfo = _init_l_Lean_instBEqBinderInfo();
lean_mark_persistent(l_Lean_instBEqBinderInfo);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__1 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__1);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__2 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__2);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__3 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__3();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__3);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__4 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__4();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__4);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__5 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__5();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__5);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__6 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__6();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__6);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__7 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__7();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__7);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__8 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__8();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__8);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__9 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__9();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__9);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__10 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__10();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__10);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__11 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__11();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__11);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__12 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__12();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__12);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__13 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__13();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__13);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__14 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__14();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__14);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__15 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__15();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__15);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__16 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__16();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__16);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__17 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__17();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__17);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__18 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__18();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__18);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__19 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__19();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__19);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__20 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__20();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__20);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__21 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__21();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__21);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__22 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__22();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__22);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__23 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__23();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__23);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__24 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__24();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__24);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__25 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__25();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__25);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__26 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__26();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__26);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__27 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__27();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__27);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__28 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__28();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__28);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__29 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__29();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__29);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__30 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__30();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_324____closed__30);
l_Lean_instReprBinderInfo___closed__1 = _init_l_Lean_instReprBinderInfo___closed__1();
lean_mark_persistent(l_Lean_instReprBinderInfo___closed__1);
l_Lean_instReprBinderInfo = _init_l_Lean_instReprBinderInfo();
lean_mark_persistent(l_Lean_instReprBinderInfo);
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
l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__5 = _init_l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__5();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_mkDataCore___closed__5);
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
l_Lean_instInhabitedFVarId = _init_l_Lean_instInhabitedFVarId();
lean_mark_persistent(l_Lean_instInhabitedFVarId);
l_Lean_instBEqFVarId___closed__1 = _init_l_Lean_instBEqFVarId___closed__1();
lean_mark_persistent(l_Lean_instBEqFVarId___closed__1);
l_Lean_instBEqFVarId = _init_l_Lean_instBEqFVarId();
lean_mark_persistent(l_Lean_instBEqFVarId);
l_Lean_instHashableFVarId___closed__1 = _init_l_Lean_instHashableFVarId___closed__1();
lean_mark_persistent(l_Lean_instHashableFVarId___closed__1);
l_Lean_instHashableFVarId = _init_l_Lean_instHashableFVarId();
lean_mark_persistent(l_Lean_instHashableFVarId);
l_Lean_instFVarIdSetInhabited = _init_l_Lean_instFVarIdSetInhabited();
lean_mark_persistent(l_Lean_instFVarIdSetInhabited);
l_Lean_instFVarIdSetEmptyCollection = _init_l_Lean_instFVarIdSetEmptyCollection();
lean_mark_persistent(l_Lean_instFVarIdSetEmptyCollection);
l_Lean_instForInFVarIdSetFVarId___closed__1 = _init_l_Lean_instForInFVarIdSetFVarId___closed__1();
lean_mark_persistent(l_Lean_instForInFVarIdSetFVarId___closed__1);
l_Lean_instForInFVarIdSetFVarId___closed__2 = _init_l_Lean_instForInFVarIdSetFVarId___closed__2();
lean_mark_persistent(l_Lean_instForInFVarIdSetFVarId___closed__2);
l_Lean_instFVarIdHashSetInhabited___closed__1 = _init_l_Lean_instFVarIdHashSetInhabited___closed__1();
lean_mark_persistent(l_Lean_instFVarIdHashSetInhabited___closed__1);
l_Lean_instFVarIdHashSetInhabited = _init_l_Lean_instFVarIdHashSetInhabited();
lean_mark_persistent(l_Lean_instFVarIdHashSetInhabited);
l_Lean_instFVarIdHashSetEmptyCollection = _init_l_Lean_instFVarIdHashSetEmptyCollection();
lean_mark_persistent(l_Lean_instFVarIdHashSetEmptyCollection);
l_Lean_instInhabitedExpr___closed__1 = _init_l_Lean_instInhabitedExpr___closed__1();
l_Lean_instInhabitedExpr___closed__2 = _init_l_Lean_instInhabitedExpr___closed__2();
lean_mark_persistent(l_Lean_instInhabitedExpr___closed__2);
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
l_Lean_Expr_ctorName___closed__11 = _init_l_Lean_Expr_ctorName___closed__11();
lean_mark_persistent(l_Lean_Expr_ctorName___closed__11);
l_Lean_Expr_ctorName___closed__12 = _init_l_Lean_Expr_ctorName___closed__12();
lean_mark_persistent(l_Lean_Expr_ctorName___closed__12);
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
l_Lean_Literal_type___closed__5 = _init_l_Lean_Literal_type___closed__5();
lean_mark_persistent(l_Lean_Literal_type___closed__5);
l_Lean_Literal_type___closed__6 = _init_l_Lean_Literal_type___closed__6();
lean_mark_persistent(l_Lean_Literal_type___closed__6);
l_Lean_mkSimpleThunkType___closed__1 = _init_l_Lean_mkSimpleThunkType___closed__1();
lean_mark_persistent(l_Lean_mkSimpleThunkType___closed__1);
l_Lean_mkSimpleThunkType___closed__2 = _init_l_Lean_mkSimpleThunkType___closed__2();
lean_mark_persistent(l_Lean_mkSimpleThunkType___closed__2);
l_Lean_mkSimpleThunkType___closed__3 = _init_l_Lean_mkSimpleThunkType___closed__3();
lean_mark_persistent(l_Lean_mkSimpleThunkType___closed__3);
l_Lean_mkSimpleThunk___closed__1 = _init_l_Lean_mkSimpleThunk___closed__1();
lean_mark_persistent(l_Lean_mkSimpleThunk___closed__1);
l_Lean_mkSimpleThunk___closed__2 = _init_l_Lean_mkSimpleThunk___closed__2();
lean_mark_persistent(l_Lean_mkSimpleThunk___closed__2);
l_Lean_mkNatLit___closed__1 = _init_l_Lean_mkNatLit___closed__1();
lean_mark_persistent(l_Lean_mkNatLit___closed__1);
l_Lean_mkNatLit___closed__2 = _init_l_Lean_mkNatLit___closed__2();
lean_mark_persistent(l_Lean_mkNatLit___closed__2);
l_Lean_mkNatLit___closed__3 = _init_l_Lean_mkNatLit___closed__3();
lean_mark_persistent(l_Lean_mkNatLit___closed__3);
l_Lean_mkNatLit___closed__4 = _init_l_Lean_mkNatLit___closed__4();
lean_mark_persistent(l_Lean_mkNatLit___closed__4);
l_Lean_mkNatLit___closed__5 = _init_l_Lean_mkNatLit___closed__5();
lean_mark_persistent(l_Lean_mkNatLit___closed__5);
l_Lean_mkNatLit___closed__6 = _init_l_Lean_mkNatLit___closed__6();
lean_mark_persistent(l_Lean_mkNatLit___closed__6);
l_Lean_mkNatLit___closed__7 = _init_l_Lean_mkNatLit___closed__7();
lean_mark_persistent(l_Lean_mkNatLit___closed__7);
l_Lean_mkNatLit___closed__8 = _init_l_Lean_mkNatLit___closed__8();
lean_mark_persistent(l_Lean_mkNatLit___closed__8);
l_Lean_mkNatLit___closed__9 = _init_l_Lean_mkNatLit___closed__9();
lean_mark_persistent(l_Lean_mkNatLit___closed__9);
l_Lean_mkNatLit___closed__10 = _init_l_Lean_mkNatLit___closed__10();
lean_mark_persistent(l_Lean_mkNatLit___closed__10);
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
l_Lean_Expr_getRevArg_x21___closed__3 = _init_l_Lean_Expr_getRevArg_x21___closed__3();
lean_mark_persistent(l_Lean_Expr_getRevArg_x21___closed__3);
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
l_Lean_Expr_mdataExpr_x21___closed__1 = _init_l_Lean_Expr_mdataExpr_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_mdataExpr_x21___closed__1);
l_Lean_Expr_mdataExpr_x21___closed__2 = _init_l_Lean_Expr_mdataExpr_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_mdataExpr_x21___closed__2);
l_Lean_Expr_mdataExpr_x21___closed__3 = _init_l_Lean_Expr_mdataExpr_x21___closed__3();
lean_mark_persistent(l_Lean_Expr_mdataExpr_x21___closed__3);
l_Lean_Expr_replaceFVar___closed__1 = _init_l_Lean_Expr_replaceFVar___closed__1();
lean_mark_persistent(l_Lean_Expr_replaceFVar___closed__1);
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
l_Lean_Expr_setPPExplicit___closed__4 = _init_l_Lean_Expr_setPPExplicit___closed__4();
lean_mark_persistent(l_Lean_Expr_setPPExplicit___closed__4);
l_Lean_Expr_setPPUniverses___closed__1 = _init_l_Lean_Expr_setPPUniverses___closed__1();
lean_mark_persistent(l_Lean_Expr_setPPUniverses___closed__1);
l_Lean_Expr_setPPUniverses___closed__2 = _init_l_Lean_Expr_setPPUniverses___closed__2();
lean_mark_persistent(l_Lean_Expr_setPPUniverses___closed__2);
l_Lean_mkAnnotation___closed__1 = _init_l_Lean_mkAnnotation___closed__1();
lean_mark_persistent(l_Lean_mkAnnotation___closed__1);
l_Lean_mkLetFunAnnotation___closed__1 = _init_l_Lean_mkLetFunAnnotation___closed__1();
lean_mark_persistent(l_Lean_mkLetFunAnnotation___closed__1);
l_Lean_mkLetFunAnnotation___closed__2 = _init_l_Lean_mkLetFunAnnotation___closed__2();
lean_mark_persistent(l_Lean_mkLetFunAnnotation___closed__2);
l_Lean_mkLHSGoal___closed__1 = _init_l_Lean_mkLHSGoal___closed__1();
lean_mark_persistent(l_Lean_mkLHSGoal___closed__1);
l_Lean_mkLHSGoal___closed__2 = _init_l_Lean_mkLHSGoal___closed__2();
lean_mark_persistent(l_Lean_mkLHSGoal___closed__2);
l_Lean_isLHSGoal_x3f___closed__1 = _init_l_Lean_isLHSGoal_x3f___closed__1();
lean_mark_persistent(l_Lean_isLHSGoal_x3f___closed__1);
l_Lean_isLHSGoal_x3f___closed__2 = _init_l_Lean_isLHSGoal_x3f___closed__2();
lean_mark_persistent(l_Lean_isLHSGoal_x3f___closed__2);
l_Lean_mkNot___closed__1 = _init_l_Lean_mkNot___closed__1();
lean_mark_persistent(l_Lean_mkNot___closed__1);
l_Lean_mkNot___closed__2 = _init_l_Lean_mkNot___closed__2();
lean_mark_persistent(l_Lean_mkNot___closed__2);
l_Lean_mkNot___closed__3 = _init_l_Lean_mkNot___closed__3();
lean_mark_persistent(l_Lean_mkNot___closed__3);
l_Lean_mkOr___closed__1 = _init_l_Lean_mkOr___closed__1();
lean_mark_persistent(l_Lean_mkOr___closed__1);
l_Lean_mkOr___closed__2 = _init_l_Lean_mkOr___closed__2();
lean_mark_persistent(l_Lean_mkOr___closed__2);
l_Lean_mkOr___closed__3 = _init_l_Lean_mkOr___closed__3();
lean_mark_persistent(l_Lean_mkOr___closed__3);
l_Lean_mkAnd___closed__1 = _init_l_Lean_mkAnd___closed__1();
lean_mark_persistent(l_Lean_mkAnd___closed__1);
l_Lean_mkAnd___closed__2 = _init_l_Lean_mkAnd___closed__2();
lean_mark_persistent(l_Lean_mkAnd___closed__2);
l_Lean_mkAnd___closed__3 = _init_l_Lean_mkAnd___closed__3();
lean_mark_persistent(l_Lean_mkAnd___closed__3);
l_Lean_mkEM___closed__1 = _init_l_Lean_mkEM___closed__1();
lean_mark_persistent(l_Lean_mkEM___closed__1);
l_Lean_mkEM___closed__2 = _init_l_Lean_mkEM___closed__2();
lean_mark_persistent(l_Lean_mkEM___closed__2);
l_Lean_mkEM___closed__3 = _init_l_Lean_mkEM___closed__3();
lean_mark_persistent(l_Lean_mkEM___closed__3);
l_Lean_mkEM___closed__4 = _init_l_Lean_mkEM___closed__4();
lean_mark_persistent(l_Lean_mkEM___closed__4);
l_Lean_mkEM___closed__5 = _init_l_Lean_mkEM___closed__5();
lean_mark_persistent(l_Lean_mkEM___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
