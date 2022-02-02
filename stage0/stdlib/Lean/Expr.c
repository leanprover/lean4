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
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__27;
static lean_object* l_Lean_Expr_ctorName___closed__7;
static lean_object* l_Lean_mkNatLit___closed__8;
LEAN_EXPORT lean_object* l_Lean_instLTLiteral;
static lean_object* l_Lean_mkLHSGoal___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateSort___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_mkDecIsFalse___closed__2;
static lean_object* l_Lean_Expr_bvarIdx_x21___closed__3;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instReprData__1___lambda__3___closed__1;
static lean_object* l_Lean_mkNatLit___closed__4;
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__9;
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isNatLit(lean_object*);
static lean_object* l_Lean_Expr_replaceFVar___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__42;
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Expr_projExpr_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object*);
static lean_object* l_Lean_instReprData__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_instReprData__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
static lean_object* l_Lean_Expr_bindingDomain_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_instReprExpr___closed__1;
static lean_object* l_Lean_Expr_getRevArg_x21___closed__1;
static lean_object* l_Lean_instReprBinderInfo___closed__1;
static lean_object* l_Lean_mkNatLit___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_letBody_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_updateConst___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkDecIsTrue___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
static lean_object* l_Lean_mkDecIsFalse___closed__1;
static lean_object* l_Lean_mkAnd___closed__2;
uint64_t lean_uint8_to_uint64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_mkEM___closed__1;
static lean_object* l_Lean_Expr_litValue_x21___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkSimpleThunkType___closed__3;
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_object* l_Lean_Expr_instHashableExpr___closed__1;
static lean_object* l_Lean_mkInaccessible___closed__1;
LEAN_EXPORT uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1719_(lean_object*);
static lean_object* l_Lean_Expr_litValue_x21___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__1(lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
uint32_t lean_uint8_to_uint32(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
static lean_object* l_Lean_Expr_letBody_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object*);
static lean_object* l_Lean_Expr_projIdx_x21___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkAppN___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkEM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object*);
static lean_object* l_Lean_Expr_updateLambda_x21___closed__3;
uint64_t lean_uint64_add(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_bindingInfo_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__13;
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instHashableExprStructEq;
uint64_t lean_bool_to_uint64(uint8_t);
static lean_object* l_Lean_Expr_updateMData_x21___closed__2;
static lean_object* l_Lean_mkNatLit___closed__9;
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRevAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_instantiateLevelParams___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_letValue_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object*);
static lean_object* l_Lean_Expr_updateMData_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__11;
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__41;
LEAN_EXPORT uint64_t l_Lean_Expr_Data_hash(uint64_t);
LEAN_EXPORT lean_object* l_Lean_mkLHSGoal(lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
static lean_object* l_Lean_mkDecIsTrue___closed__5;
LEAN_EXPORT lean_object* l_Lean_instFVarIdSetEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_consumeAutoOptParam(lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Literal_type___closed__5;
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__12;
static lean_object* l_Lean_instReprData__1___lambda__3___closed__2;
static lean_object* l_Lean_Expr_ctorName___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_litValue_x21___closed__3;
static lean_object* l_Lean_Expr_constName_x21___closed__1;
static lean_object* l_Lean_Expr_mvarId_x21___closed__1;
uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_mkData___closed__3;
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder(uint64_t, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object*, uint8_t);
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
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__26;
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_mkData___closed__5;
static lean_object* l_Lean_Expr_mvarId_x21___closed__2;
static lean_object* l_Lean_mkSimpleThunkType___closed__1;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object*);
static lean_object* l_Lean_Expr_bindingBody_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toCtorIdx(uint8_t);
static lean_object* l_Lean_Expr_ctorName___closed__4;
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_mkConst___spec__2(uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
static lean_object* l_Lean_Literal_type___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__3(uint64_t, lean_object*, lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLetFunAnnotation(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object*);
static lean_object* l_Lean_ExprStructEq_instBEqExprStructEq___closed__1;
static lean_object* l_Lean_Expr_updateForall_x21___closed__1;
static lean_object* l_Lean_ExprStructEq_instHashableExprStructEq___closed__1;
static lean_object* l_Lean_Expr_appFn_x21___closed__3;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_List_foldl___at_Lean_mkConst___spec__1(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_instantiateLevelParams___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_getAppArgs___closed__1;
static lean_object* l_Lean_mkNatLit___closed__2;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__4;
uint8_t l_Lean_Level_hasParam(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1666_(lean_object*, lean_object*);
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__45;
LEAN_EXPORT uint8_t l_Lean_instDecidableLtLiteralInstLTLiteral(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateApp_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateForall_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__40;
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_Expr_fvarId_x21___closed__2;
uint8_t lean_expr_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_sortLevel_x21___closed__3;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__8;
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_letName_x21___closed__1;
static lean_object* l_Lean_Expr_projExpr_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object*);
static lean_object* l_Lean_Expr_projExpr_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object*);
static lean_object* l_Lean_Expr_updateForall_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_updateForall_x21(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_hash___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__17;
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
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__12;
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLiteral;
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__36;
static lean_object* l_Lean_Expr_setPPExplicit___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprFVarId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object*);
static lean_object* l_Lean_Expr_updateLambdaE_x21___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__34;
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object*);
static lean_object* l_Lean_mkOr___closed__1;
static lean_object* l_Lean_instReprData__1___lambda__5___closed__1;
uint32_t lean_uint32_add(uint32_t, uint32_t);
static lean_object* l_Lean_Expr_sortLevel_x21___closed__2;
static lean_object* l_Lean_instReprData__1___lambda__4___closed__1;
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_natLit_x3f___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__19;
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object*, lean_object*);
static lean_object* l_Lean_mkOr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_Data_approxDepth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object*, lean_object*);
extern uint64_t l_instInhabitedUInt64;
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at_Lean_Expr_setPPExplicit___spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_beta___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_letFunAnnotation_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__26;
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubstArray(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBTree_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object*);
static lean_object* l_Lean_Expr_bindingName_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__1;
LEAN_EXPORT lean_object* l_Lean_instBEqBinderInfo;
static lean_object* l_Lean_Expr_updateSort_x21___closed__3;
LEAN_EXPORT uint64_t l_Lean_BinderInfo_toUInt64(uint8_t);
static lean_object* l_Lean_Expr_letName_x21___closed__3;
static lean_object* l_Lean_mkEM___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambda_x21(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107_(lean_object*, lean_object*);
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
static lean_object* l_Lean_instReprData__1___lambda__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateSort_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object*, uint8_t);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__35;
static lean_object* l_Lean_Expr_constName_x21___closed__3;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__2;
static lean_object* l_Lean_Literal_type___closed__6;
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateConst_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__5(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__6(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_31____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFVarIdSetInhabited;
static lean_object* l_Lean_Expr_sortLevel_x21___closed__1;
LEAN_EXPORT uint8_t lean_expr_has_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object*);
static lean_object* l_Lean_mkNatLit___closed__6;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__19;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__9;
static lean_object* l_Lean_Expr_ctorName___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_BinderInfo_noConfusion___rarg___closed__1;
static lean_object* l_Lean_Expr_bindingBody_x21___closed__2;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__27;
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_panic___at_Lean_Level_normalize___spec__1(lean_object*);
static lean_object* l_Lean_isLHSGoal_x3f___closed__1;
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object*);
static lean_object* l_Lean_Expr_mkData___closed__2;
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_letFunAnnotation_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isStrictImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint64_to_uint32(uint64_t);
lean_object* l_Lean_mkFreshId___rarg(lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLiteral;
static lean_object* l_Lean_Expr_instToStringExpr___closed__1;
LEAN_EXPORT uint64_t l_Lean_Expr_data(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__17;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__4(uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubstArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateProj_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkDecIsTrue___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicitForExposingMVars___spec__1(size_t, size_t, lean_object*);
uint64_t l_Lean_Name_hash(lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasFVar(uint64_t);
static lean_object* l_Lean_Expr_instBEqExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVarEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object*);
static lean_object* l_Lean_Expr_fvarId_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object*);
static lean_object* l_Lean_Expr_updateConst_x21___closed__2;
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instHashableExpr;
static lean_object* l_Lean_mkDecIsTrue___closed__2;
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_mvarId_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object*);
static lean_object* l_Lean_Literal_type___closed__1;
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_constLevels_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_bindingDomain_x21___closed__1;
lean_object* l_panic___at_String_toNat_x21___spec__1(lean_object*);
static lean_object* l_Lean_mkInaccessible___closed__2;
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object*);
static lean_object* l_Lean_Expr_getRevArg_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ctorName___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprExpr;
static lean_object* l_Lean_isLHSGoal_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_natLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__6;
static lean_object* l_Lean_Expr_isCharLit___closed__3;
static lean_object* l_Lean_mkEM___closed__5;
static lean_object* l_Lean_mkOr___closed__2;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__31;
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
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet(uint64_t, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
static lean_object* l_Lean_mkSimpleThunk___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instReprData__1___lambda__7___closed__1;
static lean_object* l_Lean_Expr_updateProj_x21___closed__3;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__2(uint64_t, lean_object*, lean_object*);
static lean_object* l_Lean_Literal_type___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_482_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_31_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLetFun___boxed(lean_object*);
static lean_object* l_Lean_mkSimpleThunk___closed__1;
lean_object* l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(lean_object*);
static lean_object* l_Lean_Expr_appFn_x21___closed__1;
static lean_object* l_Lean_Expr_updateApp_x21___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__21;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__13;
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_fvarId_x21___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isLetFun(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqData__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isAuxDecl(uint8_t);
static lean_object* l_Lean_Expr_bindingName_x21___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__23;
LEAN_EXPORT uint8_t l_Lean_Expr_Data_nonDepLet(uint64_t);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__39;
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint64_t lean_uint64_land(uint64_t, uint64_t);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__16;
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_constName_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__4(lean_object*, uint64_t, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object*, lean_object*);
uint8_t lean_expr_quick_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object*);
static lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__1;
LEAN_EXPORT uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object*);
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
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__43;
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_mkData___spec__1___boxed__const__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__22;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__28;
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_betaRevAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ctorName___closed__9;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkNatLit___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_bindingInfo_x21___spec__1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedBinderInfo;
static lean_object* l_Lean_Expr_updateLambda_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_instBEqFVarId;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarId;
static lean_object* l_Lean_Expr_updateProj_x21___closed__1;
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object*);
lean_object* lean_level_update_imax(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__18;
static lean_object* l_Lean_mkNatLit___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object*);
static lean_object* l_Lean_Expr_updateLambda_x21___closed__2;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__30;
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__7(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_mkData___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateMData___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__5;
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVarEx___boxed(lean_object*);
static lean_object* l_Lean_instHashableBinderInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_eta(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
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
uint8_t lean_uint64_to_uint8(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__3;
static lean_object* l_Lean_Expr_setPPExplicit___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object*);
static lean_object* l_Lean_Expr_constLevels_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgsAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Literal_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__29;
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_instInhabitedData__1;
static lean_object* l_Lean_instBEqLiteral___closed__1;
LEAN_EXPORT lean_object* l_Lean_instHashableBinderInfo;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object*);
extern lean_object* l_Lean_KVMap_empty;
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__5(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_instantiateLevelParamsArray___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
static lean_object* l_Lean_Expr_updateMData_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion(lean_object*);
static lean_object* l_Lean_Expr_bvarIdx_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isStrictImplicit___boxed(lean_object*);
static lean_object* l_Lean_mkNatLit___closed__10;
static lean_object* l_Lean_mkAnd___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__24;
lean_object* l___private_Lean_Data_KVMap_0__Lean_reprKVMap____x40_Lean_Data_KVMap___hyg_844_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubst(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedExpr___closed__2;
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object*);
static uint64_t l_Lean_instInhabitedExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Literal_lt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_insertCore(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_appArg_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambda_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_projIdx_x21___closed__1;
static lean_object* l_Lean_Expr_appFn_x21___closed__2;
static lean_object* l_Lean_mkNatLit___closed__5;
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__7;
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__10;
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__24;
static lean_object* l_Lean_Expr_bvarIdx_x21___closed__2;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__32;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__7;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_appArg_x21___closed__1;
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__20;
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_807_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instToStringExpr;
static lean_object* l_Lean_mkEM___closed__4;
uint64_t lean_uint32_to_uint64(uint32_t);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__6(lean_object*, uint64_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__30;
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instToStringExprStructEq___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkSimpleThunkType___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicit___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isAuxDecl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_mkConst___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_instantiateLevelParamsArray___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l_Lean_Expr_setPPUniverses___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instReprData__1___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__25;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__15;
static lean_object* l_Lean_Expr_updateLet_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____spec__1(lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__18;
static lean_object* l_Lean_Expr_mkData___closed__4;
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_hash___boxed(lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
static lean_object* l_Lean_instReprData__1___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object*);
static lean_object* l_Lean_instHashableLiteral___closed__1;
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_litValue_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__3(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_letType_x21___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicitForExposingMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFVarIdHashSetInhabited;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__3;
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_instForInFVarIdSetFVarId___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1719____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__25;
LEAN_EXPORT lean_object* l_Lean_Expr_updateProj___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_letType_x21___closed__2;
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT uint64_t lean_expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFVarIdHashSetEmptyCollection;
static lean_object* l_Lean_instReprLiteral___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__2___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_356_(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Expr_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableFVarId;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_356____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isOptParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableLiteral;
LEAN_EXPORT uint8_t l_Lean_Expr_isAtomic(lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ctorName___closed__12;
LEAN_EXPORT lean_object* l_Lean_mkApp2(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__15;
static lean_object* l_Lean_instForInFVarIdSetFVarId___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_instBEqExpr;
LEAN_EXPORT lean_object* l_Lean_instInhabitedExprStructEq;
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_mkConst___spec__3(uint8_t, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__8;
static lean_object* l_Lean_Expr_ctorName___closed__6;
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object*, lean_object*);
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__28;
static lean_object* l_Lean_instBEqFVarId___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqData__1(uint64_t, uint64_t);
lean_object* lean_string_length(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__37;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkAppN___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instToStringExprStructEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isExplicit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instDecidableLtLiteralInstLTLiteral___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_mkData___closed__1;
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_mkConst___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__14;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__20;
static lean_object* l_Lean_mkDecIsFalse___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object*);
static lean_object* l_Lean_Expr_updateLet_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at_Lean_Expr_setPPExplicit___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_nonDepLet___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Level_instantiateParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__21;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__38;
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__7;
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ctorName___closed__11;
static lean_object* l_Lean_mkNot___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1666____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicit___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__33;
static lean_object* l_Lean_Expr_letValue_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_instReprData__1(uint64_t, lean_object*);
static lean_object* l_Lean_mkLHSGoal___closed__1;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_lit_type(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__44;
LEAN_EXPORT lean_object* l_Lean_instBEqLiteral;
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkLetFunAnnotation___closed__2;
static lean_object* l_Lean_instBEqBinderInfo___closed__1;
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_isCharLit___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_BinderInfo_hash(uint8_t);
static lean_object* l_Lean_Expr_setPPUniverses___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_approxDepth(uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_mdataExpr_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkNot___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__3;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__47;
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__2(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateLet_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Literal_lt(lean_object*, lean_object*);
static lean_object* l_Lean_mkLetFunAnnotation___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_updateForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__23;
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object*);
static lean_object* l_Lean_mkNot___closed__2;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object*);
static lean_object* l_Lean_Expr_updateForallE_x21___closed__2;
lean_object* lean_expr_instantiate_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_fvarId_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instReprData__1___closed__2;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Expr_getRevArg_x21___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__10;
static lean_object* l_Lean_Expr_updateForallE_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instFVarIdHashSetInhabited___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit(lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Level_mvarId_x21___spec__1(lean_object*);
static lean_object* l_Lean_Expr_updateSort_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object*);
static lean_object* l_Lean_Expr_mdataExpr_x21___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__46;
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isNatLit___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__29;
lean_object* l_List_mapTRAux___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__2;
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_mkConst___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__16;
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__6;
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__1;
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object*);
static lean_object* l_Lean_Expr_bindingInfo_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
static lean_object* l_Lean_Expr_isCharLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__22;
LEAN_EXPORT uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
static lean_object* l_Lean_mkAnnotation___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_mkData(uint64_t, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_31_(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_31____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_31_(x_1, x_2);
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
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_31____boxed), 2, 0);
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
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Literal.natVal");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__2;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Literal.strVal");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__7;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107_(lean_object* x_1, lean_object* x_2) {
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
x_8 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__3;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
if (x_5 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
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
x_15 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
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
x_25 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__8;
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
if (x_22 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
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
x_32 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprLiteral___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____boxed), 2, 0);
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
LEAN_EXPORT uint8_t l_Lean_instDecidableLtLiteralInstLTLiteral(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Literal_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instDecidableLtLiteralInstLTLiteral___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_instDecidableLtLiteralInstLTLiteral(x_1, x_2);
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
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_356_(uint8_t x_1, uint8_t x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_356____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_356_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instBEqBinderInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_356____boxed), 2, 0);
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
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.BinderInfo.default");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__2;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__2;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__5;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.BinderInfo.implicit");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__8;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__10() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__9;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__8;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.BinderInfo.strictImplicit");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__14;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__16() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__15;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__14;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__18() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__17;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.BinderInfo.instImplicit");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__20;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__22() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__21;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__20;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__24() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__23;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.BinderInfo.auxDecl");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__25;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__26;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__28() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__27;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__26;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__30() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__29;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372_(uint8_t x_1, lean_object* x_2) {
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
x_5 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__4;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__6;
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
x_11 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__10;
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__12;
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
x_17 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__16;
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__18;
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
x_23 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__22;
x_24 = l_Repr_addAppParen(x_23, x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__24;
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
x_29 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__28;
x_30 = l_Repr_addAppParen(x_29, x_2);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__30;
x_32 = l_Repr_addAppParen(x_31, x_2);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_instReprBinderInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____boxed), 2, 0);
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
x_2 = lean_uint64_to_uint32(x_1);
x_3 = lean_uint32_to_uint64(x_2);
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
x_3 = lean_uint64_dec_eq(x_1, x_2);
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
x_3 = lean_uint64_shift_right(x_1, x_2);
x_4 = 255;
x_5 = lean_uint64_land(x_3, x_4);
x_6 = lean_uint64_to_uint8(x_5);
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
x_3 = lean_uint64_shift_right(x_1, x_2);
x_4 = lean_uint64_to_uint32(x_3);
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
x_3 = lean_uint64_shift_right(x_1, x_2);
x_4 = 1;
x_5 = lean_uint64_land(x_3, x_4);
x_6 = lean_uint64_dec_eq(x_5, x_4);
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
x_3 = lean_uint64_shift_right(x_1, x_2);
x_4 = 1;
x_5 = lean_uint64_land(x_3, x_4);
x_6 = lean_uint64_dec_eq(x_5, x_4);
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
x_3 = lean_uint64_shift_right(x_1, x_2);
x_4 = 1;
x_5 = lean_uint64_land(x_3, x_4);
x_6 = lean_uint64_dec_eq(x_5, x_4);
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
x_3 = lean_uint64_shift_right(x_1, x_2);
x_4 = 1;
x_5 = lean_uint64_land(x_3, x_4);
x_6 = lean_uint64_dec_eq(x_5, x_4);
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
x_3 = lean_uint64_shift_right(x_1, x_2);
x_4 = 1;
x_5 = lean_uint64_land(x_3, x_4);
x_6 = lean_uint64_dec_eq(x_5, x_4);
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
static lean_object* _init_l_panic___at_Lean_Expr_mkData___spec__1___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedData__1;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_mkData___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at_Lean_Expr_mkData___spec__1___boxed__const__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_mkData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(65536u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_mkData___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_mkData___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.mkData");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_mkData___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bound variable index is too big");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_mkData___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_mkData___closed__3;
x_3 = lean_unsigned_to_nat(136u);
x_4 = lean_unsigned_to_nat(44u);
x_5 = l_Lean_Expr_mkData___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkData(uint64_t x_1, lean_object* x_2, uint32_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8, uint8_t x_9) {
_start:
{
uint8_t x_10; uint32_t x_47; uint8_t x_48; lean_object* x_49; uint8_t x_50; 
x_47 = 255;
x_48 = lean_uint32_dec_lt(x_47, x_3);
x_49 = l_Lean_Expr_mkData___closed__1;
x_50 = lean_nat_dec_lt(x_49, x_2);
if (x_48 == 0)
{
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = lean_uint32_to_uint8(x_3);
x_10 = x_51;
goto block_46;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lean_Expr_mkData___closed__5;
x_53 = l_panic___at_Lean_Expr_mkData___spec__1(x_52);
return x_53;
}
}
else
{
if (x_50 == 0)
{
uint8_t x_54; 
x_54 = 255;
x_10 = x_54;
goto block_46;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Lean_Expr_mkData___closed__5;
x_56 = l_panic___at_Lean_Expr_mkData___spec__1(x_55);
return x_56;
}
}
block_46:
{
uint32_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; lean_object* x_45; 
x_11 = lean_uint64_to_uint32(x_1);
x_12 = lean_uint32_to_uint64(x_11);
x_13 = lean_bool_to_uint64(x_4);
x_14 = 32;
x_15 = lean_uint64_shift_left(x_13, x_14);
x_16 = lean_uint64_add(x_12, x_15);
x_17 = lean_bool_to_uint64(x_5);
x_18 = 33;
x_19 = lean_uint64_shift_left(x_17, x_18);
x_20 = lean_uint64_add(x_16, x_19);
x_21 = lean_bool_to_uint64(x_6);
x_22 = 34;
x_23 = lean_uint64_shift_left(x_21, x_22);
x_24 = lean_uint64_add(x_20, x_23);
x_25 = lean_bool_to_uint64(x_7);
x_26 = 35;
x_27 = lean_uint64_shift_left(x_25, x_26);
x_28 = lean_uint64_add(x_24, x_27);
x_29 = lean_bool_to_uint64(x_9);
x_30 = 36;
x_31 = lean_uint64_shift_left(x_29, x_30);
x_32 = lean_uint64_add(x_28, x_31);
x_33 = (uint64_t)x_8;
x_34 = 37;
x_35 = lean_uint64_shift_left(x_33, x_34);
x_36 = lean_uint64_add(x_32, x_35);
x_37 = lean_uint8_to_uint64(x_10);
x_38 = 40;
x_39 = lean_uint64_shift_left(x_37, x_38);
x_40 = lean_uint64_add(x_36, x_39);
x_41 = lean_uint64_of_nat(x_2);
x_42 = 48;
x_43 = lean_uint64_shift_left(x_41, x_42);
x_44 = lean_uint64_add(x_40, x_43);
x_45 = lean_box_uint64(x_44);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint64_t x_10; uint32_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_10 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_11 = lean_unbox_uint32(x_3);
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
x_18 = l_Lean_Expr_mkData(x_10, x_2, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder(uint64_t x_1, lean_object* x_2, uint32_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = l_Lean_Expr_mkData(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint64_t x_9; uint32_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_9 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_10 = lean_unbox_uint32(x_3);
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
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet(uint64_t x_1, lean_object* x_2, uint32_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = l_Lean_Expr_mkData(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint64_t x_9; uint32_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_9 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_10 = lean_unbox_uint32(x_3);
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
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Repr_addAppParen(x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_instReprData__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (bi := ");
return x_1;
}
}
static lean_object* _init_l_Lean_instReprData__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__2(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; 
x_5 = (uint8_t)((x_2 << 24) >> 61);
x_6 = 0;
x_7 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_356_(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Lean_instReprData__1___lambda__1(x_1, x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = l_Lean_instReprData__1___lambda__2___closed__1;
x_11 = lean_string_append(x_3, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372_(x_5, x_12);
x_14 = l_Std_Format_defWidth;
x_15 = lean_format_pretty(x_13, x_14);
x_16 = lean_string_append(x_11, x_15);
lean_dec(x_15);
x_17 = l_Lean_instReprData__1___lambda__2___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_box(0);
x_20 = l_Lean_instReprData__1___lambda__1(x_1, x_18, x_19);
return x_20;
}
}
}
static lean_object* _init_l_Lean_instReprData__1___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (nonDepLet := ");
return x_1;
}
}
static lean_object* _init_l_Lean_instReprData__1___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("true");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__3(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = l_Lean_Expr_Data_nonDepLet(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_instReprData__1___lambda__2(x_1, x_2, x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_instReprData__1___lambda__3___closed__1;
x_9 = lean_string_append(x_3, x_8);
x_10 = l_Lean_instReprData__1___lambda__3___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_instReprData__1___lambda__2___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_instReprData__1___lambda__2(x_1, x_2, x_13, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lean_instReprData__1___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (hasLevelMVar := ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__4(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = l_Lean_Expr_Data_hasLevelMVar(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_instReprData__1___lambda__3(x_1, x_2, x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_instReprData__1___lambda__4___closed__1;
x_9 = lean_string_append(x_3, x_8);
x_10 = l_Lean_instReprData__1___lambda__3___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_instReprData__1___lambda__2___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_instReprData__1___lambda__3(x_1, x_2, x_13, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lean_instReprData__1___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (hasExprMVar := ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__5(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = l_Lean_Expr_Data_hasExprMVar(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_instReprData__1___lambda__4(x_1, x_2, x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_instReprData__1___lambda__5___closed__1;
x_9 = lean_string_append(x_3, x_8);
x_10 = l_Lean_instReprData__1___lambda__3___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_instReprData__1___lambda__2___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_instReprData__1___lambda__4(x_1, x_2, x_13, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lean_instReprData__1___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (hasFVar := ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__6(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = l_Lean_Expr_Data_hasFVar(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_instReprData__1___lambda__5(x_1, x_2, x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_instReprData__1___lambda__6___closed__1;
x_9 = lean_string_append(x_3, x_8);
x_10 = l_Lean_instReprData__1___lambda__3___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_Lean_instReprData__1___lambda__2___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_instReprData__1___lambda__5(x_1, x_2, x_13, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lean_instReprData__1___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (approxDepth := ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__7(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; 
lean_dec(x_4);
x_5 = l_Lean_Expr_Data_approxDepth(x_2);
x_6 = 0;
x_7 = lean_uint8_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = l_Lean_instReprData__1___lambda__7___closed__1;
x_9 = lean_string_append(x_3, x_8);
x_10 = lean_uint8_to_nat(x_5);
x_11 = l_Nat_repr(x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec(x_11);
x_13 = l_Lean_instReprData__1___lambda__2___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_box(0);
x_16 = l_Lean_instReprData__1___lambda__6(x_1, x_2, x_14, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_instReprData__1___lambda__6(x_1, x_2, x_3, x_17);
return x_18;
}
}
}
static lean_object* _init_l_Lean_instReprData__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Expr.mkData ");
return x_1;
}
}
static lean_object* _init_l_Lean_instReprData__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (looseBVarRange := ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1(uint64_t x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_3 = l_Lean_Expr_Data_hash(x_1);
x_4 = lean_uint64_to_nat(x_3);
x_5 = l_Nat_repr(x_4);
x_6 = l_Lean_instReprData__1___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_Expr_Data_looseBVarRange(x_1);
x_9 = 0;
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = l_Lean_instReprData__1___closed__2;
x_12 = lean_string_append(x_7, x_11);
x_13 = lean_uint32_to_nat(x_8);
x_14 = l_Nat_repr(x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec(x_14);
x_16 = l_Lean_instReprData__1___lambda__2___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_box(0);
x_19 = l_Lean_instReprData__1___lambda__7(x_2, x_1, x_17, x_18);
lean_dec(x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_instReprData__1___lambda__7(x_2, x_1, x_7, x_20);
lean_dec(x_2);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instReprData__1___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Lean_instReprData__1___lambda__2(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Lean_instReprData__1___lambda__3(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Lean_instReprData__1___lambda__4(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Lean_instReprData__1___lambda__5(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Lean_instReprData__1___lambda__6(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; lean_object* x_6; 
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Lean_instReprData__1___lambda__7(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lean_instReprData__1(x_3, x_2);
return x_4;
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
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1666_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1666____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1666_(x_1, x_2);
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
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1666____boxed), 2, 0);
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
LEAN_EXPORT uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1719_(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; 
x_2 = 0;
x_3 = l_Lean_Name_hash(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1719____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1719_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableFVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1719____boxed), 1, 0);
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
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_807_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_807_(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_807_(x_8, x_9);
lean_inc(x_2);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
x_12 = l_Std_Format_joinSep___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____spec__2(x_4, x_2);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unsigned_to_nat(1024u);
x_5 = l_Repr_addAppParen(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__2(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; 
x_4 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__2___closed__1;
x_5 = (uint8_t)((x_1 << 24) >> 61);
x_6 = 0;
x_7 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_356_(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_apply_2(x_4, x_2, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = l_Lean_instReprData__1___lambda__2___closed__1;
x_11 = lean_string_append(x_2, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372_(x_5, x_12);
x_14 = l_Std_Format_defWidth;
x_15 = lean_format_pretty(x_13, x_14);
x_16 = lean_string_append(x_11, x_15);
lean_dec(x_15);
x_17 = l_Lean_instReprData__1___lambda__2___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_4, x_18, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__3(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_dec(x_3);
x_4 = l_Lean_Expr_Data_nonDepLet(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__2(x_1, x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_instReprData__1___lambda__3___closed__1;
x_8 = lean_string_append(x_2, x_7);
x_9 = l_Lean_instReprData__1___lambda__3___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Lean_instReprData__1___lambda__2___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_box(0);
x_14 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__2(x_1, x_12, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__4(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_dec(x_3);
x_4 = l_Lean_Expr_Data_hasLevelMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__3(x_1, x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_instReprData__1___lambda__4___closed__1;
x_8 = lean_string_append(x_2, x_7);
x_9 = l_Lean_instReprData__1___lambda__3___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Lean_instReprData__1___lambda__2___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_box(0);
x_14 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__3(x_1, x_12, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__5(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_dec(x_3);
x_4 = l_Lean_Expr_Data_hasExprMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__4(x_1, x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_instReprData__1___lambda__5___closed__1;
x_8 = lean_string_append(x_2, x_7);
x_9 = l_Lean_instReprData__1___lambda__3___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Lean_instReprData__1___lambda__2___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_box(0);
x_14 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__4(x_1, x_12, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__6(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_dec(x_3);
x_4 = l_Lean_Expr_Data_hasFVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__5(x_1, x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_instReprData__1___lambda__6___closed__1;
x_8 = lean_string_append(x_2, x_7);
x_9 = l_Lean_instReprData__1___lambda__3___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Lean_instReprData__1___lambda__2___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_box(0);
x_14 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__5(x_1, x_12, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(uint64_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; 
lean_dec(x_3);
x_4 = l_Lean_Expr_Data_approxDepth(x_1);
x_5 = 0;
x_6 = lean_uint8_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l_Lean_instReprData__1___lambda__7___closed__1;
x_8 = lean_string_append(x_2, x_7);
x_9 = lean_uint8_to_nat(x_4);
x_10 = l_Nat_repr(x_9);
x_11 = lean_string_append(x_8, x_10);
lean_dec(x_10);
x_12 = l_Lean_instReprData__1___lambda__2___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_box(0);
x_15 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__6(x_1, x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__6(x_1, x_2, x_16);
return x_17;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.bvar");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__2;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.fvar");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__5;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.mvar");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__8;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.sort");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__11;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.const");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__14;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(",");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__17;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__19;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__20;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__23;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[]");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__25;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.app");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__27;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__28;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.lam");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__30;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__31;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.forallE");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__33;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__34;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.letE");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__36;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__37;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.lit");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__39;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__40;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.mdata");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__42;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__43;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.proj");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__45;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__46;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; uint64_t x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint32_t x_18; uint32_t x_19; uint8_t x_20; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_5 = lean_unsigned_to_nat(1024u);
x_6 = lean_nat_dec_le(x_5, x_2);
x_7 = l_Nat_repr(x_3);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__3;
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_box(1);
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Expr_Data_hash(x_4);
x_14 = lean_uint64_to_nat(x_13);
x_15 = l_Nat_repr(x_14);
x_16 = l_Lean_instReprData__1___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_Expr_Data_looseBVarRange(x_4);
x_19 = 0;
x_20 = lean_uint32_dec_eq(x_18, x_19);
if (x_6 == 0)
{
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_21 = l_Lean_instReprData__1___closed__2;
x_22 = lean_string_append(x_17, x_21);
x_23 = lean_uint32_to_nat(x_18);
x_24 = l_Nat_repr(x_23);
x_25 = lean_string_append(x_22, x_24);
lean_dec(x_24);
x_26 = l_Lean_instReprData__1___lambda__2___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_box(0);
x_29 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_4, x_27, x_28);
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_32 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = 0;
x_34 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = l_Repr_addAppParen(x_34, x_2);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_box(0);
x_37 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_4, x_17, x_36);
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_12);
lean_ctor_set(x_38, 1, x_37);
x_39 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_40 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = 0;
x_42 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = l_Repr_addAppParen(x_42, x_2);
return x_43;
}
}
else
{
if (x_20 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_44 = l_Lean_instReprData__1___closed__2;
x_45 = lean_string_append(x_17, x_44);
x_46 = lean_uint32_to_nat(x_18);
x_47 = l_Nat_repr(x_46);
x_48 = lean_string_append(x_45, x_47);
lean_dec(x_47);
x_49 = l_Lean_instReprData__1___lambda__2___closed__2;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_box(0);
x_52 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_4, x_50, x_51);
x_53 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_53, 0, x_12);
lean_ctor_set(x_53, 1, x_52);
x_54 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_55 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = 0;
x_57 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_56);
x_58 = l_Repr_addAppParen(x_57, x_2);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_box(0);
x_60 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_4, x_17, x_59);
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_12);
lean_ctor_set(x_61, 1, x_60);
x_62 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_63 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = 0;
x_65 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = l_Repr_addAppParen(x_65, x_2);
return x_66;
}
}
}
case 1:
{
lean_object* x_67; uint64_t x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint32_t x_81; uint32_t x_82; uint8_t x_83; 
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
x_68 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_69 = lean_unsigned_to_nat(1024u);
x_70 = lean_nat_dec_le(x_69, x_2);
x_71 = l_Lean_Name_reprPrec(x_67, x_69);
x_72 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__6;
x_73 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_box(1);
x_75 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_Expr_Data_hash(x_68);
x_77 = lean_uint64_to_nat(x_76);
x_78 = l_Nat_repr(x_77);
x_79 = l_Lean_instReprData__1___closed__1;
x_80 = lean_string_append(x_79, x_78);
lean_dec(x_78);
x_81 = l_Lean_Expr_Data_looseBVarRange(x_68);
x_82 = 0;
x_83 = lean_uint32_dec_eq(x_81, x_82);
if (x_70 == 0)
{
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_84 = l_Lean_instReprData__1___closed__2;
x_85 = lean_string_append(x_80, x_84);
x_86 = lean_uint32_to_nat(x_81);
x_87 = l_Nat_repr(x_86);
x_88 = lean_string_append(x_85, x_87);
lean_dec(x_87);
x_89 = l_Lean_instReprData__1___lambda__2___closed__2;
x_90 = lean_string_append(x_88, x_89);
x_91 = lean_box(0);
x_92 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_68, x_90, x_91);
x_93 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_93, 0, x_75);
lean_ctor_set(x_93, 1, x_92);
x_94 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_95 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = 0;
x_97 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
x_98 = l_Repr_addAppParen(x_97, x_2);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; 
x_99 = lean_box(0);
x_100 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_68, x_80, x_99);
x_101 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_101, 0, x_75);
lean_ctor_set(x_101, 1, x_100);
x_102 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_103 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = 0;
x_105 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_104);
x_106 = l_Repr_addAppParen(x_105, x_2);
return x_106;
}
}
else
{
if (x_83 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; 
x_107 = l_Lean_instReprData__1___closed__2;
x_108 = lean_string_append(x_80, x_107);
x_109 = lean_uint32_to_nat(x_81);
x_110 = l_Nat_repr(x_109);
x_111 = lean_string_append(x_108, x_110);
lean_dec(x_110);
x_112 = l_Lean_instReprData__1___lambda__2___closed__2;
x_113 = lean_string_append(x_111, x_112);
x_114 = lean_box(0);
x_115 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_68, x_113, x_114);
x_116 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_116, 0, x_75);
lean_ctor_set(x_116, 1, x_115);
x_117 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_118 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = 0;
x_120 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set_uint8(x_120, sizeof(void*)*1, x_119);
x_121 = l_Repr_addAppParen(x_120, x_2);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; 
x_122 = lean_box(0);
x_123 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_68, x_80, x_122);
x_124 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_124, 0, x_75);
lean_ctor_set(x_124, 1, x_123);
x_125 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_126 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = 0;
x_128 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set_uint8(x_128, sizeof(void*)*1, x_127);
x_129 = l_Repr_addAppParen(x_128, x_2);
return x_129;
}
}
}
case 2:
{
lean_object* x_130; uint64_t x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint64_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint32_t x_144; uint32_t x_145; uint8_t x_146; 
x_130 = lean_ctor_get(x_1, 0);
lean_inc(x_130);
x_131 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_132 = lean_unsigned_to_nat(1024u);
x_133 = lean_nat_dec_le(x_132, x_2);
x_134 = l_Lean_Name_reprPrec(x_130, x_132);
x_135 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__9;
x_136 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
x_137 = lean_box(1);
x_138 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_Expr_Data_hash(x_131);
x_140 = lean_uint64_to_nat(x_139);
x_141 = l_Nat_repr(x_140);
x_142 = l_Lean_instReprData__1___closed__1;
x_143 = lean_string_append(x_142, x_141);
lean_dec(x_141);
x_144 = l_Lean_Expr_Data_looseBVarRange(x_131);
x_145 = 0;
x_146 = lean_uint32_dec_eq(x_144, x_145);
if (x_133 == 0)
{
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; 
x_147 = l_Lean_instReprData__1___closed__2;
x_148 = lean_string_append(x_143, x_147);
x_149 = lean_uint32_to_nat(x_144);
x_150 = l_Nat_repr(x_149);
x_151 = lean_string_append(x_148, x_150);
lean_dec(x_150);
x_152 = l_Lean_instReprData__1___lambda__2___closed__2;
x_153 = lean_string_append(x_151, x_152);
x_154 = lean_box(0);
x_155 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_131, x_153, x_154);
x_156 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_156, 0, x_138);
lean_ctor_set(x_156, 1, x_155);
x_157 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_158 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
x_159 = 0;
x_160 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set_uint8(x_160, sizeof(void*)*1, x_159);
x_161 = l_Repr_addAppParen(x_160, x_2);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; 
x_162 = lean_box(0);
x_163 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_131, x_143, x_162);
x_164 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_164, 0, x_138);
lean_ctor_set(x_164, 1, x_163);
x_165 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_166 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = 0;
x_168 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set_uint8(x_168, sizeof(void*)*1, x_167);
x_169 = l_Repr_addAppParen(x_168, x_2);
return x_169;
}
}
else
{
if (x_146 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; 
x_170 = l_Lean_instReprData__1___closed__2;
x_171 = lean_string_append(x_143, x_170);
x_172 = lean_uint32_to_nat(x_144);
x_173 = l_Nat_repr(x_172);
x_174 = lean_string_append(x_171, x_173);
lean_dec(x_173);
x_175 = l_Lean_instReprData__1___lambda__2___closed__2;
x_176 = lean_string_append(x_174, x_175);
x_177 = lean_box(0);
x_178 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_131, x_176, x_177);
x_179 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_179, 0, x_138);
lean_ctor_set(x_179, 1, x_178);
x_180 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_181 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
x_182 = 0;
x_183 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set_uint8(x_183, sizeof(void*)*1, x_182);
x_184 = l_Repr_addAppParen(x_183, x_2);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; 
x_185 = lean_box(0);
x_186 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_131, x_143, x_185);
x_187 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_187, 0, x_138);
lean_ctor_set(x_187, 1, x_186);
x_188 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_189 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_187);
x_190 = 0;
x_191 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set_uint8(x_191, sizeof(void*)*1, x_190);
x_192 = l_Repr_addAppParen(x_191, x_2);
return x_192;
}
}
}
case 3:
{
lean_object* x_193; uint64_t x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint64_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint32_t x_207; uint32_t x_208; uint8_t x_209; 
x_193 = lean_ctor_get(x_1, 0);
lean_inc(x_193);
x_194 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_195 = lean_unsigned_to_nat(1024u);
x_196 = lean_nat_dec_le(x_195, x_2);
x_197 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_807_(x_193, x_195);
x_198 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__12;
x_199 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = lean_box(1);
x_201 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Lean_Expr_Data_hash(x_194);
x_203 = lean_uint64_to_nat(x_202);
x_204 = l_Nat_repr(x_203);
x_205 = l_Lean_instReprData__1___closed__1;
x_206 = lean_string_append(x_205, x_204);
lean_dec(x_204);
x_207 = l_Lean_Expr_Data_looseBVarRange(x_194);
x_208 = 0;
x_209 = lean_uint32_dec_eq(x_207, x_208);
if (x_196 == 0)
{
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; 
x_210 = l_Lean_instReprData__1___closed__2;
x_211 = lean_string_append(x_206, x_210);
x_212 = lean_uint32_to_nat(x_207);
x_213 = l_Nat_repr(x_212);
x_214 = lean_string_append(x_211, x_213);
lean_dec(x_213);
x_215 = l_Lean_instReprData__1___lambda__2___closed__2;
x_216 = lean_string_append(x_214, x_215);
x_217 = lean_box(0);
x_218 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_194, x_216, x_217);
x_219 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_219, 0, x_201);
lean_ctor_set(x_219, 1, x_218);
x_220 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_221 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
x_222 = 0;
x_223 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set_uint8(x_223, sizeof(void*)*1, x_222);
x_224 = l_Repr_addAppParen(x_223, x_2);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; 
x_225 = lean_box(0);
x_226 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_194, x_206, x_225);
x_227 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_227, 0, x_201);
lean_ctor_set(x_227, 1, x_226);
x_228 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_229 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
x_230 = 0;
x_231 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set_uint8(x_231, sizeof(void*)*1, x_230);
x_232 = l_Repr_addAppParen(x_231, x_2);
return x_232;
}
}
else
{
if (x_209 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; 
x_233 = l_Lean_instReprData__1___closed__2;
x_234 = lean_string_append(x_206, x_233);
x_235 = lean_uint32_to_nat(x_207);
x_236 = l_Nat_repr(x_235);
x_237 = lean_string_append(x_234, x_236);
lean_dec(x_236);
x_238 = l_Lean_instReprData__1___lambda__2___closed__2;
x_239 = lean_string_append(x_237, x_238);
x_240 = lean_box(0);
x_241 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_194, x_239, x_240);
x_242 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_242, 0, x_201);
lean_ctor_set(x_242, 1, x_241);
x_243 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_244 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_242);
x_245 = 0;
x_246 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set_uint8(x_246, sizeof(void*)*1, x_245);
x_247 = l_Repr_addAppParen(x_246, x_2);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; 
x_248 = lean_box(0);
x_249 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_194, x_206, x_248);
x_250 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_250, 0, x_201);
lean_ctor_set(x_250, 1, x_249);
x_251 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_252 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_250);
x_253 = 0;
x_254 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set_uint8(x_254, sizeof(void*)*1, x_253);
x_255 = l_Repr_addAppParen(x_254, x_2);
return x_255;
}
}
}
case 4:
{
lean_object* x_256; lean_object* x_257; uint64_t x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint64_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint32_t x_271; uint32_t x_272; uint8_t x_273; lean_object* x_274; 
x_256 = lean_ctor_get(x_1, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_1, 1);
lean_inc(x_257);
x_258 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_259 = lean_unsigned_to_nat(1024u);
x_260 = lean_nat_dec_le(x_259, x_2);
x_261 = l_Lean_Name_reprPrec(x_256, x_259);
x_262 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__15;
x_263 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_261);
x_264 = lean_box(1);
x_265 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
x_266 = l_Lean_Expr_Data_hash(x_258);
x_267 = lean_uint64_to_nat(x_266);
x_268 = l_Nat_repr(x_267);
x_269 = l_Lean_instReprData__1___closed__1;
x_270 = lean_string_append(x_269, x_268);
lean_dec(x_268);
x_271 = l_Lean_Expr_Data_looseBVarRange(x_258);
x_272 = 0;
x_273 = lean_uint32_dec_eq(x_271, x_272);
if (x_260 == 0)
{
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__26;
x_308 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_308, 0, x_265);
lean_ctor_set(x_308, 1, x_307);
x_309 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_264);
if (x_273 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; lean_object* x_324; 
x_310 = l_Lean_instReprData__1___closed__2;
x_311 = lean_string_append(x_270, x_310);
x_312 = lean_uint32_to_nat(x_271);
x_313 = l_Nat_repr(x_312);
x_314 = lean_string_append(x_311, x_313);
lean_dec(x_313);
x_315 = l_Lean_instReprData__1___lambda__2___closed__2;
x_316 = lean_string_append(x_314, x_315);
x_317 = lean_box(0);
x_318 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_258, x_316, x_317);
x_319 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_319, 0, x_309);
lean_ctor_set(x_319, 1, x_318);
x_320 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_321 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_319);
x_322 = 0;
x_323 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set_uint8(x_323, sizeof(void*)*1, x_322);
x_324 = l_Repr_addAppParen(x_323, x_2);
return x_324;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; lean_object* x_331; lean_object* x_332; 
x_325 = lean_box(0);
x_326 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_258, x_270, x_325);
x_327 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_327, 0, x_309);
lean_ctor_set(x_327, 1, x_326);
x_328 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_329 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_327);
x_330 = 0;
x_331 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set_uint8(x_331, sizeof(void*)*1, x_330);
x_332 = l_Repr_addAppParen(x_331, x_2);
return x_332;
}
}
else
{
lean_object* x_333; 
x_333 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_274 = x_333;
goto block_306;
}
}
else
{
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__26;
x_335 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_335, 0, x_265);
lean_ctor_set(x_335, 1, x_334);
x_336 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_264);
if (x_273 == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; lean_object* x_350; lean_object* x_351; 
x_337 = l_Lean_instReprData__1___closed__2;
x_338 = lean_string_append(x_270, x_337);
x_339 = lean_uint32_to_nat(x_271);
x_340 = l_Nat_repr(x_339);
x_341 = lean_string_append(x_338, x_340);
lean_dec(x_340);
x_342 = l_Lean_instReprData__1___lambda__2___closed__2;
x_343 = lean_string_append(x_341, x_342);
x_344 = lean_box(0);
x_345 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_258, x_343, x_344);
x_346 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_346, 0, x_336);
lean_ctor_set(x_346, 1, x_345);
x_347 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_348 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_346);
x_349 = 0;
x_350 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set_uint8(x_350, sizeof(void*)*1, x_349);
x_351 = l_Repr_addAppParen(x_350, x_2);
return x_351;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; lean_object* x_359; 
x_352 = lean_box(0);
x_353 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_258, x_270, x_352);
x_354 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_354, 0, x_336);
lean_ctor_set(x_354, 1, x_353);
x_355 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_356 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_354);
x_357 = 0;
x_358 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set_uint8(x_358, sizeof(void*)*1, x_357);
x_359 = l_Repr_addAppParen(x_358, x_2);
return x_359;
}
}
else
{
lean_object* x_360; 
x_360 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_274 = x_360;
goto block_306;
}
}
block_306:
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_275 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__18;
x_276 = l_Std_Format_joinSep___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____spec__2(x_257, x_275);
x_277 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__22;
x_278 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_276);
x_279 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__24;
x_280 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
x_281 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__21;
x_282 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_280);
x_283 = 0;
x_284 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set_uint8(x_284, sizeof(void*)*1, x_283);
x_285 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_285, 0, x_265);
lean_ctor_set(x_285, 1, x_284);
x_286 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_264);
if (x_273 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_287 = l_Lean_instReprData__1___closed__2;
x_288 = lean_string_append(x_270, x_287);
x_289 = lean_uint32_to_nat(x_271);
x_290 = l_Nat_repr(x_289);
x_291 = lean_string_append(x_288, x_290);
lean_dec(x_290);
x_292 = l_Lean_instReprData__1___lambda__2___closed__2;
x_293 = lean_string_append(x_291, x_292);
x_294 = lean_box(0);
x_295 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_258, x_293, x_294);
x_296 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_296, 0, x_286);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_297, 0, x_274);
lean_ctor_set(x_297, 1, x_296);
x_298 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set_uint8(x_298, sizeof(void*)*1, x_283);
x_299 = l_Repr_addAppParen(x_298, x_2);
return x_299;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_300 = lean_box(0);
x_301 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_258, x_270, x_300);
x_302 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_302, 0, x_286);
lean_ctor_set(x_302, 1, x_301);
x_303 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_303, 0, x_274);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set_uint8(x_304, sizeof(void*)*1, x_283);
x_305 = l_Repr_addAppParen(x_304, x_2);
return x_305;
}
}
}
case 5:
{
lean_object* x_361; lean_object* x_362; uint64_t x_363; lean_object* x_364; uint8_t x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; uint64_t x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; uint32_t x_379; uint32_t x_380; uint8_t x_381; 
x_361 = lean_ctor_get(x_1, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_1, 1);
lean_inc(x_362);
x_363 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_364 = lean_unsigned_to_nat(1024u);
x_365 = lean_nat_dec_le(x_364, x_2);
x_366 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210_(x_361, x_364);
x_367 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__29;
x_368 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_366);
x_369 = lean_box(1);
x_370 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
x_371 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210_(x_362, x_364);
x_372 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
x_373 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_369);
x_374 = l_Lean_Expr_Data_hash(x_363);
x_375 = lean_uint64_to_nat(x_374);
x_376 = l_Nat_repr(x_375);
x_377 = l_Lean_instReprData__1___closed__1;
x_378 = lean_string_append(x_377, x_376);
lean_dec(x_376);
x_379 = l_Lean_Expr_Data_looseBVarRange(x_363);
x_380 = 0;
x_381 = lean_uint32_dec_eq(x_379, x_380);
if (x_365 == 0)
{
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; 
x_382 = l_Lean_instReprData__1___closed__2;
x_383 = lean_string_append(x_378, x_382);
x_384 = lean_uint32_to_nat(x_379);
x_385 = l_Nat_repr(x_384);
x_386 = lean_string_append(x_383, x_385);
lean_dec(x_385);
x_387 = l_Lean_instReprData__1___lambda__2___closed__2;
x_388 = lean_string_append(x_386, x_387);
x_389 = lean_box(0);
x_390 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_363, x_388, x_389);
x_391 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_391, 0, x_373);
lean_ctor_set(x_391, 1, x_390);
x_392 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_393 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_391);
x_394 = 0;
x_395 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set_uint8(x_395, sizeof(void*)*1, x_394);
x_396 = l_Repr_addAppParen(x_395, x_2);
return x_396;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; 
x_397 = lean_box(0);
x_398 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_363, x_378, x_397);
x_399 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_399, 0, x_373);
lean_ctor_set(x_399, 1, x_398);
x_400 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_401 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_399);
x_402 = 0;
x_403 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set_uint8(x_403, sizeof(void*)*1, x_402);
x_404 = l_Repr_addAppParen(x_403, x_2);
return x_404;
}
}
else
{
if (x_381 == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; 
x_405 = l_Lean_instReprData__1___closed__2;
x_406 = lean_string_append(x_378, x_405);
x_407 = lean_uint32_to_nat(x_379);
x_408 = l_Nat_repr(x_407);
x_409 = lean_string_append(x_406, x_408);
lean_dec(x_408);
x_410 = l_Lean_instReprData__1___lambda__2___closed__2;
x_411 = lean_string_append(x_409, x_410);
x_412 = lean_box(0);
x_413 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_363, x_411, x_412);
x_414 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_414, 0, x_373);
lean_ctor_set(x_414, 1, x_413);
x_415 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_416 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_414);
x_417 = 0;
x_418 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set_uint8(x_418, sizeof(void*)*1, x_417);
x_419 = l_Repr_addAppParen(x_418, x_2);
return x_419;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; lean_object* x_427; 
x_420 = lean_box(0);
x_421 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_363, x_378, x_420);
x_422 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_422, 0, x_373);
lean_ctor_set(x_422, 1, x_421);
x_423 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_424 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_422);
x_425 = 0;
x_426 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set_uint8(x_426, sizeof(void*)*1, x_425);
x_427 = l_Repr_addAppParen(x_426, x_2);
return x_427;
}
}
}
case 6:
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; uint64_t x_431; lean_object* x_432; uint8_t x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; uint64_t x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; uint32_t x_450; uint32_t x_451; uint8_t x_452; 
x_428 = lean_ctor_get(x_1, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_1, 1);
lean_inc(x_429);
x_430 = lean_ctor_get(x_1, 2);
lean_inc(x_430);
x_431 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_432 = lean_unsigned_to_nat(1024u);
x_433 = lean_nat_dec_le(x_432, x_2);
x_434 = l_Lean_Name_reprPrec(x_428, x_432);
x_435 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__32;
x_436 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_434);
x_437 = lean_box(1);
x_438 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_437);
x_439 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210_(x_429, x_432);
x_440 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_440, 0, x_438);
lean_ctor_set(x_440, 1, x_439);
x_441 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_437);
x_442 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210_(x_430, x_432);
x_443 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
x_444 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_437);
x_445 = l_Lean_Expr_Data_hash(x_431);
x_446 = lean_uint64_to_nat(x_445);
x_447 = l_Nat_repr(x_446);
x_448 = l_Lean_instReprData__1___closed__1;
x_449 = lean_string_append(x_448, x_447);
lean_dec(x_447);
x_450 = l_Lean_Expr_Data_looseBVarRange(x_431);
x_451 = 0;
x_452 = lean_uint32_dec_eq(x_450, x_451);
if (x_433 == 0)
{
if (x_452 == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; lean_object* x_467; 
x_453 = l_Lean_instReprData__1___closed__2;
x_454 = lean_string_append(x_449, x_453);
x_455 = lean_uint32_to_nat(x_450);
x_456 = l_Nat_repr(x_455);
x_457 = lean_string_append(x_454, x_456);
lean_dec(x_456);
x_458 = l_Lean_instReprData__1___lambda__2___closed__2;
x_459 = lean_string_append(x_457, x_458);
x_460 = lean_box(0);
x_461 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_431, x_459, x_460);
x_462 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_462, 0, x_444);
lean_ctor_set(x_462, 1, x_461);
x_463 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_464 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_462);
x_465 = 0;
x_466 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set_uint8(x_466, sizeof(void*)*1, x_465);
x_467 = l_Repr_addAppParen(x_466, x_2);
return x_467;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; uint8_t x_473; lean_object* x_474; lean_object* x_475; 
x_468 = lean_box(0);
x_469 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_431, x_449, x_468);
x_470 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_470, 0, x_444);
lean_ctor_set(x_470, 1, x_469);
x_471 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_472 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_470);
x_473 = 0;
x_474 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set_uint8(x_474, sizeof(void*)*1, x_473);
x_475 = l_Repr_addAppParen(x_474, x_2);
return x_475;
}
}
else
{
if (x_452 == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; lean_object* x_490; 
x_476 = l_Lean_instReprData__1___closed__2;
x_477 = lean_string_append(x_449, x_476);
x_478 = lean_uint32_to_nat(x_450);
x_479 = l_Nat_repr(x_478);
x_480 = lean_string_append(x_477, x_479);
lean_dec(x_479);
x_481 = l_Lean_instReprData__1___lambda__2___closed__2;
x_482 = lean_string_append(x_480, x_481);
x_483 = lean_box(0);
x_484 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_431, x_482, x_483);
x_485 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_485, 0, x_444);
lean_ctor_set(x_485, 1, x_484);
x_486 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_487 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_485);
x_488 = 0;
x_489 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set_uint8(x_489, sizeof(void*)*1, x_488);
x_490 = l_Repr_addAppParen(x_489, x_2);
return x_490;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; lean_object* x_497; lean_object* x_498; 
x_491 = lean_box(0);
x_492 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_431, x_449, x_491);
x_493 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_493, 0, x_444);
lean_ctor_set(x_493, 1, x_492);
x_494 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_495 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_493);
x_496 = 0;
x_497 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_497, 0, x_495);
lean_ctor_set_uint8(x_497, sizeof(void*)*1, x_496);
x_498 = l_Repr_addAppParen(x_497, x_2);
return x_498;
}
}
}
case 7:
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; uint64_t x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; uint64_t x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; uint32_t x_521; uint32_t x_522; uint8_t x_523; 
x_499 = lean_ctor_get(x_1, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_1, 1);
lean_inc(x_500);
x_501 = lean_ctor_get(x_1, 2);
lean_inc(x_501);
x_502 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_503 = lean_unsigned_to_nat(1024u);
x_504 = lean_nat_dec_le(x_503, x_2);
x_505 = l_Lean_Name_reprPrec(x_499, x_503);
x_506 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__35;
x_507 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_505);
x_508 = lean_box(1);
x_509 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_509, 0, x_507);
lean_ctor_set(x_509, 1, x_508);
x_510 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210_(x_500, x_503);
x_511 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_511, 0, x_509);
lean_ctor_set(x_511, 1, x_510);
x_512 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_508);
x_513 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210_(x_501, x_503);
x_514 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_514, 0, x_512);
lean_ctor_set(x_514, 1, x_513);
x_515 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_515, 0, x_514);
lean_ctor_set(x_515, 1, x_508);
x_516 = l_Lean_Expr_Data_hash(x_502);
x_517 = lean_uint64_to_nat(x_516);
x_518 = l_Nat_repr(x_517);
x_519 = l_Lean_instReprData__1___closed__1;
x_520 = lean_string_append(x_519, x_518);
lean_dec(x_518);
x_521 = l_Lean_Expr_Data_looseBVarRange(x_502);
x_522 = 0;
x_523 = lean_uint32_dec_eq(x_521, x_522);
if (x_504 == 0)
{
if (x_523 == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; uint8_t x_536; lean_object* x_537; lean_object* x_538; 
x_524 = l_Lean_instReprData__1___closed__2;
x_525 = lean_string_append(x_520, x_524);
x_526 = lean_uint32_to_nat(x_521);
x_527 = l_Nat_repr(x_526);
x_528 = lean_string_append(x_525, x_527);
lean_dec(x_527);
x_529 = l_Lean_instReprData__1___lambda__2___closed__2;
x_530 = lean_string_append(x_528, x_529);
x_531 = lean_box(0);
x_532 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_502, x_530, x_531);
x_533 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_533, 0, x_515);
lean_ctor_set(x_533, 1, x_532);
x_534 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_535 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_535, 0, x_534);
lean_ctor_set(x_535, 1, x_533);
x_536 = 0;
x_537 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_537, 0, x_535);
lean_ctor_set_uint8(x_537, sizeof(void*)*1, x_536);
x_538 = l_Repr_addAppParen(x_537, x_2);
return x_538;
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; uint8_t x_544; lean_object* x_545; lean_object* x_546; 
x_539 = lean_box(0);
x_540 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_502, x_520, x_539);
x_541 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_541, 0, x_515);
lean_ctor_set(x_541, 1, x_540);
x_542 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_543 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_541);
x_544 = 0;
x_545 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_545, 0, x_543);
lean_ctor_set_uint8(x_545, sizeof(void*)*1, x_544);
x_546 = l_Repr_addAppParen(x_545, x_2);
return x_546;
}
}
else
{
if (x_523 == 0)
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; lean_object* x_560; lean_object* x_561; 
x_547 = l_Lean_instReprData__1___closed__2;
x_548 = lean_string_append(x_520, x_547);
x_549 = lean_uint32_to_nat(x_521);
x_550 = l_Nat_repr(x_549);
x_551 = lean_string_append(x_548, x_550);
lean_dec(x_550);
x_552 = l_Lean_instReprData__1___lambda__2___closed__2;
x_553 = lean_string_append(x_551, x_552);
x_554 = lean_box(0);
x_555 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_502, x_553, x_554);
x_556 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_556, 0, x_515);
lean_ctor_set(x_556, 1, x_555);
x_557 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_558 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_558, 0, x_557);
lean_ctor_set(x_558, 1, x_556);
x_559 = 0;
x_560 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_560, 0, x_558);
lean_ctor_set_uint8(x_560, sizeof(void*)*1, x_559);
x_561 = l_Repr_addAppParen(x_560, x_2);
return x_561;
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; uint8_t x_567; lean_object* x_568; lean_object* x_569; 
x_562 = lean_box(0);
x_563 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_502, x_520, x_562);
x_564 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_564, 0, x_515);
lean_ctor_set(x_564, 1, x_563);
x_565 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_566 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_564);
x_567 = 0;
x_568 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_568, 0, x_566);
lean_ctor_set_uint8(x_568, sizeof(void*)*1, x_567);
x_569 = l_Repr_addAppParen(x_568, x_2);
return x_569;
}
}
}
case 8:
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; uint64_t x_574; lean_object* x_575; uint8_t x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; uint64_t x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; uint32_t x_596; uint32_t x_597; uint8_t x_598; 
x_570 = lean_ctor_get(x_1, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_1, 1);
lean_inc(x_571);
x_572 = lean_ctor_get(x_1, 2);
lean_inc(x_572);
x_573 = lean_ctor_get(x_1, 3);
lean_inc(x_573);
x_574 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_575 = lean_unsigned_to_nat(1024u);
x_576 = lean_nat_dec_le(x_575, x_2);
x_577 = l_Lean_Name_reprPrec(x_570, x_575);
x_578 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__38;
x_579 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_579, 0, x_578);
lean_ctor_set(x_579, 1, x_577);
x_580 = lean_box(1);
x_581 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_581, 0, x_579);
lean_ctor_set(x_581, 1, x_580);
x_582 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210_(x_571, x_575);
x_583 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_583, 0, x_581);
lean_ctor_set(x_583, 1, x_582);
x_584 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_584, 0, x_583);
lean_ctor_set(x_584, 1, x_580);
x_585 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210_(x_572, x_575);
x_586 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_586, 0, x_584);
lean_ctor_set(x_586, 1, x_585);
x_587 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_587, 0, x_586);
lean_ctor_set(x_587, 1, x_580);
x_588 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210_(x_573, x_575);
x_589 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_589, 0, x_587);
lean_ctor_set(x_589, 1, x_588);
x_590 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_580);
x_591 = l_Lean_Expr_Data_hash(x_574);
x_592 = lean_uint64_to_nat(x_591);
x_593 = l_Nat_repr(x_592);
x_594 = l_Lean_instReprData__1___closed__1;
x_595 = lean_string_append(x_594, x_593);
lean_dec(x_593);
x_596 = l_Lean_Expr_Data_looseBVarRange(x_574);
x_597 = 0;
x_598 = lean_uint32_dec_eq(x_596, x_597);
if (x_576 == 0)
{
if (x_598 == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; uint8_t x_611; lean_object* x_612; lean_object* x_613; 
x_599 = l_Lean_instReprData__1___closed__2;
x_600 = lean_string_append(x_595, x_599);
x_601 = lean_uint32_to_nat(x_596);
x_602 = l_Nat_repr(x_601);
x_603 = lean_string_append(x_600, x_602);
lean_dec(x_602);
x_604 = l_Lean_instReprData__1___lambda__2___closed__2;
x_605 = lean_string_append(x_603, x_604);
x_606 = lean_box(0);
x_607 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_574, x_605, x_606);
x_608 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_608, 0, x_590);
lean_ctor_set(x_608, 1, x_607);
x_609 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_610 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_610, 0, x_609);
lean_ctor_set(x_610, 1, x_608);
x_611 = 0;
x_612 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_612, 0, x_610);
lean_ctor_set_uint8(x_612, sizeof(void*)*1, x_611);
x_613 = l_Repr_addAppParen(x_612, x_2);
return x_613;
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; uint8_t x_619; lean_object* x_620; lean_object* x_621; 
x_614 = lean_box(0);
x_615 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_574, x_595, x_614);
x_616 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_616, 0, x_590);
lean_ctor_set(x_616, 1, x_615);
x_617 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_618 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_618, 0, x_617);
lean_ctor_set(x_618, 1, x_616);
x_619 = 0;
x_620 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_620, 0, x_618);
lean_ctor_set_uint8(x_620, sizeof(void*)*1, x_619);
x_621 = l_Repr_addAppParen(x_620, x_2);
return x_621;
}
}
else
{
if (x_598 == 0)
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; uint8_t x_634; lean_object* x_635; lean_object* x_636; 
x_622 = l_Lean_instReprData__1___closed__2;
x_623 = lean_string_append(x_595, x_622);
x_624 = lean_uint32_to_nat(x_596);
x_625 = l_Nat_repr(x_624);
x_626 = lean_string_append(x_623, x_625);
lean_dec(x_625);
x_627 = l_Lean_instReprData__1___lambda__2___closed__2;
x_628 = lean_string_append(x_626, x_627);
x_629 = lean_box(0);
x_630 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_574, x_628, x_629);
x_631 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_631, 0, x_590);
lean_ctor_set(x_631, 1, x_630);
x_632 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_633 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_633, 0, x_632);
lean_ctor_set(x_633, 1, x_631);
x_634 = 0;
x_635 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_635, 0, x_633);
lean_ctor_set_uint8(x_635, sizeof(void*)*1, x_634);
x_636 = l_Repr_addAppParen(x_635, x_2);
return x_636;
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; uint8_t x_642; lean_object* x_643; lean_object* x_644; 
x_637 = lean_box(0);
x_638 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_574, x_595, x_637);
x_639 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_639, 0, x_590);
lean_ctor_set(x_639, 1, x_638);
x_640 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_641 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_639);
x_642 = 0;
x_643 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_643, 0, x_641);
lean_ctor_set_uint8(x_643, sizeof(void*)*1, x_642);
x_644 = l_Repr_addAppParen(x_643, x_2);
return x_644;
}
}
}
case 9:
{
lean_object* x_645; uint64_t x_646; lean_object* x_647; uint8_t x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; uint64_t x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; uint32_t x_659; uint32_t x_660; uint8_t x_661; 
x_645 = lean_ctor_get(x_1, 0);
lean_inc(x_645);
x_646 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_647 = lean_unsigned_to_nat(1024u);
x_648 = lean_nat_dec_le(x_647, x_2);
x_649 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107_(x_645, x_647);
x_650 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__41;
x_651 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_651, 0, x_650);
lean_ctor_set(x_651, 1, x_649);
x_652 = lean_box(1);
x_653 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_653, 0, x_651);
lean_ctor_set(x_653, 1, x_652);
x_654 = l_Lean_Expr_Data_hash(x_646);
x_655 = lean_uint64_to_nat(x_654);
x_656 = l_Nat_repr(x_655);
x_657 = l_Lean_instReprData__1___closed__1;
x_658 = lean_string_append(x_657, x_656);
lean_dec(x_656);
x_659 = l_Lean_Expr_Data_looseBVarRange(x_646);
x_660 = 0;
x_661 = lean_uint32_dec_eq(x_659, x_660);
if (x_648 == 0)
{
if (x_661 == 0)
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; uint8_t x_674; lean_object* x_675; lean_object* x_676; 
x_662 = l_Lean_instReprData__1___closed__2;
x_663 = lean_string_append(x_658, x_662);
x_664 = lean_uint32_to_nat(x_659);
x_665 = l_Nat_repr(x_664);
x_666 = lean_string_append(x_663, x_665);
lean_dec(x_665);
x_667 = l_Lean_instReprData__1___lambda__2___closed__2;
x_668 = lean_string_append(x_666, x_667);
x_669 = lean_box(0);
x_670 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_646, x_668, x_669);
x_671 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_671, 0, x_653);
lean_ctor_set(x_671, 1, x_670);
x_672 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_673 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_673, 0, x_672);
lean_ctor_set(x_673, 1, x_671);
x_674 = 0;
x_675 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_675, 0, x_673);
lean_ctor_set_uint8(x_675, sizeof(void*)*1, x_674);
x_676 = l_Repr_addAppParen(x_675, x_2);
return x_676;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; uint8_t x_682; lean_object* x_683; lean_object* x_684; 
x_677 = lean_box(0);
x_678 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_646, x_658, x_677);
x_679 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_679, 0, x_653);
lean_ctor_set(x_679, 1, x_678);
x_680 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_681 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_681, 0, x_680);
lean_ctor_set(x_681, 1, x_679);
x_682 = 0;
x_683 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_683, 0, x_681);
lean_ctor_set_uint8(x_683, sizeof(void*)*1, x_682);
x_684 = l_Repr_addAppParen(x_683, x_2);
return x_684;
}
}
else
{
if (x_661 == 0)
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; uint8_t x_697; lean_object* x_698; lean_object* x_699; 
x_685 = l_Lean_instReprData__1___closed__2;
x_686 = lean_string_append(x_658, x_685);
x_687 = lean_uint32_to_nat(x_659);
x_688 = l_Nat_repr(x_687);
x_689 = lean_string_append(x_686, x_688);
lean_dec(x_688);
x_690 = l_Lean_instReprData__1___lambda__2___closed__2;
x_691 = lean_string_append(x_689, x_690);
x_692 = lean_box(0);
x_693 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_646, x_691, x_692);
x_694 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_694, 0, x_653);
lean_ctor_set(x_694, 1, x_693);
x_695 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_696 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_696, 0, x_695);
lean_ctor_set(x_696, 1, x_694);
x_697 = 0;
x_698 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_698, 0, x_696);
lean_ctor_set_uint8(x_698, sizeof(void*)*1, x_697);
x_699 = l_Repr_addAppParen(x_698, x_2);
return x_699;
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; uint8_t x_705; lean_object* x_706; lean_object* x_707; 
x_700 = lean_box(0);
x_701 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_646, x_658, x_700);
x_702 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_702, 0, x_653);
lean_ctor_set(x_702, 1, x_701);
x_703 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_704 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_704, 0, x_703);
lean_ctor_set(x_704, 1, x_702);
x_705 = 0;
x_706 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_706, 0, x_704);
lean_ctor_set_uint8(x_706, sizeof(void*)*1, x_705);
x_707 = l_Repr_addAppParen(x_706, x_2);
return x_707;
}
}
}
case 10:
{
lean_object* x_708; lean_object* x_709; uint64_t x_710; lean_object* x_711; uint8_t x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; uint64_t x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; uint32_t x_726; uint32_t x_727; uint8_t x_728; 
x_708 = lean_ctor_get(x_1, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_1, 1);
lean_inc(x_709);
x_710 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_711 = lean_unsigned_to_nat(1024u);
x_712 = lean_nat_dec_le(x_711, x_2);
x_713 = l___private_Lean_Data_KVMap_0__Lean_reprKVMap____x40_Lean_Data_KVMap___hyg_844_(x_708, x_711);
x_714 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__44;
x_715 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_715, 0, x_714);
lean_ctor_set(x_715, 1, x_713);
x_716 = lean_box(1);
x_717 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_717, 0, x_715);
lean_ctor_set(x_717, 1, x_716);
x_718 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210_(x_709, x_711);
x_719 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_719, 0, x_717);
lean_ctor_set(x_719, 1, x_718);
x_720 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_720, 0, x_719);
lean_ctor_set(x_720, 1, x_716);
x_721 = l_Lean_Expr_Data_hash(x_710);
x_722 = lean_uint64_to_nat(x_721);
x_723 = l_Nat_repr(x_722);
x_724 = l_Lean_instReprData__1___closed__1;
x_725 = lean_string_append(x_724, x_723);
lean_dec(x_723);
x_726 = l_Lean_Expr_Data_looseBVarRange(x_710);
x_727 = 0;
x_728 = lean_uint32_dec_eq(x_726, x_727);
if (x_712 == 0)
{
if (x_728 == 0)
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; uint8_t x_741; lean_object* x_742; lean_object* x_743; 
x_729 = l_Lean_instReprData__1___closed__2;
x_730 = lean_string_append(x_725, x_729);
x_731 = lean_uint32_to_nat(x_726);
x_732 = l_Nat_repr(x_731);
x_733 = lean_string_append(x_730, x_732);
lean_dec(x_732);
x_734 = l_Lean_instReprData__1___lambda__2___closed__2;
x_735 = lean_string_append(x_733, x_734);
x_736 = lean_box(0);
x_737 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_710, x_735, x_736);
x_738 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_738, 0, x_720);
lean_ctor_set(x_738, 1, x_737);
x_739 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_740 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_740, 0, x_739);
lean_ctor_set(x_740, 1, x_738);
x_741 = 0;
x_742 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_742, 0, x_740);
lean_ctor_set_uint8(x_742, sizeof(void*)*1, x_741);
x_743 = l_Repr_addAppParen(x_742, x_2);
return x_743;
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; uint8_t x_749; lean_object* x_750; lean_object* x_751; 
x_744 = lean_box(0);
x_745 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_710, x_725, x_744);
x_746 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_746, 0, x_720);
lean_ctor_set(x_746, 1, x_745);
x_747 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_748 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_748, 0, x_747);
lean_ctor_set(x_748, 1, x_746);
x_749 = 0;
x_750 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_750, 0, x_748);
lean_ctor_set_uint8(x_750, sizeof(void*)*1, x_749);
x_751 = l_Repr_addAppParen(x_750, x_2);
return x_751;
}
}
else
{
if (x_728 == 0)
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; uint8_t x_764; lean_object* x_765; lean_object* x_766; 
x_752 = l_Lean_instReprData__1___closed__2;
x_753 = lean_string_append(x_725, x_752);
x_754 = lean_uint32_to_nat(x_726);
x_755 = l_Nat_repr(x_754);
x_756 = lean_string_append(x_753, x_755);
lean_dec(x_755);
x_757 = l_Lean_instReprData__1___lambda__2___closed__2;
x_758 = lean_string_append(x_756, x_757);
x_759 = lean_box(0);
x_760 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_710, x_758, x_759);
x_761 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_761, 0, x_720);
lean_ctor_set(x_761, 1, x_760);
x_762 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_763 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_763, 0, x_762);
lean_ctor_set(x_763, 1, x_761);
x_764 = 0;
x_765 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_765, 0, x_763);
lean_ctor_set_uint8(x_765, sizeof(void*)*1, x_764);
x_766 = l_Repr_addAppParen(x_765, x_2);
return x_766;
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; uint8_t x_772; lean_object* x_773; lean_object* x_774; 
x_767 = lean_box(0);
x_768 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_710, x_725, x_767);
x_769 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_769, 0, x_720);
lean_ctor_set(x_769, 1, x_768);
x_770 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_771 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_771, 0, x_770);
lean_ctor_set(x_771, 1, x_769);
x_772 = 0;
x_773 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_773, 0, x_771);
lean_ctor_set_uint8(x_773, sizeof(void*)*1, x_772);
x_774 = l_Repr_addAppParen(x_773, x_2);
return x_774;
}
}
}
default: 
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; uint64_t x_778; lean_object* x_779; uint8_t x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; uint64_t x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; uint32_t x_798; uint32_t x_799; uint8_t x_800; 
x_775 = lean_ctor_get(x_1, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_1, 1);
lean_inc(x_776);
x_777 = lean_ctor_get(x_1, 2);
lean_inc(x_777);
x_778 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_779 = lean_unsigned_to_nat(1024u);
x_780 = lean_nat_dec_le(x_779, x_2);
x_781 = l_Lean_Name_reprPrec(x_775, x_779);
x_782 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__47;
x_783 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_783, 0, x_782);
lean_ctor_set(x_783, 1, x_781);
x_784 = lean_box(1);
x_785 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_785, 0, x_783);
lean_ctor_set(x_785, 1, x_784);
x_786 = l_Nat_repr(x_776);
x_787 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_787, 0, x_786);
x_788 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_788, 0, x_785);
lean_ctor_set(x_788, 1, x_787);
x_789 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_789, 0, x_788);
lean_ctor_set(x_789, 1, x_784);
x_790 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210_(x_777, x_779);
x_791 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_791, 0, x_789);
lean_ctor_set(x_791, 1, x_790);
x_792 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_792, 0, x_791);
lean_ctor_set(x_792, 1, x_784);
x_793 = l_Lean_Expr_Data_hash(x_778);
x_794 = lean_uint64_to_nat(x_793);
x_795 = l_Nat_repr(x_794);
x_796 = l_Lean_instReprData__1___closed__1;
x_797 = lean_string_append(x_796, x_795);
lean_dec(x_795);
x_798 = l_Lean_Expr_Data_looseBVarRange(x_778);
x_799 = 0;
x_800 = lean_uint32_dec_eq(x_798, x_799);
if (x_780 == 0)
{
if (x_800 == 0)
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; uint8_t x_813; lean_object* x_814; lean_object* x_815; 
x_801 = l_Lean_instReprData__1___closed__2;
x_802 = lean_string_append(x_797, x_801);
x_803 = lean_uint32_to_nat(x_798);
x_804 = l_Nat_repr(x_803);
x_805 = lean_string_append(x_802, x_804);
lean_dec(x_804);
x_806 = l_Lean_instReprData__1___lambda__2___closed__2;
x_807 = lean_string_append(x_805, x_806);
x_808 = lean_box(0);
x_809 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_778, x_807, x_808);
x_810 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_810, 0, x_792);
lean_ctor_set(x_810, 1, x_809);
x_811 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_812 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_812, 0, x_811);
lean_ctor_set(x_812, 1, x_810);
x_813 = 0;
x_814 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_814, 0, x_812);
lean_ctor_set_uint8(x_814, sizeof(void*)*1, x_813);
x_815 = l_Repr_addAppParen(x_814, x_2);
return x_815;
}
else
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; uint8_t x_821; lean_object* x_822; lean_object* x_823; 
x_816 = lean_box(0);
x_817 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_778, x_797, x_816);
x_818 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_818, 0, x_792);
lean_ctor_set(x_818, 1, x_817);
x_819 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4;
x_820 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_820, 0, x_819);
lean_ctor_set(x_820, 1, x_818);
x_821 = 0;
x_822 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_822, 0, x_820);
lean_ctor_set_uint8(x_822, sizeof(void*)*1, x_821);
x_823 = l_Repr_addAppParen(x_822, x_2);
return x_823;
}
}
else
{
if (x_800 == 0)
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; uint8_t x_836; lean_object* x_837; lean_object* x_838; 
x_824 = l_Lean_instReprData__1___closed__2;
x_825 = lean_string_append(x_797, x_824);
x_826 = lean_uint32_to_nat(x_798);
x_827 = l_Nat_repr(x_826);
x_828 = lean_string_append(x_825, x_827);
lean_dec(x_827);
x_829 = l_Lean_instReprData__1___lambda__2___closed__2;
x_830 = lean_string_append(x_828, x_829);
x_831 = lean_box(0);
x_832 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_778, x_830, x_831);
x_833 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_833, 0, x_792);
lean_ctor_set(x_833, 1, x_832);
x_834 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_835 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_835, 0, x_834);
lean_ctor_set(x_835, 1, x_833);
x_836 = 0;
x_837 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_837, 0, x_835);
lean_ctor_set_uint8(x_837, sizeof(void*)*1, x_836);
x_838 = l_Repr_addAppParen(x_837, x_2);
return x_838;
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; uint8_t x_844; lean_object* x_845; lean_object* x_846; 
x_839 = lean_box(0);
x_840 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_778, x_797, x_839);
x_841 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_841, 0, x_792);
lean_ctor_set(x_841, 1, x_840);
x_842 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5;
x_843 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_843, 0, x_842);
lean_ctor_set(x_843, 1, x_841);
x_844 = 0;
x_845 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_845, 0, x_843);
lean_ctor_set_uint8(x_845, sizeof(void*)*1, x_844);
x_846 = l_Repr_addAppParen(x_845, x_2);
return x_846;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__2(x_4, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__3(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__4(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__5(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__6(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__7(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instReprExpr___closed__1;
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
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
uint64_t x_2; uint8_t x_3; uint32_t x_4; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_3 = l_Lean_Expr_Data_approxDepth(x_2);
x_4 = lean_uint8_to_uint32(x_3);
return x_4;
}
case 5:
{
uint64_t x_5; uint8_t x_6; uint32_t x_7; 
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_6 = l_Lean_Expr_Data_approxDepth(x_5);
x_7 = lean_uint8_to_uint32(x_6);
return x_7;
}
case 6:
{
uint64_t x_8; uint8_t x_9; uint32_t x_10; 
x_8 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_9 = l_Lean_Expr_Data_approxDepth(x_8);
x_10 = lean_uint8_to_uint32(x_9);
return x_10;
}
case 7:
{
uint64_t x_11; uint8_t x_12; uint32_t x_13; 
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_12 = l_Lean_Expr_Data_approxDepth(x_11);
x_13 = lean_uint8_to_uint32(x_12);
return x_13;
}
case 8:
{
uint64_t x_14; uint8_t x_15; uint32_t x_16; 
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_15 = l_Lean_Expr_Data_approxDepth(x_14);
x_16 = lean_uint8_to_uint32(x_15);
return x_16;
}
case 10:
{
uint64_t x_17; uint8_t x_18; uint32_t x_19; 
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_18 = l_Lean_Expr_Data_approxDepth(x_17);
x_19 = lean_uint8_to_uint32(x_18);
return x_19;
}
case 11:
{
uint64_t x_20; uint8_t x_21; uint32_t x_22; 
x_20 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_21 = l_Lean_Expr_Data_approxDepth(x_20);
x_22 = lean_uint8_to_uint32(x_21);
return x_22;
}
default: 
{
uint64_t x_23; uint8_t x_24; uint32_t x_25; 
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_24 = l_Lean_Expr_Data_approxDepth(x_23);
x_25 = lean_uint8_to_uint32(x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_approxDepth(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
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
uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint32_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; 
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
x_14 = 0;
x_15 = l_Lean_Expr_mkData(x_8, x_13, x_9, x_10, x_10, x_11, x_12, x_14, x_10);
x_16 = lean_unbox_uint64(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set_uint64(x_17, sizeof(void*)*2, x_16);
return x_17;
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
uint64_t x_2; uint64_t x_3; uint64_t x_4; lean_object* x_5; lean_object* x_6; uint32_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; 
x_2 = 7;
x_3 = lean_uint64_of_nat(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_1, x_5);
x_7 = 0;
x_8 = 0;
x_9 = 0;
x_10 = l_Lean_Expr_mkData(x_4, x_6, x_7, x_8, x_8, x_8, x_8, x_9, x_8);
lean_dec(x_6);
x_11 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set_uint64(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint32_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; 
x_2 = 11;
x_3 = l_Lean_Level_hash(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
x_5 = 0;
x_6 = l_Lean_Level_hasMVar(x_1);
x_7 = l_Lean_Level_hasParam(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = 0;
x_10 = 0;
x_11 = l_Lean_Expr_mkData(x_4, x_8, x_5, x_9, x_9, x_6, x_7, x_10, x_9);
x_12 = lean_unbox_uint64(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(3, 1, 8);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set_uint64(x_13, sizeof(void*)*1, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint32_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; 
x_2 = 13;
x_3 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1719_(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
x_5 = 0;
x_6 = lean_unsigned_to_nat(0u);
x_7 = 1;
x_8 = 0;
x_9 = 0;
x_10 = l_Lean_Expr_mkData(x_4, x_6, x_5, x_7, x_8, x_8, x_8, x_9, x_8);
x_11 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(1, 1, 8);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set_uint64(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint32_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; 
x_2 = 17;
x_3 = l___private_Lean_Level_0__Lean_hashMVarId____x40_Lean_Level___hyg_482_(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
x_5 = 0;
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = 1;
x_9 = 0;
x_10 = l_Lean_Expr_mkData(x_4, x_6, x_5, x_7, x_8, x_7, x_7, x_9, x_7);
x_11 = lean_unbox_uint64(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set_uint64(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; 
x_3 = l_Lean_Expr_approxDepth(x_2);
x_4 = 1;
x_5 = lean_uint32_add(x_3, x_4);
x_6 = lean_uint32_to_uint64(x_5);
x_7 = l_Lean_Expr_hash(x_2);
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = l_Lean_Expr_looseBVarRange(x_2);
x_10 = l_Lean_Expr_hasFVar(x_2);
x_11 = l_Lean_Expr_hasExprMVar(x_2);
x_12 = l_Lean_Expr_hasLevelMVar(x_2);
x_13 = l_Lean_Expr_hasLevelParam(x_2);
x_14 = 0;
x_15 = 0;
x_16 = l_Lean_Expr_mkData(x_8, x_9, x_5, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
x_17 = lean_unbox_uint64(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set_uint64(x_18, sizeof(void*)*2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; uint32_t x_5; uint32_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; 
x_4 = l_Lean_Expr_approxDepth(x_3);
x_5 = 1;
x_6 = lean_uint32_add(x_4, x_5);
x_7 = lean_uint32_to_uint64(x_6);
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
x_19 = 0;
x_20 = 0;
x_21 = l_Lean_Expr_mkData(x_13, x_14, x_6, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_14);
x_22 = lean_unbox_uint64(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set(x_23, 2, x_3);
lean_ctor_set_uint64(x_23, sizeof(void*)*3, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; uint32_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint32_t x_17; 
x_3 = l_Lean_Expr_approxDepth(x_1);
x_4 = l_Lean_Expr_approxDepth(x_2);
x_5 = lean_uint32_dec_lt(x_4, x_3);
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
goto block_135;
}
else
{
x_17 = x_3;
goto block_135;
}
block_135:
{
uint32_t x_18; uint64_t x_19; uint64_t x_20; lean_object* x_21; lean_object* x_78; 
x_18 = lean_uint32_add(x_17, x_6);
x_19 = lean_uint32_to_uint64(x_18);
x_20 = lean_uint64_mix_hash(x_19, x_9);
if (x_12 == 0)
{
lean_dec(x_10);
if (x_13 == 0)
{
x_21 = x_11;
goto block_77;
}
else
{
x_78 = x_11;
goto block_134;
}
}
else
{
lean_dec(x_11);
if (x_13 == 0)
{
x_21 = x_10;
goto block_77;
}
else
{
x_78 = x_10;
goto block_134;
}
}
block_77:
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
uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; 
x_25 = l_Lean_Expr_hasLevelParam(x_2);
x_26 = 0;
x_27 = 0;
x_28 = l_Lean_Expr_mkData(x_20, x_21, x_18, x_22, x_23, x_24, x_25, x_26, x_27);
lean_dec(x_21);
x_29 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set_uint64(x_30, sizeof(void*)*2, x_29);
return x_30;
}
else
{
uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; 
x_31 = 1;
x_32 = 0;
x_33 = 0;
x_34 = l_Lean_Expr_mkData(x_20, x_21, x_18, x_22, x_23, x_24, x_31, x_32, x_33);
lean_dec(x_21);
x_35 = lean_unbox_uint64(x_34);
lean_dec(x_34);
x_36 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_2);
lean_ctor_set_uint64(x_36, sizeof(void*)*2, x_35);
return x_36;
}
}
else
{
if (x_16 == 0)
{
uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; 
x_37 = l_Lean_Expr_hasLevelParam(x_2);
x_38 = 1;
x_39 = 0;
x_40 = 0;
x_41 = l_Lean_Expr_mkData(x_20, x_21, x_18, x_22, x_23, x_38, x_37, x_39, x_40);
lean_dec(x_21);
x_42 = lean_unbox_uint64(x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_2);
lean_ctor_set_uint64(x_43, sizeof(void*)*2, x_42);
return x_43;
}
else
{
uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; 
x_44 = 1;
x_45 = 0;
x_46 = 0;
x_47 = l_Lean_Expr_mkData(x_20, x_21, x_18, x_22, x_23, x_44, x_44, x_45, x_46);
lean_dec(x_21);
x_48 = lean_unbox_uint64(x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_2);
lean_ctor_set_uint64(x_49, sizeof(void*)*2, x_48);
return x_49;
}
}
}
else
{
if (x_15 == 0)
{
uint8_t x_50; 
x_50 = l_Lean_Expr_hasLevelMVar(x_2);
if (x_16 == 0)
{
uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; uint64_t x_56; lean_object* x_57; 
x_51 = l_Lean_Expr_hasLevelParam(x_2);
x_52 = 1;
x_53 = 0;
x_54 = 0;
x_55 = l_Lean_Expr_mkData(x_20, x_21, x_18, x_22, x_52, x_50, x_51, x_53, x_54);
lean_dec(x_21);
x_56 = lean_unbox_uint64(x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_2);
lean_ctor_set_uint64(x_57, sizeof(void*)*2, x_56);
return x_57;
}
else
{
uint8_t x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; uint64_t x_62; lean_object* x_63; 
x_58 = 1;
x_59 = 0;
x_60 = 0;
x_61 = l_Lean_Expr_mkData(x_20, x_21, x_18, x_22, x_58, x_50, x_58, x_59, x_60);
lean_dec(x_21);
x_62 = lean_unbox_uint64(x_61);
lean_dec(x_61);
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
uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; uint64_t x_69; lean_object* x_70; 
x_64 = l_Lean_Expr_hasLevelParam(x_2);
x_65 = 1;
x_66 = 0;
x_67 = 0;
x_68 = l_Lean_Expr_mkData(x_20, x_21, x_18, x_22, x_65, x_65, x_64, x_66, x_67);
lean_dec(x_21);
x_69 = lean_unbox_uint64(x_68);
lean_dec(x_68);
x_70 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_2);
lean_ctor_set_uint64(x_70, sizeof(void*)*2, x_69);
return x_70;
}
else
{
uint8_t x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; uint64_t x_75; lean_object* x_76; 
x_71 = 1;
x_72 = 0;
x_73 = 0;
x_74 = l_Lean_Expr_mkData(x_20, x_21, x_18, x_22, x_71, x_71, x_71, x_72, x_73);
lean_dec(x_21);
x_75 = lean_unbox_uint64(x_74);
lean_dec(x_74);
x_76 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_2);
lean_ctor_set_uint64(x_76, sizeof(void*)*2, x_75);
return x_76;
}
}
}
}
block_134:
{
if (x_14 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Expr_hasExprMVar(x_2);
if (x_15 == 0)
{
uint8_t x_80; 
x_80 = l_Lean_Expr_hasLevelMVar(x_2);
if (x_16 == 0)
{
uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; 
x_81 = l_Lean_Expr_hasLevelParam(x_2);
x_82 = 1;
x_83 = 0;
x_84 = 0;
x_85 = l_Lean_Expr_mkData(x_20, x_78, x_18, x_82, x_79, x_80, x_81, x_83, x_84);
lean_dec(x_78);
x_86 = lean_unbox_uint64(x_85);
lean_dec(x_85);
x_87 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_2);
lean_ctor_set_uint64(x_87, sizeof(void*)*2, x_86);
return x_87;
}
else
{
uint8_t x_88; uint8_t x_89; uint8_t x_90; lean_object* x_91; uint64_t x_92; lean_object* x_93; 
x_88 = 1;
x_89 = 0;
x_90 = 0;
x_91 = l_Lean_Expr_mkData(x_20, x_78, x_18, x_88, x_79, x_80, x_88, x_89, x_90);
lean_dec(x_78);
x_92 = lean_unbox_uint64(x_91);
lean_dec(x_91);
x_93 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_2);
lean_ctor_set_uint64(x_93, sizeof(void*)*2, x_92);
return x_93;
}
}
else
{
if (x_16 == 0)
{
uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; uint64_t x_99; lean_object* x_100; 
x_94 = l_Lean_Expr_hasLevelParam(x_2);
x_95 = 1;
x_96 = 0;
x_97 = 0;
x_98 = l_Lean_Expr_mkData(x_20, x_78, x_18, x_95, x_79, x_95, x_94, x_96, x_97);
lean_dec(x_78);
x_99 = lean_unbox_uint64(x_98);
lean_dec(x_98);
x_100 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_100, 0, x_1);
lean_ctor_set(x_100, 1, x_2);
lean_ctor_set_uint64(x_100, sizeof(void*)*2, x_99);
return x_100;
}
else
{
uint8_t x_101; uint8_t x_102; uint8_t x_103; lean_object* x_104; uint64_t x_105; lean_object* x_106; 
x_101 = 1;
x_102 = 0;
x_103 = 0;
x_104 = l_Lean_Expr_mkData(x_20, x_78, x_18, x_101, x_79, x_101, x_101, x_102, x_103);
lean_dec(x_78);
x_105 = lean_unbox_uint64(x_104);
lean_dec(x_104);
x_106 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_106, 0, x_1);
lean_ctor_set(x_106, 1, x_2);
lean_ctor_set_uint64(x_106, sizeof(void*)*2, x_105);
return x_106;
}
}
}
else
{
if (x_15 == 0)
{
uint8_t x_107; 
x_107 = l_Lean_Expr_hasLevelMVar(x_2);
if (x_16 == 0)
{
uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; uint64_t x_113; lean_object* x_114; 
x_108 = l_Lean_Expr_hasLevelParam(x_2);
x_109 = 1;
x_110 = 0;
x_111 = 0;
x_112 = l_Lean_Expr_mkData(x_20, x_78, x_18, x_109, x_109, x_107, x_108, x_110, x_111);
lean_dec(x_78);
x_113 = lean_unbox_uint64(x_112);
lean_dec(x_112);
x_114 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_114, 0, x_1);
lean_ctor_set(x_114, 1, x_2);
lean_ctor_set_uint64(x_114, sizeof(void*)*2, x_113);
return x_114;
}
else
{
uint8_t x_115; uint8_t x_116; uint8_t x_117; lean_object* x_118; uint64_t x_119; lean_object* x_120; 
x_115 = 1;
x_116 = 0;
x_117 = 0;
x_118 = l_Lean_Expr_mkData(x_20, x_78, x_18, x_115, x_115, x_107, x_115, x_116, x_117);
lean_dec(x_78);
x_119 = lean_unbox_uint64(x_118);
lean_dec(x_118);
x_120 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_120, 0, x_1);
lean_ctor_set(x_120, 1, x_2);
lean_ctor_set_uint64(x_120, sizeof(void*)*2, x_119);
return x_120;
}
}
else
{
if (x_16 == 0)
{
uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; lean_object* x_125; uint64_t x_126; lean_object* x_127; 
x_121 = l_Lean_Expr_hasLevelParam(x_2);
x_122 = 1;
x_123 = 0;
x_124 = 0;
x_125 = l_Lean_Expr_mkData(x_20, x_78, x_18, x_122, x_122, x_122, x_121, x_123, x_124);
lean_dec(x_78);
x_126 = lean_unbox_uint64(x_125);
lean_dec(x_125);
x_127 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_127, 0, x_1);
lean_ctor_set(x_127, 1, x_2);
lean_ctor_set_uint64(x_127, sizeof(void*)*2, x_126);
return x_127;
}
else
{
uint8_t x_128; uint8_t x_129; uint8_t x_130; lean_object* x_131; uint64_t x_132; lean_object* x_133; 
x_128 = 1;
x_129 = 0;
x_130 = 0;
x_131 = l_Lean_Expr_mkData(x_20, x_78, x_18, x_128, x_128, x_128, x_128, x_129, x_130);
lean_dec(x_78);
x_132 = lean_unbox_uint64(x_131);
lean_dec(x_131);
x_133 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_133, 0, x_1);
lean_ctor_set(x_133, 1, x_2);
lean_ctor_set_uint64(x_133, sizeof(void*)*2, x_132);
return x_133;
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
uint32_t x_5; uint32_t x_6; uint8_t x_7; uint32_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint32_t x_21; 
x_5 = l_Lean_Expr_approxDepth(x_3);
x_6 = l_Lean_Expr_approxDepth(x_4);
x_7 = lean_uint32_dec_lt(x_6, x_5);
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
goto block_123;
}
else
{
x_21 = x_5;
goto block_123;
}
block_123:
{
uint32_t x_22; uint64_t x_23; uint64_t x_24; lean_object* x_25; lean_object* x_74; 
x_22 = lean_uint32_add(x_21, x_8);
x_23 = lean_uint32_to_uint64(x_22);
x_24 = lean_uint64_mix_hash(x_23, x_11);
if (x_16 == 0)
{
lean_dec(x_12);
if (x_17 == 0)
{
x_25 = x_15;
goto block_73;
}
else
{
x_74 = x_15;
goto block_122;
}
}
else
{
lean_dec(x_15);
if (x_17 == 0)
{
x_25 = x_12;
goto block_73;
}
else
{
x_74 = x_12;
goto block_122;
}
}
block_73:
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
uint8_t x_29; uint8_t x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; 
x_29 = l_Lean_Expr_hasLevelParam(x_4);
x_30 = 0;
x_31 = l_Lean_Expr_mkData(x_24, x_25, x_22, x_26, x_27, x_28, x_29, x_2, x_30);
lean_dec(x_25);
x_32 = lean_unbox_uint64(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_3);
lean_ctor_set(x_33, 2, x_4);
lean_ctor_set_uint64(x_33, sizeof(void*)*3, x_32);
return x_33;
}
else
{
uint8_t x_34; uint8_t x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; 
x_34 = 1;
x_35 = 0;
x_36 = l_Lean_Expr_mkData(x_24, x_25, x_22, x_26, x_27, x_28, x_34, x_2, x_35);
lean_dec(x_25);
x_37 = lean_unbox_uint64(x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set(x_38, 2, x_4);
lean_ctor_set_uint64(x_38, sizeof(void*)*3, x_37);
return x_38;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; 
x_39 = l_Lean_Expr_hasLevelParam(x_4);
x_40 = 1;
x_41 = 0;
x_42 = l_Lean_Expr_mkData(x_24, x_25, x_22, x_26, x_27, x_40, x_39, x_2, x_41);
lean_dec(x_25);
x_43 = lean_unbox_uint64(x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_3);
lean_ctor_set(x_44, 2, x_4);
lean_ctor_set_uint64(x_44, sizeof(void*)*3, x_43);
return x_44;
}
else
{
uint8_t x_45; uint8_t x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; 
x_45 = 1;
x_46 = 0;
x_47 = l_Lean_Expr_mkData(x_24, x_25, x_22, x_26, x_27, x_45, x_45, x_2, x_46);
lean_dec(x_25);
x_48 = lean_unbox_uint64(x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_3);
lean_ctor_set(x_49, 2, x_4);
lean_ctor_set_uint64(x_49, sizeof(void*)*3, x_48);
return x_49;
}
}
}
else
{
if (x_19 == 0)
{
uint8_t x_50; 
x_50 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_20 == 0)
{
uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; uint64_t x_55; lean_object* x_56; 
x_51 = l_Lean_Expr_hasLevelParam(x_4);
x_52 = 1;
x_53 = 0;
x_54 = l_Lean_Expr_mkData(x_24, x_25, x_22, x_26, x_52, x_50, x_51, x_2, x_53);
lean_dec(x_25);
x_55 = lean_unbox_uint64(x_54);
lean_dec(x_54);
x_56 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_4);
lean_ctor_set_uint64(x_56, sizeof(void*)*3, x_55);
return x_56;
}
else
{
uint8_t x_57; uint8_t x_58; lean_object* x_59; uint64_t x_60; lean_object* x_61; 
x_57 = 1;
x_58 = 0;
x_59 = l_Lean_Expr_mkData(x_24, x_25, x_22, x_26, x_57, x_50, x_57, x_2, x_58);
lean_dec(x_25);
x_60 = lean_unbox_uint64(x_59);
lean_dec(x_59);
x_61 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_3);
lean_ctor_set(x_61, 2, x_4);
lean_ctor_set_uint64(x_61, sizeof(void*)*3, x_60);
return x_61;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; uint64_t x_66; lean_object* x_67; 
x_62 = l_Lean_Expr_hasLevelParam(x_4);
x_63 = 1;
x_64 = 0;
x_65 = l_Lean_Expr_mkData(x_24, x_25, x_22, x_26, x_63, x_63, x_62, x_2, x_64);
lean_dec(x_25);
x_66 = lean_unbox_uint64(x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_3);
lean_ctor_set(x_67, 2, x_4);
lean_ctor_set_uint64(x_67, sizeof(void*)*3, x_66);
return x_67;
}
else
{
uint8_t x_68; uint8_t x_69; lean_object* x_70; uint64_t x_71; lean_object* x_72; 
x_68 = 1;
x_69 = 0;
x_70 = l_Lean_Expr_mkData(x_24, x_25, x_22, x_26, x_68, x_68, x_68, x_2, x_69);
lean_dec(x_25);
x_71 = lean_unbox_uint64(x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_3);
lean_ctor_set(x_72, 2, x_4);
lean_ctor_set_uint64(x_72, sizeof(void*)*3, x_71);
return x_72;
}
}
}
}
block_122:
{
if (x_18 == 0)
{
uint8_t x_75; 
x_75 = l_Lean_Expr_hasExprMVar(x_4);
if (x_19 == 0)
{
uint8_t x_76; 
x_76 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_20 == 0)
{
uint8_t x_77; uint8_t x_78; uint8_t x_79; lean_object* x_80; uint64_t x_81; lean_object* x_82; 
x_77 = l_Lean_Expr_hasLevelParam(x_4);
x_78 = 1;
x_79 = 0;
x_80 = l_Lean_Expr_mkData(x_24, x_74, x_22, x_78, x_75, x_76, x_77, x_2, x_79);
lean_dec(x_74);
x_81 = lean_unbox_uint64(x_80);
lean_dec(x_80);
x_82 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_3);
lean_ctor_set(x_82, 2, x_4);
lean_ctor_set_uint64(x_82, sizeof(void*)*3, x_81);
return x_82;
}
else
{
uint8_t x_83; uint8_t x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; 
x_83 = 1;
x_84 = 0;
x_85 = l_Lean_Expr_mkData(x_24, x_74, x_22, x_83, x_75, x_76, x_83, x_2, x_84);
lean_dec(x_74);
x_86 = lean_unbox_uint64(x_85);
lean_dec(x_85);
x_87 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_3);
lean_ctor_set(x_87, 2, x_4);
lean_ctor_set_uint64(x_87, sizeof(void*)*3, x_86);
return x_87;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_88; uint8_t x_89; uint8_t x_90; lean_object* x_91; uint64_t x_92; lean_object* x_93; 
x_88 = l_Lean_Expr_hasLevelParam(x_4);
x_89 = 1;
x_90 = 0;
x_91 = l_Lean_Expr_mkData(x_24, x_74, x_22, x_89, x_75, x_89, x_88, x_2, x_90);
lean_dec(x_74);
x_92 = lean_unbox_uint64(x_91);
lean_dec(x_91);
x_93 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_3);
lean_ctor_set(x_93, 2, x_4);
lean_ctor_set_uint64(x_93, sizeof(void*)*3, x_92);
return x_93;
}
else
{
uint8_t x_94; uint8_t x_95; lean_object* x_96; uint64_t x_97; lean_object* x_98; 
x_94 = 1;
x_95 = 0;
x_96 = l_Lean_Expr_mkData(x_24, x_74, x_22, x_94, x_75, x_94, x_94, x_2, x_95);
lean_dec(x_74);
x_97 = lean_unbox_uint64(x_96);
lean_dec(x_96);
x_98 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_98, 0, x_1);
lean_ctor_set(x_98, 1, x_3);
lean_ctor_set(x_98, 2, x_4);
lean_ctor_set_uint64(x_98, sizeof(void*)*3, x_97);
return x_98;
}
}
}
else
{
if (x_19 == 0)
{
uint8_t x_99; 
x_99 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_20 == 0)
{
uint8_t x_100; uint8_t x_101; uint8_t x_102; lean_object* x_103; uint64_t x_104; lean_object* x_105; 
x_100 = l_Lean_Expr_hasLevelParam(x_4);
x_101 = 1;
x_102 = 0;
x_103 = l_Lean_Expr_mkData(x_24, x_74, x_22, x_101, x_101, x_99, x_100, x_2, x_102);
lean_dec(x_74);
x_104 = lean_unbox_uint64(x_103);
lean_dec(x_103);
x_105 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_105, 0, x_1);
lean_ctor_set(x_105, 1, x_3);
lean_ctor_set(x_105, 2, x_4);
lean_ctor_set_uint64(x_105, sizeof(void*)*3, x_104);
return x_105;
}
else
{
uint8_t x_106; uint8_t x_107; lean_object* x_108; uint64_t x_109; lean_object* x_110; 
x_106 = 1;
x_107 = 0;
x_108 = l_Lean_Expr_mkData(x_24, x_74, x_22, x_106, x_106, x_99, x_106, x_2, x_107);
lean_dec(x_74);
x_109 = lean_unbox_uint64(x_108);
lean_dec(x_108);
x_110 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_110, 0, x_1);
lean_ctor_set(x_110, 1, x_3);
lean_ctor_set(x_110, 2, x_4);
lean_ctor_set_uint64(x_110, sizeof(void*)*3, x_109);
return x_110;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_111; uint8_t x_112; uint8_t x_113; lean_object* x_114; uint64_t x_115; lean_object* x_116; 
x_111 = l_Lean_Expr_hasLevelParam(x_4);
x_112 = 1;
x_113 = 0;
x_114 = l_Lean_Expr_mkData(x_24, x_74, x_22, x_112, x_112, x_112, x_111, x_2, x_113);
lean_dec(x_74);
x_115 = lean_unbox_uint64(x_114);
lean_dec(x_114);
x_116 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_116, 0, x_1);
lean_ctor_set(x_116, 1, x_3);
lean_ctor_set(x_116, 2, x_4);
lean_ctor_set_uint64(x_116, sizeof(void*)*3, x_115);
return x_116;
}
else
{
uint8_t x_117; uint8_t x_118; lean_object* x_119; uint64_t x_120; lean_object* x_121; 
x_117 = 1;
x_118 = 0;
x_119 = l_Lean_Expr_mkData(x_24, x_74, x_22, x_117, x_117, x_117, x_117, x_2, x_118);
lean_dec(x_74);
x_120 = lean_unbox_uint64(x_119);
lean_dec(x_119);
x_121 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_121, 0, x_1);
lean_ctor_set(x_121, 1, x_3);
lean_ctor_set(x_121, 2, x_4);
lean_ctor_set_uint64(x_121, sizeof(void*)*3, x_120);
return x_121;
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
uint32_t x_5; uint32_t x_6; uint8_t x_7; uint32_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint32_t x_21; 
x_5 = l_Lean_Expr_approxDepth(x_3);
x_6 = l_Lean_Expr_approxDepth(x_4);
x_7 = lean_uint32_dec_lt(x_6, x_5);
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
goto block_123;
}
else
{
x_21 = x_5;
goto block_123;
}
block_123:
{
uint32_t x_22; uint64_t x_23; uint64_t x_24; lean_object* x_25; lean_object* x_74; 
x_22 = lean_uint32_add(x_21, x_8);
x_23 = lean_uint32_to_uint64(x_22);
x_24 = lean_uint64_mix_hash(x_23, x_11);
if (x_16 == 0)
{
lean_dec(x_12);
if (x_17 == 0)
{
x_25 = x_15;
goto block_73;
}
else
{
x_74 = x_15;
goto block_122;
}
}
else
{
lean_dec(x_15);
if (x_17 == 0)
{
x_25 = x_12;
goto block_73;
}
else
{
x_74 = x_12;
goto block_122;
}
}
block_73:
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
uint8_t x_29; uint8_t x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; 
x_29 = l_Lean_Expr_hasLevelParam(x_4);
x_30 = 0;
x_31 = l_Lean_Expr_mkData(x_24, x_25, x_22, x_26, x_27, x_28, x_29, x_2, x_30);
lean_dec(x_25);
x_32 = lean_unbox_uint64(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_3);
lean_ctor_set(x_33, 2, x_4);
lean_ctor_set_uint64(x_33, sizeof(void*)*3, x_32);
return x_33;
}
else
{
uint8_t x_34; uint8_t x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; 
x_34 = 1;
x_35 = 0;
x_36 = l_Lean_Expr_mkData(x_24, x_25, x_22, x_26, x_27, x_28, x_34, x_2, x_35);
lean_dec(x_25);
x_37 = lean_unbox_uint64(x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set(x_38, 2, x_4);
lean_ctor_set_uint64(x_38, sizeof(void*)*3, x_37);
return x_38;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; 
x_39 = l_Lean_Expr_hasLevelParam(x_4);
x_40 = 1;
x_41 = 0;
x_42 = l_Lean_Expr_mkData(x_24, x_25, x_22, x_26, x_27, x_40, x_39, x_2, x_41);
lean_dec(x_25);
x_43 = lean_unbox_uint64(x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_3);
lean_ctor_set(x_44, 2, x_4);
lean_ctor_set_uint64(x_44, sizeof(void*)*3, x_43);
return x_44;
}
else
{
uint8_t x_45; uint8_t x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; 
x_45 = 1;
x_46 = 0;
x_47 = l_Lean_Expr_mkData(x_24, x_25, x_22, x_26, x_27, x_45, x_45, x_2, x_46);
lean_dec(x_25);
x_48 = lean_unbox_uint64(x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_3);
lean_ctor_set(x_49, 2, x_4);
lean_ctor_set_uint64(x_49, sizeof(void*)*3, x_48);
return x_49;
}
}
}
else
{
if (x_19 == 0)
{
uint8_t x_50; 
x_50 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_20 == 0)
{
uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; uint64_t x_55; lean_object* x_56; 
x_51 = l_Lean_Expr_hasLevelParam(x_4);
x_52 = 1;
x_53 = 0;
x_54 = l_Lean_Expr_mkData(x_24, x_25, x_22, x_26, x_52, x_50, x_51, x_2, x_53);
lean_dec(x_25);
x_55 = lean_unbox_uint64(x_54);
lean_dec(x_54);
x_56 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_4);
lean_ctor_set_uint64(x_56, sizeof(void*)*3, x_55);
return x_56;
}
else
{
uint8_t x_57; uint8_t x_58; lean_object* x_59; uint64_t x_60; lean_object* x_61; 
x_57 = 1;
x_58 = 0;
x_59 = l_Lean_Expr_mkData(x_24, x_25, x_22, x_26, x_57, x_50, x_57, x_2, x_58);
lean_dec(x_25);
x_60 = lean_unbox_uint64(x_59);
lean_dec(x_59);
x_61 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_3);
lean_ctor_set(x_61, 2, x_4);
lean_ctor_set_uint64(x_61, sizeof(void*)*3, x_60);
return x_61;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; uint64_t x_66; lean_object* x_67; 
x_62 = l_Lean_Expr_hasLevelParam(x_4);
x_63 = 1;
x_64 = 0;
x_65 = l_Lean_Expr_mkData(x_24, x_25, x_22, x_26, x_63, x_63, x_62, x_2, x_64);
lean_dec(x_25);
x_66 = lean_unbox_uint64(x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_3);
lean_ctor_set(x_67, 2, x_4);
lean_ctor_set_uint64(x_67, sizeof(void*)*3, x_66);
return x_67;
}
else
{
uint8_t x_68; uint8_t x_69; lean_object* x_70; uint64_t x_71; lean_object* x_72; 
x_68 = 1;
x_69 = 0;
x_70 = l_Lean_Expr_mkData(x_24, x_25, x_22, x_26, x_68, x_68, x_68, x_2, x_69);
lean_dec(x_25);
x_71 = lean_unbox_uint64(x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_3);
lean_ctor_set(x_72, 2, x_4);
lean_ctor_set_uint64(x_72, sizeof(void*)*3, x_71);
return x_72;
}
}
}
}
block_122:
{
if (x_18 == 0)
{
uint8_t x_75; 
x_75 = l_Lean_Expr_hasExprMVar(x_4);
if (x_19 == 0)
{
uint8_t x_76; 
x_76 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_20 == 0)
{
uint8_t x_77; uint8_t x_78; uint8_t x_79; lean_object* x_80; uint64_t x_81; lean_object* x_82; 
x_77 = l_Lean_Expr_hasLevelParam(x_4);
x_78 = 1;
x_79 = 0;
x_80 = l_Lean_Expr_mkData(x_24, x_74, x_22, x_78, x_75, x_76, x_77, x_2, x_79);
lean_dec(x_74);
x_81 = lean_unbox_uint64(x_80);
lean_dec(x_80);
x_82 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_3);
lean_ctor_set(x_82, 2, x_4);
lean_ctor_set_uint64(x_82, sizeof(void*)*3, x_81);
return x_82;
}
else
{
uint8_t x_83; uint8_t x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; 
x_83 = 1;
x_84 = 0;
x_85 = l_Lean_Expr_mkData(x_24, x_74, x_22, x_83, x_75, x_76, x_83, x_2, x_84);
lean_dec(x_74);
x_86 = lean_unbox_uint64(x_85);
lean_dec(x_85);
x_87 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_3);
lean_ctor_set(x_87, 2, x_4);
lean_ctor_set_uint64(x_87, sizeof(void*)*3, x_86);
return x_87;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_88; uint8_t x_89; uint8_t x_90; lean_object* x_91; uint64_t x_92; lean_object* x_93; 
x_88 = l_Lean_Expr_hasLevelParam(x_4);
x_89 = 1;
x_90 = 0;
x_91 = l_Lean_Expr_mkData(x_24, x_74, x_22, x_89, x_75, x_89, x_88, x_2, x_90);
lean_dec(x_74);
x_92 = lean_unbox_uint64(x_91);
lean_dec(x_91);
x_93 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_3);
lean_ctor_set(x_93, 2, x_4);
lean_ctor_set_uint64(x_93, sizeof(void*)*3, x_92);
return x_93;
}
else
{
uint8_t x_94; uint8_t x_95; lean_object* x_96; uint64_t x_97; lean_object* x_98; 
x_94 = 1;
x_95 = 0;
x_96 = l_Lean_Expr_mkData(x_24, x_74, x_22, x_94, x_75, x_94, x_94, x_2, x_95);
lean_dec(x_74);
x_97 = lean_unbox_uint64(x_96);
lean_dec(x_96);
x_98 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_98, 0, x_1);
lean_ctor_set(x_98, 1, x_3);
lean_ctor_set(x_98, 2, x_4);
lean_ctor_set_uint64(x_98, sizeof(void*)*3, x_97);
return x_98;
}
}
}
else
{
if (x_19 == 0)
{
uint8_t x_99; 
x_99 = l_Lean_Expr_hasLevelMVar(x_4);
if (x_20 == 0)
{
uint8_t x_100; uint8_t x_101; uint8_t x_102; lean_object* x_103; uint64_t x_104; lean_object* x_105; 
x_100 = l_Lean_Expr_hasLevelParam(x_4);
x_101 = 1;
x_102 = 0;
x_103 = l_Lean_Expr_mkData(x_24, x_74, x_22, x_101, x_101, x_99, x_100, x_2, x_102);
lean_dec(x_74);
x_104 = lean_unbox_uint64(x_103);
lean_dec(x_103);
x_105 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_105, 0, x_1);
lean_ctor_set(x_105, 1, x_3);
lean_ctor_set(x_105, 2, x_4);
lean_ctor_set_uint64(x_105, sizeof(void*)*3, x_104);
return x_105;
}
else
{
uint8_t x_106; uint8_t x_107; lean_object* x_108; uint64_t x_109; lean_object* x_110; 
x_106 = 1;
x_107 = 0;
x_108 = l_Lean_Expr_mkData(x_24, x_74, x_22, x_106, x_106, x_99, x_106, x_2, x_107);
lean_dec(x_74);
x_109 = lean_unbox_uint64(x_108);
lean_dec(x_108);
x_110 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_110, 0, x_1);
lean_ctor_set(x_110, 1, x_3);
lean_ctor_set(x_110, 2, x_4);
lean_ctor_set_uint64(x_110, sizeof(void*)*3, x_109);
return x_110;
}
}
else
{
if (x_20 == 0)
{
uint8_t x_111; uint8_t x_112; uint8_t x_113; lean_object* x_114; uint64_t x_115; lean_object* x_116; 
x_111 = l_Lean_Expr_hasLevelParam(x_4);
x_112 = 1;
x_113 = 0;
x_114 = l_Lean_Expr_mkData(x_24, x_74, x_22, x_112, x_112, x_112, x_111, x_2, x_113);
lean_dec(x_74);
x_115 = lean_unbox_uint64(x_114);
lean_dec(x_114);
x_116 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_116, 0, x_1);
lean_ctor_set(x_116, 1, x_3);
lean_ctor_set(x_116, 2, x_4);
lean_ctor_set_uint64(x_116, sizeof(void*)*3, x_115);
return x_116;
}
else
{
uint8_t x_117; uint8_t x_118; lean_object* x_119; uint64_t x_120; lean_object* x_121; 
x_117 = 1;
x_118 = 0;
x_119 = l_Lean_Expr_mkData(x_24, x_74, x_22, x_117, x_117, x_117, x_117, x_2, x_118);
lean_dec(x_74);
x_120 = lean_unbox_uint64(x_119);
lean_dec(x_119);
x_121 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_121, 0, x_1);
lean_ctor_set(x_121, 1, x_3);
lean_ctor_set(x_121, 2, x_4);
lean_ctor_set_uint64(x_121, sizeof(void*)*3, x_120);
return x_121;
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
uint32_t x_6; uint32_t x_7; uint8_t x_8; uint32_t x_9; uint32_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint32_t x_26; 
x_6 = l_Lean_Expr_approxDepth(x_2);
x_7 = l_Lean_Expr_approxDepth(x_3);
x_8 = lean_uint32_dec_lt(x_7, x_6);
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
uint8_t x_133; 
x_133 = lean_uint32_dec_lt(x_9, x_7);
if (x_133 == 0)
{
x_26 = x_9;
goto block_132;
}
else
{
x_26 = x_7;
goto block_132;
}
}
else
{
uint8_t x_134; 
x_134 = lean_uint32_dec_lt(x_9, x_6);
if (x_134 == 0)
{
x_26 = x_9;
goto block_132;
}
else
{
x_26 = x_6;
goto block_132;
}
}
block_132:
{
uint32_t x_27; uint64_t x_28; uint64_t x_29; lean_object* x_30; 
x_27 = lean_uint32_add(x_26, x_10);
x_28 = lean_uint32_to_uint64(x_27);
x_29 = lean_uint64_mix_hash(x_28, x_15);
if (x_18 == 0)
{
uint8_t x_130; 
lean_dec(x_16);
x_130 = lean_nat_dec_lt(x_21, x_17);
if (x_130 == 0)
{
lean_dec(x_17);
x_30 = x_21;
goto block_129;
}
else
{
lean_dec(x_21);
x_30 = x_17;
goto block_129;
}
}
else
{
uint8_t x_131; 
lean_dec(x_17);
x_131 = lean_nat_dec_lt(x_21, x_16);
if (x_131 == 0)
{
lean_dec(x_16);
x_30 = x_21;
goto block_129;
}
else
{
lean_dec(x_21);
x_30 = x_16;
goto block_129;
}
}
block_129:
{
uint8_t x_31; 
if (x_22 == 0)
{
uint8_t x_125; 
x_125 = l_Lean_Expr_hasFVar(x_3);
if (x_125 == 0)
{
uint8_t x_126; 
x_126 = l_Lean_Expr_hasFVar(x_4);
x_31 = x_126;
goto block_124;
}
else
{
uint8_t x_127; 
x_127 = 1;
x_31 = x_127;
goto block_124;
}
}
else
{
uint8_t x_128; 
x_128 = 1;
x_31 = x_128;
goto block_124;
}
block_124:
{
uint8_t x_32; 
if (x_23 == 0)
{
uint8_t x_69; 
x_69 = l_Lean_Expr_hasExprMVar(x_3);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_hasExprMVar(x_4);
if (x_24 == 0)
{
x_32 = x_70;
goto block_68;
}
else
{
if (x_25 == 0)
{
uint8_t x_71; 
x_71 = l_Lean_Expr_hasLevelParam(x_3);
if (x_71 == 0)
{
uint8_t x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; 
x_72 = l_Lean_Expr_hasLevelParam(x_4);
x_73 = 1;
x_74 = 0;
x_75 = l_Lean_Expr_mkData(x_29, x_30, x_27, x_31, x_70, x_73, x_72, x_74, x_5);
lean_dec(x_30);
x_76 = lean_unbox_uint64(x_75);
lean_dec(x_75);
x_77 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_2);
lean_ctor_set(x_77, 2, x_3);
lean_ctor_set(x_77, 3, x_4);
lean_ctor_set_uint64(x_77, sizeof(void*)*4, x_76);
return x_77;
}
else
{
uint8_t x_78; uint8_t x_79; lean_object* x_80; uint64_t x_81; lean_object* x_82; 
x_78 = 1;
x_79 = 0;
x_80 = l_Lean_Expr_mkData(x_29, x_30, x_27, x_31, x_70, x_78, x_78, x_79, x_5);
lean_dec(x_30);
x_81 = lean_unbox_uint64(x_80);
lean_dec(x_80);
x_82 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_2);
lean_ctor_set(x_82, 2, x_3);
lean_ctor_set(x_82, 3, x_4);
lean_ctor_set_uint64(x_82, sizeof(void*)*4, x_81);
return x_82;
}
}
else
{
uint8_t x_83; uint8_t x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; 
x_83 = 1;
x_84 = 0;
x_85 = l_Lean_Expr_mkData(x_29, x_30, x_27, x_31, x_70, x_83, x_83, x_84, x_5);
lean_dec(x_30);
x_86 = lean_unbox_uint64(x_85);
lean_dec(x_85);
x_87 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_2);
lean_ctor_set(x_87, 2, x_3);
lean_ctor_set(x_87, 3, x_4);
lean_ctor_set_uint64(x_87, sizeof(void*)*4, x_86);
return x_87;
}
}
}
else
{
if (x_24 == 0)
{
uint8_t x_88; 
x_88 = 1;
x_32 = x_88;
goto block_68;
}
else
{
if (x_25 == 0)
{
uint8_t x_89; 
x_89 = l_Lean_Expr_hasLevelParam(x_3);
if (x_89 == 0)
{
uint8_t x_90; uint8_t x_91; uint8_t x_92; lean_object* x_93; uint64_t x_94; lean_object* x_95; 
x_90 = l_Lean_Expr_hasLevelParam(x_4);
x_91 = 1;
x_92 = 0;
x_93 = l_Lean_Expr_mkData(x_29, x_30, x_27, x_31, x_91, x_91, x_90, x_92, x_5);
lean_dec(x_30);
x_94 = lean_unbox_uint64(x_93);
lean_dec(x_93);
x_95 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_2);
lean_ctor_set(x_95, 2, x_3);
lean_ctor_set(x_95, 3, x_4);
lean_ctor_set_uint64(x_95, sizeof(void*)*4, x_94);
return x_95;
}
else
{
uint8_t x_96; uint8_t x_97; lean_object* x_98; uint64_t x_99; lean_object* x_100; 
x_96 = 1;
x_97 = 0;
x_98 = l_Lean_Expr_mkData(x_29, x_30, x_27, x_31, x_96, x_96, x_96, x_97, x_5);
lean_dec(x_30);
x_99 = lean_unbox_uint64(x_98);
lean_dec(x_98);
x_100 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_100, 0, x_1);
lean_ctor_set(x_100, 1, x_2);
lean_ctor_set(x_100, 2, x_3);
lean_ctor_set(x_100, 3, x_4);
lean_ctor_set_uint64(x_100, sizeof(void*)*4, x_99);
return x_100;
}
}
else
{
uint8_t x_101; uint8_t x_102; lean_object* x_103; uint64_t x_104; lean_object* x_105; 
x_101 = 1;
x_102 = 0;
x_103 = l_Lean_Expr_mkData(x_29, x_30, x_27, x_31, x_101, x_101, x_101, x_102, x_5);
lean_dec(x_30);
x_104 = lean_unbox_uint64(x_103);
lean_dec(x_103);
x_105 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_105, 0, x_1);
lean_ctor_set(x_105, 1, x_2);
lean_ctor_set(x_105, 2, x_3);
lean_ctor_set(x_105, 3, x_4);
lean_ctor_set_uint64(x_105, sizeof(void*)*4, x_104);
return x_105;
}
}
}
}
else
{
if (x_24 == 0)
{
uint8_t x_106; 
x_106 = 1;
x_32 = x_106;
goto block_68;
}
else
{
if (x_25 == 0)
{
uint8_t x_107; 
x_107 = l_Lean_Expr_hasLevelParam(x_3);
if (x_107 == 0)
{
uint8_t x_108; uint8_t x_109; uint8_t x_110; lean_object* x_111; uint64_t x_112; lean_object* x_113; 
x_108 = l_Lean_Expr_hasLevelParam(x_4);
x_109 = 1;
x_110 = 0;
x_111 = l_Lean_Expr_mkData(x_29, x_30, x_27, x_31, x_109, x_109, x_108, x_110, x_5);
lean_dec(x_30);
x_112 = lean_unbox_uint64(x_111);
lean_dec(x_111);
x_113 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_113, 0, x_1);
lean_ctor_set(x_113, 1, x_2);
lean_ctor_set(x_113, 2, x_3);
lean_ctor_set(x_113, 3, x_4);
lean_ctor_set_uint64(x_113, sizeof(void*)*4, x_112);
return x_113;
}
else
{
uint8_t x_114; uint8_t x_115; lean_object* x_116; uint64_t x_117; lean_object* x_118; 
x_114 = 1;
x_115 = 0;
x_116 = l_Lean_Expr_mkData(x_29, x_30, x_27, x_31, x_114, x_114, x_114, x_115, x_5);
lean_dec(x_30);
x_117 = lean_unbox_uint64(x_116);
lean_dec(x_116);
x_118 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_118, 0, x_1);
lean_ctor_set(x_118, 1, x_2);
lean_ctor_set(x_118, 2, x_3);
lean_ctor_set(x_118, 3, x_4);
lean_ctor_set_uint64(x_118, sizeof(void*)*4, x_117);
return x_118;
}
}
else
{
uint8_t x_119; uint8_t x_120; lean_object* x_121; uint64_t x_122; lean_object* x_123; 
x_119 = 1;
x_120 = 0;
x_121 = l_Lean_Expr_mkData(x_29, x_30, x_27, x_31, x_119, x_119, x_119, x_120, x_5);
lean_dec(x_30);
x_122 = lean_unbox_uint64(x_121);
lean_dec(x_121);
x_123 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_123, 0, x_1);
lean_ctor_set(x_123, 1, x_2);
lean_ctor_set(x_123, 2, x_3);
lean_ctor_set(x_123, 3, x_4);
lean_ctor_set_uint64(x_123, sizeof(void*)*4, x_122);
return x_123;
}
}
}
block_68:
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
uint8_t x_36; uint8_t x_37; lean_object* x_38; uint64_t x_39; lean_object* x_40; 
x_36 = l_Lean_Expr_hasLevelParam(x_4);
x_37 = 0;
x_38 = l_Lean_Expr_mkData(x_29, x_30, x_27, x_31, x_32, x_34, x_36, x_37, x_5);
lean_dec(x_30);
x_39 = lean_unbox_uint64(x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_2);
lean_ctor_set(x_40, 2, x_3);
lean_ctor_set(x_40, 3, x_4);
lean_ctor_set_uint64(x_40, sizeof(void*)*4, x_39);
return x_40;
}
else
{
uint8_t x_41; uint8_t x_42; lean_object* x_43; uint64_t x_44; lean_object* x_45; 
x_41 = 1;
x_42 = 0;
x_43 = l_Lean_Expr_mkData(x_29, x_30, x_27, x_31, x_32, x_34, x_41, x_42, x_5);
lean_dec(x_30);
x_44 = lean_unbox_uint64(x_43);
lean_dec(x_43);
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
uint8_t x_46; uint8_t x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; 
x_46 = 1;
x_47 = 0;
x_48 = l_Lean_Expr_mkData(x_29, x_30, x_27, x_31, x_32, x_34, x_46, x_47, x_5);
lean_dec(x_30);
x_49 = lean_unbox_uint64(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_2);
lean_ctor_set(x_50, 2, x_3);
lean_ctor_set(x_50, 3, x_4);
lean_ctor_set_uint64(x_50, sizeof(void*)*4, x_49);
return x_50;
}
}
else
{
if (x_25 == 0)
{
uint8_t x_51; 
x_51 = l_Lean_Expr_hasLevelParam(x_3);
if (x_51 == 0)
{
uint8_t x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; uint64_t x_56; lean_object* x_57; 
x_52 = l_Lean_Expr_hasLevelParam(x_4);
x_53 = 1;
x_54 = 0;
x_55 = l_Lean_Expr_mkData(x_29, x_30, x_27, x_31, x_32, x_53, x_52, x_54, x_5);
lean_dec(x_30);
x_56 = lean_unbox_uint64(x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_2);
lean_ctor_set(x_57, 2, x_3);
lean_ctor_set(x_57, 3, x_4);
lean_ctor_set_uint64(x_57, sizeof(void*)*4, x_56);
return x_57;
}
else
{
uint8_t x_58; uint8_t x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; 
x_58 = 1;
x_59 = 0;
x_60 = l_Lean_Expr_mkData(x_29, x_30, x_27, x_31, x_32, x_58, x_58, x_59, x_5);
lean_dec(x_30);
x_61 = lean_unbox_uint64(x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_2);
lean_ctor_set(x_62, 2, x_3);
lean_ctor_set(x_62, 3, x_4);
lean_ctor_set_uint64(x_62, sizeof(void*)*4, x_61);
return x_62;
}
}
else
{
uint8_t x_63; uint8_t x_64; lean_object* x_65; uint64_t x_66; lean_object* x_67; 
x_63 = 1;
x_64 = 0;
x_65 = l_Lean_Expr_mkData(x_29, x_30, x_27, x_31, x_32, x_63, x_63, x_64, x_5);
lean_dec(x_30);
x_66 = lean_unbox_uint64(x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_2);
lean_ctor_set(x_67, 2, x_3);
lean_ctor_set(x_67, 3, x_4);
lean_ctor_set_uint64(x_67, sizeof(void*)*4, x_66);
return x_67;
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
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint32_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; 
x_2 = 3;
x_3 = l_Lean_Literal_hash(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
x_5 = 0;
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = 0;
x_9 = l_Lean_Expr_mkData(x_4, x_6, x_5, x_7, x_7, x_7, x_7, x_8, x_7);
x_10 = lean_unbox_uint64(x_9);
lean_dec(x_9);
x_11 = lean_alloc_ctor(9, 1, 8);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set_uint64(x_11, sizeof(void*)*1, x_10);
return x_11;
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
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_mkApp(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
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
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
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
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 1)
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
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isType(x_1);
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedExpr;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_getRevArg_x21___closed__1;
x_3 = lean_unsigned_to_nat(566u);
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
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_1 = x_3;
x_2 = x_8;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_Expr_getRevArg_x21___closed__3;
x_11 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_10);
return x_11;
}
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_appFn_x21___closed__1;
x_3 = lean_unsigned_to_nat(586u);
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
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_appFn_x21___closed__3;
x_4 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_3);
return x_4;
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_appArg_x21___closed__1;
x_3 = lean_unsigned_to_nat(590u);
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
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_appArg_x21___closed__2;
x_4 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_3);
return x_4;
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
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.sortLevel!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sort expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_sortLevel_x21___closed__1;
x_3 = lean_unsigned_to_nat(594u);
x_4 = lean_unsigned_to_nat(17u);
x_5 = l_Lean_Expr_sortLevel_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_sortLevel_x21___closed__3;
x_4 = l_panic___at_Lean_Level_normalize___spec__1(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_sortLevel_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_litValue_x21___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedLiteral;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.litValue!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("literal expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_litValue_x21___closed__1;
x_3 = lean_unsigned_to_nat(598u);
x_4 = lean_unsigned_to_nat(16u);
x_5 = l_Lean_Expr_litValue_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = l_Lean_Expr_litValue_x21___closed__3;
x_4 = l_panic___at_Lean_Expr_litValue_x21___spec__1(x_3);
return x_4;
}
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_constName_x21___closed__1;
x_3 = lean_unsigned_to_nat(617u);
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
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_constName_x21___closed__3;
x_4 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_3);
return x_4;
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_constLevels_x21___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_constLevels_x21___closed__1;
x_3 = lean_unsigned_to_nat(625u);
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
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = l_Lean_Expr_constLevels_x21___closed__2;
x_4 = l_panic___at_Lean_Expr_constLevels_x21___spec__1(x_3);
return x_4;
}
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_bvarIdx_x21___closed__1;
x_3 = lean_unsigned_to_nat(629u);
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
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_bvarIdx_x21___closed__3;
x_4 = l_panic___at_String_toNat_x21___spec__1(x_3);
return x_4;
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_fvarId_x21___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedFVarId;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_fvarId_x21___closed__1;
x_3 = lean_unsigned_to_nat(633u);
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
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = l_Lean_Expr_fvarId_x21___closed__3;
x_4 = l_panic___at_Lean_Expr_fvarId_x21___spec__1(x_3);
return x_4;
}
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_mvarId_x21___closed__1;
x_3 = lean_unsigned_to_nat(637u);
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
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_mvarId_x21___closed__3;
x_4 = l_panic___at_Lean_Level_mvarId_x21___spec__1(x_3);
return x_4;
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_bindingName_x21___closed__1;
x_3 = lean_unsigned_to_nat(642u);
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
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_bindingName_x21___closed__3;
x_5 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_4);
return x_5;
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_bindingDomain_x21___closed__1;
x_3 = lean_unsigned_to_nat(647u);
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
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_bindingDomain_x21___closed__2;
x_5 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_4);
return x_5;
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_bindingBody_x21___closed__1;
x_3 = lean_unsigned_to_nat(652u);
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
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_bindingBody_x21___closed__2;
x_5 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_bindingInfo_x21___spec__1(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_instInhabitedBinderInfo;
x_3 = lean_box(x_2);
x_4 = lean_panic_fn(x_3, x_1);
return x_4;
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_bindingInfo_x21___closed__1;
x_3 = lean_unsigned_to_nat(657u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Expr_bindingName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_3 = (uint8_t)((x_2 << 24) >> 61);
x_4 = lean_box(x_3);
return x_4;
}
case 7:
{
uint64_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_6 = (uint8_t)((x_5 << 24) >> 61);
x_7 = lean_box(x_6);
return x_7;
}
default: 
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = l_Lean_Expr_bindingInfo_x21___closed__2;
x_9 = l_panic___at_Lean_Expr_bindingInfo_x21___spec__1(x_8);
return x_9;
}
}
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_letName_x21___closed__1;
x_3 = lean_unsigned_to_nat(661u);
x_4 = lean_unsigned_to_nat(17u);
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
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_letName_x21___closed__3;
x_4 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_3);
return x_4;
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
static lean_object* _init_l_Lean_Expr_letType_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.letType!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_letType_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_letType_x21___closed__1;
x_3 = lean_unsigned_to_nat(665u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l_Lean_Expr_letName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_letType_x21___closed__2;
x_4 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_letType_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_letValue_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.letValue!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_letValue_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_letValue_x21___closed__1;
x_3 = lean_unsigned_to_nat(669u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Expr_letName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_letValue_x21___closed__2;
x_4 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_letValue_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_letBody_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.letBody!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_letBody_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_letBody_x21___closed__1;
x_3 = lean_unsigned_to_nat(673u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Expr_letName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_letBody_x21___closed__2;
x_4 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_letBody_x21(x_1);
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_mdataExpr_x21___closed__1;
x_3 = lean_unsigned_to_nat(681u);
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
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_mdataExpr_x21___closed__3;
x_4 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_3);
return x_4;
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
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.projExpr!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("proj expression expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_projExpr_x21___closed__1;
x_3 = lean_unsigned_to_nat(685u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Expr_projExpr_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_projExpr_x21___closed__3;
x_4 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_projExpr_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_projIdx_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.projIdx!");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_projIdx_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_projIdx_x21___closed__1;
x_3 = lean_unsigned_to_nat(689u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Expr_projExpr_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_projIdx_x21___closed__2;
x_4 = l_panic___at_String_toNat_x21___spec__1(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_projIdx_x21(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Array_reverse___rarg(x_2);
x_4 = l_Lean_Expr_betaRev(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_beta___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_beta(x_1, x_2);
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_updateApp_x21___closed__1;
x_3 = lean_unsigned_to_nat(966u);
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
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Expr_updateApp_x21___closed__2;
x_12 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_11);
return x_12;
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_updateConst_x21___closed__1;
x_3 = lean_unsigned_to_nat(975u);
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
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_Expr_updateConst_x21___closed__2;
x_11 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_10);
return x_11;
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_updateSort_x21___closed__1;
x_3 = lean_unsigned_to_nat(984u);
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
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = l_Lean_Expr_updateSort_x21___closed__3;
x_10 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_9);
return x_10;
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_updateMData_x21___closed__1;
x_3 = lean_unsigned_to_nat(1001u);
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
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_Expr_updateMData_x21___closed__3;
x_11 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_10);
return x_11;
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_updateProj_x21___closed__1;
x_3 = lean_unsigned_to_nat(1006u);
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
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Expr_updateProj_x21___closed__3;
x_12 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_11);
return x_12;
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_updateForall_x21___closed__1;
x_3 = lean_unsigned_to_nat(1015u);
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
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = l_Lean_Expr_updateForall_x21___closed__3;
x_14 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_13);
return x_14;
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_updateForallE_x21___closed__1;
x_3 = lean_unsigned_to_nat(1020u);
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
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Expr_updateForallE_x21___closed__2;
x_16 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_15);
return x_16;
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_updateLambda_x21___closed__1;
x_3 = lean_unsigned_to_nat(1029u);
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
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = l_Lean_Expr_updateLambda_x21___closed__3;
x_14 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_13);
return x_14;
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_updateLambdaE_x21___closed__1;
x_3 = lean_unsigned_to_nat(1034u);
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
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Expr_updateLambdaE_x21___closed__2;
x_16 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_15);
return x_16;
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
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_updateLet_x21___closed__1;
x_3 = lean_unsigned_to_nat(1043u);
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
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Expr_updateLet_x21___closed__2;
x_15 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_14);
return x_15;
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
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 0;
x_9 = l_Lean_Expr_setPPExplicit(x_5, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
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
x_15 = l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicit___spec__1(x_13, x_14, x_11);
x_16 = l_Lean_mkAppN(x_4, x_15);
x_17 = 1;
x_18 = l_Lean_Expr_setPPExplicit(x_16, x_17);
return x_18;
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
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; size_t x_9; size_t x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Expr_hasMVar(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
if (x_8 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = 0;
x_12 = l_Lean_Expr_setPPExplicit(x_5, x_11);
x_13 = lean_array_uset(x_7, x_2, x_12);
x_2 = x_10;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_10;
x_3 = x_15;
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
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
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
x_15 = l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicitForExposingMVars___spec__1(x_13, x_14, x_11);
x_16 = l_Lean_mkAppN(x_4, x_15);
x_17 = 1;
x_18 = l_Lean_Expr_setPPExplicit(x_16, x_17);
return x_18;
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
static lean_object* _init_l_Lean_mkInaccessible___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_inaccessible");
return x_1;
}
}
static lean_object* _init_l_Lean_mkInaccessible___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkInaccessible___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkInaccessible___closed__2;
x_3 = l_Lean_mkAnnotation(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkInaccessible___closed__2;
x_3 = l_Lean_annotation_x3f(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_inaccessible_x3f(x_1);
lean_dec(x_1);
return x_2;
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_KVMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Level(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_KVMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Level(builtin, lean_io_mk_world());
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
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__1 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__1);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__2 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__2);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__3 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__3();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__3);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__4);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__5);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__6 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__6();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__6);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__7 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__7();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__7);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__8 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__8();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_107____closed__8);
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
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__1 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__1);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__2 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__2);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__3 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__3();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__3);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__4 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__4();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__4);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__5 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__5();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__5);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__6 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__6();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__6);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__7 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__7();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__7);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__8 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__8();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__8);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__9 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__9();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__9);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__10 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__10();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__10);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__11 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__11();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__11);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__12 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__12();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__12);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__13 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__13();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__13);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__14 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__14();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__14);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__15 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__15();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__15);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__16 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__16();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__16);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__17 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__17();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__17);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__18 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__18();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__18);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__19 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__19();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__19);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__20 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__20();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__20);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__21 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__21();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__21);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__22 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__22();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__22);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__23 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__23();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__23);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__24 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__24();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__24);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__25 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__25();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__25);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__26 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__26();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__26);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__27 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__27();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__27);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__28 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__28();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__28);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__29 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__29();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__29);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__30 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__30();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_372____closed__30);
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
l_panic___at_Lean_Expr_mkData___spec__1___boxed__const__1 = _init_l_panic___at_Lean_Expr_mkData___spec__1___boxed__const__1();
lean_mark_persistent(l_panic___at_Lean_Expr_mkData___spec__1___boxed__const__1);
l_Lean_Expr_mkData___closed__1 = _init_l_Lean_Expr_mkData___closed__1();
lean_mark_persistent(l_Lean_Expr_mkData___closed__1);
l_Lean_Expr_mkData___closed__2 = _init_l_Lean_Expr_mkData___closed__2();
lean_mark_persistent(l_Lean_Expr_mkData___closed__2);
l_Lean_Expr_mkData___closed__3 = _init_l_Lean_Expr_mkData___closed__3();
lean_mark_persistent(l_Lean_Expr_mkData___closed__3);
l_Lean_Expr_mkData___closed__4 = _init_l_Lean_Expr_mkData___closed__4();
lean_mark_persistent(l_Lean_Expr_mkData___closed__4);
l_Lean_Expr_mkData___closed__5 = _init_l_Lean_Expr_mkData___closed__5();
lean_mark_persistent(l_Lean_Expr_mkData___closed__5);
l_Lean_instReprData__1___lambda__2___closed__1 = _init_l_Lean_instReprData__1___lambda__2___closed__1();
lean_mark_persistent(l_Lean_instReprData__1___lambda__2___closed__1);
l_Lean_instReprData__1___lambda__2___closed__2 = _init_l_Lean_instReprData__1___lambda__2___closed__2();
lean_mark_persistent(l_Lean_instReprData__1___lambda__2___closed__2);
l_Lean_instReprData__1___lambda__3___closed__1 = _init_l_Lean_instReprData__1___lambda__3___closed__1();
lean_mark_persistent(l_Lean_instReprData__1___lambda__3___closed__1);
l_Lean_instReprData__1___lambda__3___closed__2 = _init_l_Lean_instReprData__1___lambda__3___closed__2();
lean_mark_persistent(l_Lean_instReprData__1___lambda__3___closed__2);
l_Lean_instReprData__1___lambda__4___closed__1 = _init_l_Lean_instReprData__1___lambda__4___closed__1();
lean_mark_persistent(l_Lean_instReprData__1___lambda__4___closed__1);
l_Lean_instReprData__1___lambda__5___closed__1 = _init_l_Lean_instReprData__1___lambda__5___closed__1();
lean_mark_persistent(l_Lean_instReprData__1___lambda__5___closed__1);
l_Lean_instReprData__1___lambda__6___closed__1 = _init_l_Lean_instReprData__1___lambda__6___closed__1();
lean_mark_persistent(l_Lean_instReprData__1___lambda__6___closed__1);
l_Lean_instReprData__1___lambda__7___closed__1 = _init_l_Lean_instReprData__1___lambda__7___closed__1();
lean_mark_persistent(l_Lean_instReprData__1___lambda__7___closed__1);
l_Lean_instReprData__1___closed__1 = _init_l_Lean_instReprData__1___closed__1();
lean_mark_persistent(l_Lean_instReprData__1___closed__1);
l_Lean_instReprData__1___closed__2 = _init_l_Lean_instReprData__1___closed__2();
lean_mark_persistent(l_Lean_instReprData__1___closed__2);
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
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__2___closed__1 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____lambda__2___closed__1);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__1 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__1);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__2 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__2);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__3 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__3();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__3);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__4 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__4();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__4);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__5 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__5();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__5);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__6 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__6();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__6);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__7 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__7();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__7);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__8 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__8();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__8);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__9 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__9();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__9);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__10 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__10();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__10);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__11 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__11();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__11);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__12 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__12();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__12);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__13 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__13();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__13);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__14 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__14();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__14);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__15 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__15();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__15);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__16 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__16();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__16);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__17 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__17();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__17);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__18 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__18();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__18);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__19 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__19();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__19);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__20 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__20();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__20);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__21 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__21();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__21);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__22 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__22();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__22);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__23 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__23();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__23);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__24 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__24();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__24);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__25 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__25();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__25);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__26 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__26();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__26);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__27 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__27();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__27);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__28 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__28();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__28);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__29 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__29();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__29);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__30 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__30();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__30);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__31 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__31();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__31);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__32 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__32();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__32);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__33 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__33();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__33);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__34 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__34();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__34);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__35 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__35();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__35);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__36 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__36();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__36);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__37 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__37();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__37);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__38 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__38();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__38);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__39 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__39();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__39);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__40 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__40();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__40);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__41 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__41();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__41);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__42 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__42();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__42);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__43 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__43();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__43);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__44 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__44();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__44);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__45 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__45();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__45);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__46 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__46();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__46);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__47 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__47();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_2210____closed__47);
l_Lean_instReprExpr___closed__1 = _init_l_Lean_instReprExpr___closed__1();
lean_mark_persistent(l_Lean_instReprExpr___closed__1);
l_Lean_instReprExpr = _init_l_Lean_instReprExpr();
lean_mark_persistent(l_Lean_instReprExpr);
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
l_Lean_Expr_sortLevel_x21___closed__1 = _init_l_Lean_Expr_sortLevel_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_sortLevel_x21___closed__1);
l_Lean_Expr_sortLevel_x21___closed__2 = _init_l_Lean_Expr_sortLevel_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_sortLevel_x21___closed__2);
l_Lean_Expr_sortLevel_x21___closed__3 = _init_l_Lean_Expr_sortLevel_x21___closed__3();
lean_mark_persistent(l_Lean_Expr_sortLevel_x21___closed__3);
l_Lean_Expr_litValue_x21___closed__1 = _init_l_Lean_Expr_litValue_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_litValue_x21___closed__1);
l_Lean_Expr_litValue_x21___closed__2 = _init_l_Lean_Expr_litValue_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_litValue_x21___closed__2);
l_Lean_Expr_litValue_x21___closed__3 = _init_l_Lean_Expr_litValue_x21___closed__3();
lean_mark_persistent(l_Lean_Expr_litValue_x21___closed__3);
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
l_Lean_Expr_letType_x21___closed__1 = _init_l_Lean_Expr_letType_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_letType_x21___closed__1);
l_Lean_Expr_letType_x21___closed__2 = _init_l_Lean_Expr_letType_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_letType_x21___closed__2);
l_Lean_Expr_letValue_x21___closed__1 = _init_l_Lean_Expr_letValue_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_letValue_x21___closed__1);
l_Lean_Expr_letValue_x21___closed__2 = _init_l_Lean_Expr_letValue_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_letValue_x21___closed__2);
l_Lean_Expr_letBody_x21___closed__1 = _init_l_Lean_Expr_letBody_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_letBody_x21___closed__1);
l_Lean_Expr_letBody_x21___closed__2 = _init_l_Lean_Expr_letBody_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_letBody_x21___closed__2);
l_Lean_Expr_mdataExpr_x21___closed__1 = _init_l_Lean_Expr_mdataExpr_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_mdataExpr_x21___closed__1);
l_Lean_Expr_mdataExpr_x21___closed__2 = _init_l_Lean_Expr_mdataExpr_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_mdataExpr_x21___closed__2);
l_Lean_Expr_mdataExpr_x21___closed__3 = _init_l_Lean_Expr_mdataExpr_x21___closed__3();
lean_mark_persistent(l_Lean_Expr_mdataExpr_x21___closed__3);
l_Lean_Expr_projExpr_x21___closed__1 = _init_l_Lean_Expr_projExpr_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_projExpr_x21___closed__1);
l_Lean_Expr_projExpr_x21___closed__2 = _init_l_Lean_Expr_projExpr_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_projExpr_x21___closed__2);
l_Lean_Expr_projExpr_x21___closed__3 = _init_l_Lean_Expr_projExpr_x21___closed__3();
lean_mark_persistent(l_Lean_Expr_projExpr_x21___closed__3);
l_Lean_Expr_projIdx_x21___closed__1 = _init_l_Lean_Expr_projIdx_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_projIdx_x21___closed__1);
l_Lean_Expr_projIdx_x21___closed__2 = _init_l_Lean_Expr_projIdx_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_projIdx_x21___closed__2);
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
l_Lean_mkInaccessible___closed__1 = _init_l_Lean_mkInaccessible___closed__1();
lean_mark_persistent(l_Lean_mkInaccessible___closed__1);
l_Lean_mkInaccessible___closed__2 = _init_l_Lean_mkInaccessible___closed__2();
lean_mark_persistent(l_Lean_mkInaccessible___closed__2);
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
