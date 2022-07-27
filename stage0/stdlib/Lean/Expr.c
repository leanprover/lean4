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
LEAN_EXPORT lean_object* l_Lean_Expr_bindingInfo_x21(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(lean_object*, lean_object*);
static lean_object* l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__11;
static lean_object* l_Lean_mkDecIsFalse___closed__2;
static lean_object* l_Lean_Expr_bvarIdx_x21___closed__3;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instReprData__1___lambda__3___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__3;
static lean_object* l_Lean_mkNatLit___closed__4;
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isCharLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_litValue_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isNatLit(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__20;
static lean_object* l_Lean_Expr_replaceFVar___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__33;
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Expr_projExpr_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object*);
static lean_object* l_Lean_instReprData__1___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__22;
static lean_object* l_Lean_Expr_bindingDomain_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_abstract___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_instReprExpr___closed__1;
static lean_object* l_Lean_Expr_getRevArg_x21___closed__1;
static lean_object* l_Lean_instReprBinderInfo___closed__1;
static lean_object* l_Lean_mkNatLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__37;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Expr_traverseApp___spec__1(lean_object*);
static lean_object* l_Lean_Expr_letBody_x21___closed__1;
static lean_object* l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__3;
static lean_object* l_Lean_mkDecIsTrue___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_withApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isMData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letBody_x21___boxed(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
static lean_object* l_Lean_mkDecIsFalse___closed__1;
static lean_object* l_Lean_mkAnd___closed__2;
uint64_t lean_uint8_to_uint64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__6;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_mkEM___closed__1;
static lean_object* l_Lean_Expr_litValue_x21___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkSimpleThunkType___closed__3;
LEAN_EXPORT uint8_t l_Lean_Expr_isProp(lean_object*);
static lean_object* l_Lean_Expr_instHashableExpr___closed__1;
static lean_object* l_Lean_mkInaccessible___closed__1;
LEAN_EXPORT uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1929_(lean_object*);
static lean_object* l_Lean_Expr_litValue_x21___closed__1;
uint32_t lean_uint8_to_uint32(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarId(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_letBody_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object*);
static lean_object* l_Lean_Expr_projIdx_x21___closed__2;
lean_object* l_Lean_Level_succ___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedBody(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_RBMap_instForInRBMapProd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkAppN___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkEM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_isLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_approxDepth___boxed(lean_object*);
uint64_t lean_uint64_add(uint64_t, uint64_t);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__25;
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_bindingInfo_x21___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instHashableExprStructEq;
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_bool_to_uint64(uint8_t);
static lean_object* l_Lean_mkNatLit___closed__9;
LEAN_EXPORT uint8_t l_Lean_Expr_isArrow(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkOr(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__18;
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_instantiateLevelParams___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_letValue_x21___closed__2;
static lean_object* l_Lean_Expr_mkAppData___closed__4;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__15;
LEAN_EXPORT lean_object* l_Lean_Expr_isOptParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkForallEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__30;
LEAN_EXPORT lean_object* l_Lean_mkLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppRevArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParamEx___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Expr_Data_hash(uint64_t);
LEAN_EXPORT lean_object* l_Lean_mkLHSGoal(lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
static lean_object* l_Lean_mkDecIsTrue___closed__5;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__5;
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_instFVarIdSetEmptyCollection;
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_etaExpandedAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hash___boxed(lean_object*);
static lean_object* l_Lean_Expr_appFn_x21_x27___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1872____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object*, lean_object*);
static lean_object* l_Lean_Literal_type___closed__5;
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object*);
static lean_object* l_Lean_instReprData__1___lambda__3___closed__2;
static lean_object* l_Lean_Expr_ctorName___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_litValue_x21___closed__3;
static lean_object* l_Lean_Expr_constName_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_mvarId_x21___closed__1;
uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21___boxed(lean_object*);
static lean_object* l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Expr_isArrow___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__17;
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_mkData___closed__3;
LEAN_EXPORT lean_object* l_Lean_annotation_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder(uint64_t, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit(lean_object*, uint8_t);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubst___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_appArg_x21_x27___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfoEx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_binderInfo___boxed(lean_object*);
static lean_object* l_Lean_Expr_ctorName___closed__2;
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVarInExplicitDomain(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVarEx___boxed(lean_object*);
uint64_t l_Lean_Level_hash(lean_object*);
static lean_object* l_Lean_Expr_ctorName___closed__8;
LEAN_EXPORT lean_object* l_Lean_Expr_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAutoParam___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_mkData___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object*, lean_object*);
static lean_object* l_Lean_instForInMVarIdMapProdMVarId___closed__1;
static lean_object* l_Lean_Expr_mvarId_x21___closed__2;
static lean_object* l_Lean_mkSimpleThunkType___closed__1;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object*);
static lean_object* l_Lean_Expr_bindingBody_x21___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__7;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toCtorIdx(uint8_t);
static lean_object* l_Lean_Expr_ctorName___closed__4;
LEAN_EXPORT uint8_t l_Lean_Expr_isBVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarId(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
static lean_object* l_Lean_Literal_type___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Expr_traverseApp___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Expr_traverseApp___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLetFunAnnotation(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_appFn_x21_x27___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1;
LEAN_EXPORT uint8_t lean_expr_has_level_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_ExprStructEq_instBEqExprStructEq___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__5;
static lean_object* l_Lean_ExprStructEq_instHashableExprStructEq___closed__1;
static lean_object* l_Lean_Expr_appFn_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_instMVarIdSetInhabited;
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object*);
uint8_t l_ptrEqList___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_instantiateLevelParams___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_getAppArgs___closed__1;
static lean_object* l_Lean_mkNatLit___closed__2;
uint8_t l_Lean_Level_hasParam(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__2;
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1872_(lean_object*, lean_object*);
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__10;
LEAN_EXPORT uint8_t l_Lean_instDecidableLtLiteralInstLTLiteral(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_Expr_const___override___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167_(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_fvarId_x21___closed__2;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2;
uint8_t lean_expr_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_sortLevel_x21___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_letName_x21___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__4;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2;
static lean_object* l_Lean_Expr_projExpr_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mdataExpr_x21(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_letName_x21___boxed(lean_object*);
static lean_object* l_Lean_Expr_projExpr_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForBinder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_mkAppRev___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__27;
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_containsFVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_forall(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_expr_instantiate(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_bindingName_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_setOption(lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instBEqExprStructEq;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__10;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__14;
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVarEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprLiteral;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__39;
LEAN_EXPORT lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object*);
static lean_object* l_Lean_Expr_setPPExplicit___closed__4;
uint16_t lean_uint16_add(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprFVarId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__19;
static lean_object* l_Lean_Expr_updateLambdaE_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkOr___closed__1;
static lean_object* l_Lean_instReprData__1___lambda__5___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__23;
uint32_t lean_uint32_add(uint32_t, uint32_t);
static lean_object* l_Lean_Expr_sortLevel_x21___closed__2;
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_Expr_const___override___spec__2(uint8_t, lean_object*);
static lean_object* l_Lean_instReprData__1___lambda__4___closed__1;
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_natLit_x3f___boxed(lean_object*);
lean_object* l_Lean_simpLevelIMax_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object*, lean_object*);
static lean_object* l_Lean_mkOr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_Data_approxDepth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDecIsTrue(lean_object*, lean_object*);
extern uint64_t l_instInhabitedUInt64;
LEAN_EXPORT lean_object* l_Lean_mkLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__10;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__32;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at_Lean_Expr_setPPExplicit___spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_letFunAnnotation_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isMVar___boxed(lean_object*);
static lean_object* l_Lean_instBEqMVarId___closed__1;
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasExprMVar(uint64_t);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__28;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_type(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubstArray(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBTree_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21___boxed(lean_object*);
static lean_object* l_Lean_Expr_bindingName_x21___closed__3;
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVarInExplicitDomain___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isConstOf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqBinderInfo;
LEAN_EXPORT uint64_t l_Lean_BinderInfo_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__7;
static lean_object* l_Lean_Expr_letName_x21___closed__3;
static lean_object* l_Lean_mkEM___closed__3;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113_(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__24;
static lean_object* l_Lean_instHashableFVarId___closed__1;
static lean_object* l_Lean_Expr_updateLambdaE_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprFVarId___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_getOptParamDefault_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___rarg___lambda__1___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__13;
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
static lean_object* l_Lean_instReprData__1___lambda__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_expr_mvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses(lean_object*, uint8_t);
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_constName_x21___closed__3;
static lean_object* l_Lean_Literal_type___closed__6;
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instCoeExprExprStructEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionFVarIdMap(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__21;
LEAN_EXPORT lean_object* l_Lean_Expr_projExpr_x21(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__3;
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLevelParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_31____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFVarIdSetInhabited;
static lean_object* l_Lean_Expr_sortLevel_x21___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2;
static lean_object* l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__6;
LEAN_EXPORT uint8_t lean_expr_has_mvar(lean_object*);
static lean_object* l_Lean_Expr_mkData___closed__7;
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_2138____boxed(lean_object*);
static lean_object* l_Lean_mkNatLit___closed__6;
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__7;
static lean_object* l_Lean_Expr_ctorName___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_BinderInfo_noConfusion___rarg___closed__1;
static lean_object* l_Lean_Expr_bindingBody_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__24;
lean_object* l_panic___at_Lean_Level_normalize___spec__1(lean_object*);
static lean_object* l_Lean_isLHSGoal_x3f___closed__1;
LEAN_EXPORT uint8_t lean_expr_binder_info(lean_object*);
static lean_object* l_Lean_Expr_mkData___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_letFunAnnotation_x3f___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1;
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isStrictImplicit(uint8_t);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__29;
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRangeEx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
LEAN_EXPORT uint8_t lean_is_out_param(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_abstractRange___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint64_to_uint32(uint64_t);
static lean_object* l_Lean_instHashableMVarId___closed__1;
lean_object* l_Lean_simpLevelMax_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___rarg(lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLiteral;
static lean_object* l_Lean_Expr_instToStringExpr___closed__1;
LEAN_EXPORT uint64_t l_Lean_Expr_data(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__2;
LEAN_EXPORT lean_object* l_Lean_instReprMVarId;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubstArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inaccessible_x3f(lean_object*);
static lean_object* l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__5;
uint16_t lean_uint8_to_uint16(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instMVarIdSetEmptyCollection;
LEAN_EXPORT uint8_t l_Lean_Expr_isBinding(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
static uint32_t l_Lean_Expr_mkAppData___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__6;
static lean_object* l_Lean_Expr_appArg_x21_x27___closed__2;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkDecIsTrue___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAutoParamTactic_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicitForExposingMVars___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_instReprMVarId___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__14;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__28;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__29;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasFVar(uint64_t);
static lean_object* l_Lean_Expr_instBEqExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVarEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Expr_approxDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicitForExposingMVars(lean_object*);
static lean_object* l_Lean_Expr_fvarId_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_isType___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instHashableExpr;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__22;
static lean_object* l_Lean_mkDecIsTrue___closed__2;
LEAN_EXPORT uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_mvarId_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Literal_type___boxed(lean_object*);
static lean_object* l_Lean_Literal_type___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__1;
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_constLevels_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_bindingDomain_x21___closed__1;
static lean_object* l_Lean_mkInaccessible___closed__2;
LEAN_EXPORT lean_object* l_Lean_isLHSGoal_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Expr_getRevArg_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__8;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ctorName___closed__3;
LEAN_EXPORT uint64_t l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_2138_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprExpr;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__25;
static lean_object* l_Lean_isLHSGoal_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_natLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__30;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__5;
LEAN_EXPORT lean_object* l_Lean_mkAppRange(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_isCharLit___closed__3;
static lean_object* l_Lean_mkEM___closed__5;
static lean_object* l_Lean_mkOr___closed__2;
static lean_object* l_Lean_Expr_mkAppData___closed__2;
static lean_object* l_Lean_Expr_mdataExpr_x21___closed__3;
static lean_object* l_Lean_Literal_type___closed__4;
static lean_object* l_Lean_mkDecIsTrue___closed__4;
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelMVar(uint64_t);
lean_object* lean_expr_dbg_to_string(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Expr_traverseApp___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet(uint64_t, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
static lean_object* l_Lean_mkSimpleThunk___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instReprData__1___lambda__7___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Expr_const___override___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Literal_type___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_mkDataForLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_31_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLetFun___boxed(lean_object*);
static lean_object* l_Lean_mkSimpleThunk___closed__1;
lean_object* l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__23;
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_appFn_x21___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isConst(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__13;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__2;
LEAN_EXPORT uint8_t l_Lean_Expr_hasLevelMVar(lean_object*);
static lean_object* l_Lean_Expr_mkAppData___closed__5;
LEAN_EXPORT lean_object* lean_expr_mk_let(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_fvarId_x21___closed__3;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__3;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasFVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isLetFun(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqData__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isAuxDecl(uint8_t);
static lean_object* l_Lean_Expr_bindingName_x21___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasLevelMVar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_nonDepLet(uint64_t);
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint64_t lean_uint64_land(uint64_t, uint64_t);
static lean_object* l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__4;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__31;
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableMVarId;
static lean_object* l_Lean_Expr_mkAppData___closed__3;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__35;
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_constName_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__4(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkDecIsFalse(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__1;
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_Expr_const___override___spec__3___boxed(lean_object*, lean_object*);
static lean_object* l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__9;
uint8_t lean_expr_quick_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object*);
static lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__9;
LEAN_EXPORT uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_letValue_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MData_empty;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object*);
LEAN_EXPORT uint64_t l_Lean_ExprStructEq_hash(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isAutoParam(lean_object*);
static lean_object* l_Lean_Expr_getAutoParamTactic_x3f___closed__2;
LEAN_EXPORT uint8_t l_Lean_Expr_isLambda(lean_object*);
static uint64_t l_Lean_Expr_mkAppData___closed__6;
static lean_object* l_Lean_instInhabitedLiteral___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_ctorName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceFVarId(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1929____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object*);
static lean_object* l_Lean_Expr_setPPExplicit___closed__1;
static lean_object* l_Lean_Expr_setPPExplicit___closed__2;
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isImplicit(uint8_t);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__19;
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPExplicit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__21;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_mkData___spec__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Expr_setAppPPExplicit(lean_object*);
static lean_object* l_Lean_Expr_ctorName___closed__9;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkNatLit___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_bindingInfo_x21___spec__1(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__38;
static lean_object* l_Lean_Expr_mkData___closed__6;
LEAN_EXPORT uint8_t l_Lean_instInhabitedBinderInfo;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__3;
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__6;
LEAN_EXPORT lean_object* l_Lean_instBEqFVarId;
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarId;
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isType(lean_object*);
static lean_object* l_Lean_mkNatLit___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarId;
LEAN_EXPORT lean_object* l_Lean_Expr_isProj___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__7(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_mkData___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getOptParamDefault_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqMVarId;
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqMVarId____x40_Lean_Expr___hyg_2081_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Expr_traverseApp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1;
static lean_object* l_Lean_Expr_getOptParamDefault_x3f___closed__1;
LEAN_EXPORT uint8_t l_Lean_Expr_isMVar(lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_fvar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__8;
uint8_t lean_uint64_to_uint8(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_setPPExplicit___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_hasMVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object*);
static lean_object* l_Lean_Expr_constLevels_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Literal_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkLambdaEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT uint64_t l_Lean_instInhabitedData__1;
static lean_object* l_Lean_instBEqLiteral___closed__1;
LEAN_EXPORT lean_object* l_Lean_instHashableBinderInfo;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object*);
extern lean_object* l_Lean_KVMap_empty;
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__5(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_instantiateLevelParamsArray___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_Expr_const___override___spec__3(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_looseBVarRange___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_noConfusion(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__11;
static lean_object* l_Lean_Expr_bvarIdx_x21___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__20;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isStrictImplicit___boxed(lean_object*);
static lean_object* l_Lean_mkNatLit___closed__10;
static lean_object* l_Lean_mkAnd___closed__1;
lean_object* l___private_Lean_Data_KVMap_0__Lean_reprKVMap____x40_Lean_Data_KVMap___hyg_877_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withApp___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__8;
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getParamSubst(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__6;
LEAN_EXPORT lean_object* l_Lean_Expr_binderInfo___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__17;
static lean_object* l_Lean_instInhabitedExpr___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Literal_lt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_KVMap_insertCore(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_appArg_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_instReprMVarId__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__27;
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_projIdx_x21___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__16;
static lean_object* l_Lean_Expr_appFn_x21___closed__2;
uint64_t lean_uint64_lor(uint64_t, uint64_t);
static lean_object* l_Lean_mkNatLit___closed__5;
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasExprMVar___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__4;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2;
LEAN_EXPORT lean_object* l_Lean_instReprBinderInfo;
LEAN_EXPORT lean_object* l_Lean_instReprMVarId__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_liftLooseBVars___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_bvarIdx_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_appArg_x21___closed__1;
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_hasLevelParam(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_dbgToString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isForall___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isMData___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isProp___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_962_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isStringLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppRev(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__9;
LEAN_EXPORT lean_object* l_Lean_Expr_quickLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instToStringExpr;
static lean_object* l_Lean_mkEM___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint32_to_uint64(uint32_t);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__6(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instToStringExprStructEq___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkSimpleThunkType___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicit___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isAuxDecl___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__11;
static lean_object* l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Expr_instantiateLevelParamsArray___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__34;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_setPPUniverses___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiate1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instReprData__1___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__3;
static lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_isSort___boxed(lean_object*);
static lean_object* l_Lean_Expr_isOutParam___closed__1;
uint8_t lean_uint16_to_uint8(uint16_t);
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_mkData___closed__4;
lean_object* l_panic___at_Lean_TSyntax_getNat___spec__1(lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_hash___boxed(lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
static lean_object* l_Lean_instReprData__1___lambda__2___closed__1;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_isBVar___boxed(lean_object*);
static lean_object* l_Lean_instHashableLiteral___closed__1;
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_litValue_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__3(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_letType_x21___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicitForExposingMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__2;
LEAN_EXPORT lean_object* l_Lean_instFVarIdHashSetInhabited;
static lean_object* l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__3;
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_instForInFVarIdSetFVarId___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_letType_x21___boxed(lean_object*);
static lean_object* l_Lean_Expr_letType_x21___closed__2;
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isStringLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT uint64_t lean_expr_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_hasFVar___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__2;
LEAN_EXPORT uint8_t l_Lean_Expr_isProj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instFVarIdHashSetEmptyCollection;
static lean_object* l_Lean_instReprLiteral___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(uint8_t, uint8_t);
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
static lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__12;
LEAN_EXPORT uint64_t l_List_foldl___at_Lean_Expr_const___override___spec__1(uint64_t, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__2;
static lean_object* l_Lean_Expr_ctorName___closed__6;
LEAN_EXPORT lean_object* l_Lean_mkAnd(lean_object*, lean_object*);
LEAN_EXPORT uint32_t lean_expr_loose_bvar_range(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_inferImplicit(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_instBEqFVarId___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqData__1(uint64_t, uint64_t);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_mkAppN___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_projIdx_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInFVarIdSetFVarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_mkData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_instToStringExprStructEq(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_patternRefAnnotationKey;
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BinderInfo_isExplicit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getForallBody(lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__18;
LEAN_EXPORT lean_object* l_Lean_instDecidableLtLiteralInstLTLiteral___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
static lean_object* l_Lean_Expr_mkData___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_hashEx___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__16;
static lean_object* l_Lean_mkDecIsFalse___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___at_Lean_Expr_setPPExplicit___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAtomic___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_Data_nonDepLet___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__8;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__9;
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__15;
LEAN_EXPORT lean_object* l_Lean_instInhabitedFVarIdMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Level_instantiateParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStrLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_sortLevel_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_etaExpandedStrict_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ctorName___closed__11;
static lean_object* l_Lean_mkNot___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_setAppPPExplicit___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_letValue_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_instReprData__1(uint64_t, lean_object*);
static lean_object* l_Lean_mkLHSGoal___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__26;
LEAN_EXPORT lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__26;
LEAN_EXPORT lean_object* lean_lit_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqLiteral;
LEAN_EXPORT lean_object* l_Lean_Expr_getArgD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_mkLetFunAnnotation___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqMVarId____x40_Lean_Expr___hyg_2081____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_instBEqBinderInfo___closed__1;
static lean_object* l_Lean_Expr_isCharLit___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_setOption___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__36;
LEAN_EXPORT uint64_t l_Lean_BinderInfo_hash(uint8_t);
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1;
static lean_object* l_Lean_Expr_setPPUniverses___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT uint8_t l_Lean_Expr_Data_approxDepth(uint64_t);
LEAN_EXPORT lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_mdataExpr_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkApp10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkNot___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_isApp___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__1;
LEAN_EXPORT lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__2(lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasFVar(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__1;
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Expr_consumeMData___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_equal___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Literal_lt(lean_object*, lean_object*);
static lean_object* l_Lean_mkLetFunAnnotation___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__11;
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object*);
static lean_object* l_Lean_mkNot___closed__2;
LEAN_EXPORT lean_object* l_Lean_BinderInfo_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isLambda___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_constName_x21(lean_object*);
static lean_object* l_Lean_Expr_updateForallE_x21___closed__2;
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__7;
lean_object* lean_expr_instantiate_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_fvarId_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_lowerLooseBVars___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instReprData__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_mvarId_x21___spec__1(lean_object*);
static lean_object* l_Lean_Expr_getRevArg_x21___closed__2;
static lean_object* l_Lean_Expr_updateForallE_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instFVarIdHashSetInhabited___closed__1;
static lean_object* l_Lean_Expr_isOutParam___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_isConst___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__10;
LEAN_EXPORT lean_object* l_Lean_mkInaccessible(lean_object*);
static lean_object* l_Lean_Expr_mdataExpr_x21___closed__1;
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isNatLit___boxed(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371____boxed(lean_object*, lean_object*);
lean_object* l_List_mapTRAux___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isSort(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isLet(lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isLet___boxed(lean_object*);
static lean_object* l_Lean_Expr_bindingInfo_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
static lean_object* l_Lean_Expr_isCharLit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_isCharLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Expr_Data_looseBVarRange(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Expr_setPPUniverses___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__12;
LEAN_EXPORT uint8_t l_Lean_Expr_containsFVar(lean_object*, lean_object*);
static lean_object* l_Lean_mkAnnotation___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_mkData(uint64_t, lean_object*, uint32_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
static lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__12;
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev_go(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_expr_has_level_param(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object*);
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
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Literal.natVal", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__2;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Literal.strVal", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__7;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113_(lean_object* x_1, lean_object* x_2) {
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
x_8 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__3;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
if (x_5 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
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
x_15 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
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
x_25 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__8;
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
if (x_22 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
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
x_32 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprLiteral___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____boxed), 2, 0);
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
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(uint8_t x_1, uint8_t x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instBEqBinderInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371____boxed), 2, 0);
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
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.BinderInfo.default", 23);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__2;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__3;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__2;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__5;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.BinderInfo.implicit", 24);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__8;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__10() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__9;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__8;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.BinderInfo.strictImplicit", 30);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__14;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__16() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__15;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__14;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__18() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__17;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.BinderInfo.instImplicit", 28);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__20;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__22() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__21;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__20;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__24() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__23;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.BinderInfo.auxDecl", 23);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__25;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__26;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__28() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__27;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
x_2 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__26;
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__30() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__29;
x_2 = 0;
x_3 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387_(uint8_t x_1, lean_object* x_2) {
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
x_5 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__4;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__6;
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
x_11 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__10;
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__12;
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
x_17 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__16;
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__18;
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
x_23 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__22;
x_24 = l_Repr_addAppParen(x_23, x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__24;
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
x_29 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__28;
x_30 = l_Repr_addAppParen(x_29, x_2);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__30;
x_32 = l_Repr_addAppParen(x_31, x_2);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_instReprBinderInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____boxed), 2, 0);
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
x_1 = lean_mk_string_from_bytes("assertion violation: ", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_mkData___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(looseBVarRange ≤ Nat.pow 2 16 - 1)\n  ", 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_mkData___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_mkData___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_mkData___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_mkData___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.mkData", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_mkData___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_mkData___closed__6;
x_3 = lean_unsigned_to_nat(200u);
x_4 = lean_unsigned_to_nat(2u);
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
x_50 = lean_nat_dec_le(x_2, x_49);
if (x_48 == 0)
{
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = l_Lean_Expr_mkData___closed__7;
x_52 = l_panic___at_Lean_Expr_mkData___spec__1(x_51);
return x_52;
}
else
{
uint8_t x_53; 
x_53 = lean_uint32_to_uint8(x_3);
x_10 = x_53;
goto block_46;
}
}
else
{
if (x_50 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Lean_Expr_mkData___closed__7;
x_55 = l_panic___at_Lean_Expr_mkData___spec__1(x_54);
return x_55;
}
else
{
uint8_t x_56; 
x_56 = 255;
x_10 = x_56;
goto block_46;
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
static uint32_t _init_l_Lean_Expr_mkAppData___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = l_Lean_Expr_mkData___closed__1;
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_mkAppData___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(looseBVarRange ≤ (Nat.pow 2 16 - 1).toUInt32)\n  ", 51);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_mkAppData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_mkData___closed__2;
x_2 = l_Lean_Expr_mkAppData___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_mkAppData___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.mkAppData", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_mkAppData___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_mkAppData___closed__4;
x_3 = lean_unsigned_to_nat(221u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Expr_mkAppData___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static uint64_t _init_l_Lean_Expr_mkAppData___closed__6() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 15;
x_2 = 32;
x_3 = lean_uint64_shift_left(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; uint16_t x_4; uint8_t x_5; uint16_t x_6; uint8_t x_7; uint16_t x_8; uint16_t x_9; uint32_t x_10; uint32_t x_11; uint8_t x_12; uint64_t x_13; uint8_t x_14; 
x_3 = l_Lean_Expr_Data_approxDepth(x_1);
x_4 = lean_uint8_to_uint16(x_3);
x_5 = l_Lean_Expr_Data_approxDepth(x_2);
x_6 = lean_uint8_to_uint16(x_5);
x_7 = lean_uint16_dec_lt(x_6, x_4);
x_8 = 1;
x_9 = 255;
x_10 = l_Lean_Expr_Data_looseBVarRange(x_1);
x_11 = l_Lean_Expr_Data_looseBVarRange(x_2);
x_12 = lean_uint32_dec_lt(x_11, x_10);
x_13 = lean_uint64_mix_hash(x_1, x_2);
if (x_7 == 0)
{
uint16_t x_37; uint8_t x_38; 
x_37 = lean_uint16_add(x_6, x_8);
x_38 = lean_uint16_dec_lt(x_9, x_37);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = lean_uint16_to_uint8(x_37);
x_14 = x_39;
goto block_36;
}
else
{
uint8_t x_40; 
x_40 = 255;
x_14 = x_40;
goto block_36;
}
}
else
{
uint16_t x_41; uint8_t x_42; 
x_41 = lean_uint16_add(x_4, x_8);
x_42 = lean_uint16_dec_lt(x_9, x_41);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = lean_uint16_to_uint8(x_41);
x_14 = x_43;
goto block_36;
}
else
{
uint8_t x_44; 
x_44 = 255;
x_14 = x_44;
goto block_36;
}
}
block_36:
{
uint32_t x_15; 
if (x_12 == 0)
{
x_15 = x_11;
goto block_35;
}
else
{
x_15 = x_10;
goto block_35;
}
block_35:
{
uint32_t x_16; uint8_t x_17; 
x_16 = l_Lean_Expr_mkAppData___closed__1;
x_17 = lean_uint32_dec_le(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Expr_mkAppData___closed__5;
x_19 = l_panic___at_Lean_Expr_mkData___spec__1(x_18);
return x_19;
}
else
{
uint64_t x_20; uint64_t x_21; uint64_t x_22; uint32_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; lean_object* x_34; 
x_20 = lean_uint64_lor(x_1, x_2);
x_21 = l_Lean_Expr_mkAppData___closed__6;
x_22 = lean_uint64_land(x_20, x_21);
x_23 = lean_uint64_to_uint32(x_13);
x_24 = lean_uint32_to_uint64(x_23);
x_25 = lean_uint64_lor(x_22, x_24);
x_26 = lean_uint8_to_uint64(x_14);
x_27 = 40;
x_28 = lean_uint64_shift_left(x_26, x_27);
x_29 = lean_uint64_lor(x_25, x_28);
x_30 = lean_uint32_to_uint64(x_15);
x_31 = 48;
x_32 = lean_uint64_shift_left(x_30, x_31);
x_33 = lean_uint64_lor(x_29, x_32);
x_34 = lean_box_uint64(x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_mkAppData___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lean_Expr_mkAppData(x_3, x_4);
return x_5;
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
x_1 = lean_mk_string_from_bytes(" (bi := ", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprData__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprData__1___lambda__2(lean_object* x_1, uint64_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; 
x_5 = (uint8_t)((x_2 << 24) >> 61);
x_6 = 0;
x_7 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_5, x_6);
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
x_13 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387_(x_5, x_12);
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
x_1 = lean_mk_string_from_bytes(" (nonDepLet := ", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprData__1___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
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
x_1 = lean_mk_string_from_bytes(" (hasLevelMVar := ", 18);
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
x_1 = lean_mk_string_from_bytes(" (hasExprMVar := ", 17);
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
x_1 = lean_mk_string_from_bytes(" (hasFVar := ", 13);
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
x_1 = lean_mk_string_from_bytes(" (approxDepth := ", 17);
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
x_1 = lean_mk_string_from_bytes("Expr.mkData ", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprData__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" (looseBVarRange := ", 20);
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
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1872_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1872____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1872_(x_1, x_2);
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
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1872____boxed), 2, 0);
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
LEAN_EXPORT uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1929_(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; 
x_2 = 0;
x_3 = l_Lean_Name_hash___override(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1929____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1929_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableFVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1929____boxed), 1, 0);
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
static lean_object* _init_l_Lean_instInhabitedMVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_beqMVarId____x40_Lean_Expr___hyg_2081_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_beqMVarId____x40_Lean_Expr___hyg_2081____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Expr_0__Lean_beqMVarId____x40_Lean_Expr___hyg_2081_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqMVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_beqMVarId____x40_Lean_Expr___hyg_2081____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instBEqMVarId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instBEqMVarId___closed__1;
return x_1;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_2138_(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; 
x_2 = 0;
x_3 = l_Lean_Name_hash___override(x_1);
x_4 = lean_uint64_mix_hash(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_2138____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_2138_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableMVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_2138____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instHashableMVarId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instHashableMVarId___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("name", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" := ", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__3;
x_2 = l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__5;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("{ ", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__7;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__8;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" }", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Name_reprPrec(x_1, x_3);
x_5 = l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__6;
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__10;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__12;
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__9;
x_12 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = 0;
x_14 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprMVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instReprMVarId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instReprMVarId___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprMVarId__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Name_reprPrec(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprMVarId__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instReprMVarId__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instMVarIdSetInhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_instMVarIdSetEmptyCollection() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdSetMVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instForInFVarIdSetFVarId___closed__2;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instEmptyCollectionMVarIdMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_instForInMVarIdMapProdMVarId___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instForInFVarIdSetFVarId___closed__1;
x_2 = lean_alloc_closure((void*)(l_Std_RBMap_instForInRBMapProd___boxed), 5, 4);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
lean_closure_set(x_2, 3, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInMVarIdMapProdMVarId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instForInMVarIdMapProdMVarId___closed__1;
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedMVarIdMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_data___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_ctor_get_uint64(x_1, lean_ctor_num_objs(x_1)*sizeof(void*));
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
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
lean_dec(x_1);
x_15 = lean_apply_1(x_2, x_14);
return x_15;
}
case 1:
{
lean_object* x_16; lean_object* x_17; 
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
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_1(x_3, x_16);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; 
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
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_apply_1(x_4, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; 
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
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_1(x_5, x_20);
return x_21;
}
case 4:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
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
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_apply_2(x_6, x_22, x_23);
return x_24;
}
case 5:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
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
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_apply_2(x_7, x_25, x_26);
return x_27;
}
case 6:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
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
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_32 = lean_box(x_31);
x_33 = lean_apply_4(x_8, x_28, x_29, x_30, x_32);
return x_33;
}
case 7:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
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
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 2);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_38 = lean_box(x_37);
x_39 = lean_apply_4(x_9, x_34, x_35, x_36, x_38);
return x_39;
}
case 8:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
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
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 3);
lean_inc(x_43);
x_44 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_45 = lean_box(x_44);
x_46 = lean_apply_5(x_10, x_40, x_41, x_42, x_43, x_45);
return x_46;
}
case 9:
{
lean_object* x_47; lean_object* x_48; 
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
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_apply_1(x_11, x_47);
return x_48;
}
case 10:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
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
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
lean_dec(x_1);
x_51 = lean_apply_2(x_12, x_49, x_50);
return x_51;
}
default: 
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
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
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 2);
lean_inc(x_54);
lean_dec(x_1);
x_55 = lean_apply_3(x_13, x_52, x_53, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_casesOn___override(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_casesOn___override___rarg), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_bvar___override(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_fvar___override(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint32_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; 
x_2 = 13;
x_3 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1929_(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Expr_mvar___override(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint32_t x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; 
x_2 = 17;
x_3 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_2138_(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Expr_sort___override(lean_object* x_1) {
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
LEAN_EXPORT uint64_t l_List_foldl___at_Lean_Expr_const___override___spec__1(uint64_t x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_Expr_const___override___spec__2(uint8_t x_1, lean_object* x_2) {
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
x_5 = l_List_foldr___at_Lean_Expr_const___override___spec__2(x_1, x_4);
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
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_Expr_const___override___spec__3(uint8_t x_1, lean_object* x_2) {
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
x_5 = l_List_foldr___at_Lean_Expr_const___override___spec__3(x_1, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Expr_const___override(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint32_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; 
x_3 = 5;
x_4 = l_Lean_Name_hash___override(x_1);
x_5 = 7;
x_6 = l_List_foldl___at_Lean_Expr_const___override___spec__1(x_5, x_2);
x_7 = lean_uint64_mix_hash(x_4, x_6);
x_8 = lean_uint64_mix_hash(x_3, x_7);
x_9 = 0;
x_10 = 0;
x_11 = l_List_foldr___at_Lean_Expr_const___override___spec__2(x_10, x_2);
x_12 = l_List_foldr___at_Lean_Expr_const___override___spec__3(x_10, x_2);
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
LEAN_EXPORT lean_object* l_Lean_Expr_app___override(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; uint16_t x_6; uint8_t x_7; uint16_t x_8; uint8_t x_9; uint16_t x_10; uint16_t x_11; uint32_t x_12; uint32_t x_13; uint8_t x_14; uint64_t x_15; uint8_t x_16; 
x_3 = lean_ctor_get_uint64(x_1, lean_ctor_num_objs(x_1)*sizeof(void*));
x_4 = lean_ctor_get_uint64(x_2, lean_ctor_num_objs(x_2)*sizeof(void*));
x_5 = l_Lean_Expr_Data_approxDepth(x_3);
x_6 = lean_uint8_to_uint16(x_5);
x_7 = l_Lean_Expr_Data_approxDepth(x_4);
x_8 = lean_uint8_to_uint16(x_7);
x_9 = lean_uint16_dec_lt(x_8, x_6);
x_10 = 1;
x_11 = 255;
x_12 = l_Lean_Expr_Data_looseBVarRange(x_3);
x_13 = l_Lean_Expr_Data_looseBVarRange(x_4);
x_14 = lean_uint32_dec_lt(x_13, x_12);
x_15 = lean_uint64_mix_hash(x_3, x_4);
if (x_9 == 0)
{
uint16_t x_41; uint8_t x_42; 
x_41 = lean_uint16_add(x_8, x_10);
x_42 = lean_uint16_dec_lt(x_11, x_41);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = lean_uint16_to_uint8(x_41);
x_16 = x_43;
goto block_40;
}
else
{
uint8_t x_44; 
x_44 = 255;
x_16 = x_44;
goto block_40;
}
}
else
{
uint16_t x_45; uint8_t x_46; 
x_45 = lean_uint16_add(x_6, x_10);
x_46 = lean_uint16_dec_lt(x_11, x_45);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = lean_uint16_to_uint8(x_45);
x_16 = x_47;
goto block_40;
}
else
{
uint8_t x_48; 
x_48 = 255;
x_16 = x_48;
goto block_40;
}
}
block_40:
{
uint32_t x_17; 
if (x_14 == 0)
{
x_17 = x_13;
goto block_39;
}
else
{
x_17 = x_12;
goto block_39;
}
block_39:
{
uint32_t x_18; uint8_t x_19; 
x_18 = l_Lean_Expr_mkAppData___closed__1;
x_19 = lean_uint32_dec_le(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; 
x_20 = l_Lean_Expr_mkAppData___closed__5;
x_21 = l_panic___at_Lean_Expr_mkData___spec__1(x_20);
x_22 = lean_unbox_uint64(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set_uint64(x_23, sizeof(void*)*2, x_22);
return x_23;
}
else
{
uint64_t x_24; uint64_t x_25; uint64_t x_26; uint32_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; lean_object* x_38; 
x_24 = lean_uint64_lor(x_3, x_4);
x_25 = l_Lean_Expr_mkAppData___closed__6;
x_26 = lean_uint64_land(x_24, x_25);
x_27 = lean_uint64_to_uint32(x_15);
x_28 = lean_uint32_to_uint64(x_27);
x_29 = lean_uint64_lor(x_26, x_28);
x_30 = lean_uint8_to_uint64(x_16);
x_31 = 40;
x_32 = lean_uint64_shift_left(x_30, x_31);
x_33 = lean_uint64_lor(x_29, x_32);
x_34 = lean_uint32_to_uint64(x_17);
x_35 = 48;
x_36 = lean_uint64_shift_left(x_34, x_35);
x_37 = lean_uint64_lor(x_33, x_36);
x_38 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_2);
lean_ctor_set_uint64(x_38, sizeof(void*)*2, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
uint64_t x_5; uint8_t x_6; uint32_t x_7; uint64_t x_8; uint8_t x_9; uint32_t x_10; uint8_t x_11; uint32_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint32_t x_16; lean_object* x_17; uint32_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint32_t x_27; 
x_5 = lean_ctor_get_uint64(x_2, lean_ctor_num_objs(x_2)*sizeof(void*));
x_6 = l_Lean_Expr_Data_approxDepth(x_5);
x_7 = lean_uint8_to_uint32(x_6);
x_8 = lean_ctor_get_uint64(x_3, lean_ctor_num_objs(x_3)*sizeof(void*));
x_9 = l_Lean_Expr_Data_approxDepth(x_8);
x_10 = lean_uint8_to_uint32(x_9);
x_11 = lean_uint32_dec_lt(x_10, x_7);
x_12 = 1;
x_13 = l_Lean_Expr_Data_hash(x_5);
x_14 = l_Lean_Expr_Data_hash(x_8);
x_15 = lean_uint64_mix_hash(x_13, x_14);
x_16 = l_Lean_Expr_Data_looseBVarRange(x_5);
x_17 = lean_uint32_to_nat(x_16);
x_18 = l_Lean_Expr_Data_looseBVarRange(x_8);
x_19 = lean_uint32_to_nat(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_19, x_20);
lean_dec(x_19);
x_22 = lean_nat_dec_lt(x_21, x_17);
x_23 = l_Lean_Expr_Data_hasFVar(x_5);
x_24 = l_Lean_Expr_Data_hasExprMVar(x_5);
x_25 = l_Lean_Expr_Data_hasLevelMVar(x_5);
x_26 = l_Lean_Expr_Data_hasLevelParam(x_5);
if (x_11 == 0)
{
x_27 = x_10;
goto block_129;
}
else
{
x_27 = x_7;
goto block_129;
}
block_129:
{
uint32_t x_28; uint64_t x_29; uint64_t x_30; lean_object* x_31; lean_object* x_80; 
x_28 = lean_uint32_add(x_27, x_12);
x_29 = lean_uint32_to_uint64(x_28);
x_30 = lean_uint64_mix_hash(x_29, x_15);
if (x_22 == 0)
{
lean_dec(x_17);
if (x_23 == 0)
{
x_31 = x_21;
goto block_79;
}
else
{
x_80 = x_21;
goto block_128;
}
}
else
{
lean_dec(x_21);
if (x_23 == 0)
{
x_31 = x_17;
goto block_79;
}
else
{
x_80 = x_17;
goto block_128;
}
}
block_79:
{
uint8_t x_32; 
x_32 = l_Lean_Expr_Data_hasFVar(x_8);
if (x_24 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Expr_Data_hasExprMVar(x_8);
if (x_25 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Expr_Data_hasLevelMVar(x_8);
if (x_26 == 0)
{
uint8_t x_35; uint8_t x_36; lean_object* x_37; uint64_t x_38; lean_object* x_39; 
x_35 = l_Lean_Expr_Data_hasLevelParam(x_8);
x_36 = 0;
x_37 = l_Lean_Expr_mkData(x_30, x_31, x_28, x_32, x_33, x_34, x_35, x_4, x_36);
lean_dec(x_31);
x_38 = lean_unbox_uint64(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_2);
lean_ctor_set(x_39, 2, x_3);
lean_ctor_set_uint64(x_39, sizeof(void*)*3, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 8, x_4);
return x_39;
}
else
{
uint8_t x_40; uint8_t x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; 
x_40 = 1;
x_41 = 0;
x_42 = l_Lean_Expr_mkData(x_30, x_31, x_28, x_32, x_33, x_34, x_40, x_4, x_41);
lean_dec(x_31);
x_43 = lean_unbox_uint64(x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_2);
lean_ctor_set(x_44, 2, x_3);
lean_ctor_set_uint64(x_44, sizeof(void*)*3, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*3 + 8, x_4);
return x_44;
}
}
else
{
if (x_26 == 0)
{
uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; 
x_45 = l_Lean_Expr_Data_hasLevelParam(x_8);
x_46 = 1;
x_47 = 0;
x_48 = l_Lean_Expr_mkData(x_30, x_31, x_28, x_32, x_33, x_46, x_45, x_4, x_47);
lean_dec(x_31);
x_49 = lean_unbox_uint64(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_2);
lean_ctor_set(x_50, 2, x_3);
lean_ctor_set_uint64(x_50, sizeof(void*)*3, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*3 + 8, x_4);
return x_50;
}
else
{
uint8_t x_51; uint8_t x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; 
x_51 = 1;
x_52 = 0;
x_53 = l_Lean_Expr_mkData(x_30, x_31, x_28, x_32, x_33, x_51, x_51, x_4, x_52);
lean_dec(x_31);
x_54 = lean_unbox_uint64(x_53);
lean_dec(x_53);
x_55 = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_2);
lean_ctor_set(x_55, 2, x_3);
lean_ctor_set_uint64(x_55, sizeof(void*)*3, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 8, x_4);
return x_55;
}
}
}
else
{
if (x_25 == 0)
{
uint8_t x_56; 
x_56 = l_Lean_Expr_Data_hasLevelMVar(x_8);
if (x_26 == 0)
{
uint8_t x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; 
x_57 = l_Lean_Expr_Data_hasLevelParam(x_8);
x_58 = 1;
x_59 = 0;
x_60 = l_Lean_Expr_mkData(x_30, x_31, x_28, x_32, x_58, x_56, x_57, x_4, x_59);
lean_dec(x_31);
x_61 = lean_unbox_uint64(x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_2);
lean_ctor_set(x_62, 2, x_3);
lean_ctor_set_uint64(x_62, sizeof(void*)*3, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*3 + 8, x_4);
return x_62;
}
else
{
uint8_t x_63; uint8_t x_64; lean_object* x_65; uint64_t x_66; lean_object* x_67; 
x_63 = 1;
x_64 = 0;
x_65 = l_Lean_Expr_mkData(x_30, x_31, x_28, x_32, x_63, x_56, x_63, x_4, x_64);
lean_dec(x_31);
x_66 = lean_unbox_uint64(x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_2);
lean_ctor_set(x_67, 2, x_3);
lean_ctor_set_uint64(x_67, sizeof(void*)*3, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*3 + 8, x_4);
return x_67;
}
}
else
{
if (x_26 == 0)
{
uint8_t x_68; uint8_t x_69; uint8_t x_70; lean_object* x_71; uint64_t x_72; lean_object* x_73; 
x_68 = l_Lean_Expr_Data_hasLevelParam(x_8);
x_69 = 1;
x_70 = 0;
x_71 = l_Lean_Expr_mkData(x_30, x_31, x_28, x_32, x_69, x_69, x_68, x_4, x_70);
lean_dec(x_31);
x_72 = lean_unbox_uint64(x_71);
lean_dec(x_71);
x_73 = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_2);
lean_ctor_set(x_73, 2, x_3);
lean_ctor_set_uint64(x_73, sizeof(void*)*3, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*3 + 8, x_4);
return x_73;
}
else
{
uint8_t x_74; uint8_t x_75; lean_object* x_76; uint64_t x_77; lean_object* x_78; 
x_74 = 1;
x_75 = 0;
x_76 = l_Lean_Expr_mkData(x_30, x_31, x_28, x_32, x_74, x_74, x_74, x_4, x_75);
lean_dec(x_31);
x_77 = lean_unbox_uint64(x_76);
lean_dec(x_76);
x_78 = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_2);
lean_ctor_set(x_78, 2, x_3);
lean_ctor_set_uint64(x_78, sizeof(void*)*3, x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*3 + 8, x_4);
return x_78;
}
}
}
}
block_128:
{
if (x_24 == 0)
{
uint8_t x_81; 
x_81 = l_Lean_Expr_Data_hasExprMVar(x_8);
if (x_25 == 0)
{
uint8_t x_82; 
x_82 = l_Lean_Expr_Data_hasLevelMVar(x_8);
if (x_26 == 0)
{
uint8_t x_83; uint8_t x_84; uint8_t x_85; lean_object* x_86; uint64_t x_87; lean_object* x_88; 
x_83 = l_Lean_Expr_Data_hasLevelParam(x_8);
x_84 = 1;
x_85 = 0;
x_86 = l_Lean_Expr_mkData(x_30, x_80, x_28, x_84, x_81, x_82, x_83, x_4, x_85);
lean_dec(x_80);
x_87 = lean_unbox_uint64(x_86);
lean_dec(x_86);
x_88 = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_2);
lean_ctor_set(x_88, 2, x_3);
lean_ctor_set_uint64(x_88, sizeof(void*)*3, x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*3 + 8, x_4);
return x_88;
}
else
{
uint8_t x_89; uint8_t x_90; lean_object* x_91; uint64_t x_92; lean_object* x_93; 
x_89 = 1;
x_90 = 0;
x_91 = l_Lean_Expr_mkData(x_30, x_80, x_28, x_89, x_81, x_82, x_89, x_4, x_90);
lean_dec(x_80);
x_92 = lean_unbox_uint64(x_91);
lean_dec(x_91);
x_93 = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_2);
lean_ctor_set(x_93, 2, x_3);
lean_ctor_set_uint64(x_93, sizeof(void*)*3, x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*3 + 8, x_4);
return x_93;
}
}
else
{
if (x_26 == 0)
{
uint8_t x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; uint64_t x_98; lean_object* x_99; 
x_94 = l_Lean_Expr_Data_hasLevelParam(x_8);
x_95 = 1;
x_96 = 0;
x_97 = l_Lean_Expr_mkData(x_30, x_80, x_28, x_95, x_81, x_95, x_94, x_4, x_96);
lean_dec(x_80);
x_98 = lean_unbox_uint64(x_97);
lean_dec(x_97);
x_99 = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(x_99, 0, x_1);
lean_ctor_set(x_99, 1, x_2);
lean_ctor_set(x_99, 2, x_3);
lean_ctor_set_uint64(x_99, sizeof(void*)*3, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*3 + 8, x_4);
return x_99;
}
else
{
uint8_t x_100; uint8_t x_101; lean_object* x_102; uint64_t x_103; lean_object* x_104; 
x_100 = 1;
x_101 = 0;
x_102 = l_Lean_Expr_mkData(x_30, x_80, x_28, x_100, x_81, x_100, x_100, x_4, x_101);
lean_dec(x_80);
x_103 = lean_unbox_uint64(x_102);
lean_dec(x_102);
x_104 = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_2);
lean_ctor_set(x_104, 2, x_3);
lean_ctor_set_uint64(x_104, sizeof(void*)*3, x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*3 + 8, x_4);
return x_104;
}
}
}
else
{
if (x_25 == 0)
{
uint8_t x_105; 
x_105 = l_Lean_Expr_Data_hasLevelMVar(x_8);
if (x_26 == 0)
{
uint8_t x_106; uint8_t x_107; uint8_t x_108; lean_object* x_109; uint64_t x_110; lean_object* x_111; 
x_106 = l_Lean_Expr_Data_hasLevelParam(x_8);
x_107 = 1;
x_108 = 0;
x_109 = l_Lean_Expr_mkData(x_30, x_80, x_28, x_107, x_107, x_105, x_106, x_4, x_108);
lean_dec(x_80);
x_110 = lean_unbox_uint64(x_109);
lean_dec(x_109);
x_111 = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(x_111, 0, x_1);
lean_ctor_set(x_111, 1, x_2);
lean_ctor_set(x_111, 2, x_3);
lean_ctor_set_uint64(x_111, sizeof(void*)*3, x_110);
lean_ctor_set_uint8(x_111, sizeof(void*)*3 + 8, x_4);
return x_111;
}
else
{
uint8_t x_112; uint8_t x_113; lean_object* x_114; uint64_t x_115; lean_object* x_116; 
x_112 = 1;
x_113 = 0;
x_114 = l_Lean_Expr_mkData(x_30, x_80, x_28, x_112, x_112, x_105, x_112, x_4, x_113);
lean_dec(x_80);
x_115 = lean_unbox_uint64(x_114);
lean_dec(x_114);
x_116 = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(x_116, 0, x_1);
lean_ctor_set(x_116, 1, x_2);
lean_ctor_set(x_116, 2, x_3);
lean_ctor_set_uint64(x_116, sizeof(void*)*3, x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*3 + 8, x_4);
return x_116;
}
}
else
{
if (x_26 == 0)
{
uint8_t x_117; uint8_t x_118; uint8_t x_119; lean_object* x_120; uint64_t x_121; lean_object* x_122; 
x_117 = l_Lean_Expr_Data_hasLevelParam(x_8);
x_118 = 1;
x_119 = 0;
x_120 = l_Lean_Expr_mkData(x_30, x_80, x_28, x_118, x_118, x_118, x_117, x_4, x_119);
lean_dec(x_80);
x_121 = lean_unbox_uint64(x_120);
lean_dec(x_120);
x_122 = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(x_122, 0, x_1);
lean_ctor_set(x_122, 1, x_2);
lean_ctor_set(x_122, 2, x_3);
lean_ctor_set_uint64(x_122, sizeof(void*)*3, x_121);
lean_ctor_set_uint8(x_122, sizeof(void*)*3 + 8, x_4);
return x_122;
}
else
{
uint8_t x_123; uint8_t x_124; lean_object* x_125; uint64_t x_126; lean_object* x_127; 
x_123 = 1;
x_124 = 0;
x_125 = l_Lean_Expr_mkData(x_30, x_80, x_28, x_123, x_123, x_123, x_123, x_4, x_124);
lean_dec(x_80);
x_126 = lean_unbox_uint64(x_125);
lean_dec(x_125);
x_127 = lean_alloc_ctor(6, 3, 9);
lean_ctor_set(x_127, 0, x_1);
lean_ctor_set(x_127, 1, x_2);
lean_ctor_set(x_127, 2, x_3);
lean_ctor_set_uint64(x_127, sizeof(void*)*3, x_126);
lean_ctor_set_uint8(x_127, sizeof(void*)*3 + 8, x_4);
return x_127;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
uint64_t x_5; uint8_t x_6; uint32_t x_7; uint64_t x_8; uint8_t x_9; uint32_t x_10; uint8_t x_11; uint32_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint32_t x_16; lean_object* x_17; uint32_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint32_t x_27; 
x_5 = lean_ctor_get_uint64(x_2, lean_ctor_num_objs(x_2)*sizeof(void*));
x_6 = l_Lean_Expr_Data_approxDepth(x_5);
x_7 = lean_uint8_to_uint32(x_6);
x_8 = lean_ctor_get_uint64(x_3, lean_ctor_num_objs(x_3)*sizeof(void*));
x_9 = l_Lean_Expr_Data_approxDepth(x_8);
x_10 = lean_uint8_to_uint32(x_9);
x_11 = lean_uint32_dec_lt(x_10, x_7);
x_12 = 1;
x_13 = l_Lean_Expr_Data_hash(x_5);
x_14 = l_Lean_Expr_Data_hash(x_8);
x_15 = lean_uint64_mix_hash(x_13, x_14);
x_16 = l_Lean_Expr_Data_looseBVarRange(x_5);
x_17 = lean_uint32_to_nat(x_16);
x_18 = l_Lean_Expr_Data_looseBVarRange(x_8);
x_19 = lean_uint32_to_nat(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_19, x_20);
lean_dec(x_19);
x_22 = lean_nat_dec_lt(x_21, x_17);
x_23 = l_Lean_Expr_Data_hasFVar(x_5);
x_24 = l_Lean_Expr_Data_hasExprMVar(x_5);
x_25 = l_Lean_Expr_Data_hasLevelMVar(x_5);
x_26 = l_Lean_Expr_Data_hasLevelParam(x_5);
if (x_11 == 0)
{
x_27 = x_10;
goto block_129;
}
else
{
x_27 = x_7;
goto block_129;
}
block_129:
{
uint32_t x_28; uint64_t x_29; uint64_t x_30; lean_object* x_31; lean_object* x_80; 
x_28 = lean_uint32_add(x_27, x_12);
x_29 = lean_uint32_to_uint64(x_28);
x_30 = lean_uint64_mix_hash(x_29, x_15);
if (x_22 == 0)
{
lean_dec(x_17);
if (x_23 == 0)
{
x_31 = x_21;
goto block_79;
}
else
{
x_80 = x_21;
goto block_128;
}
}
else
{
lean_dec(x_21);
if (x_23 == 0)
{
x_31 = x_17;
goto block_79;
}
else
{
x_80 = x_17;
goto block_128;
}
}
block_79:
{
uint8_t x_32; 
x_32 = l_Lean_Expr_Data_hasFVar(x_8);
if (x_24 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Expr_Data_hasExprMVar(x_8);
if (x_25 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Expr_Data_hasLevelMVar(x_8);
if (x_26 == 0)
{
uint8_t x_35; uint8_t x_36; lean_object* x_37; uint64_t x_38; lean_object* x_39; 
x_35 = l_Lean_Expr_Data_hasLevelParam(x_8);
x_36 = 0;
x_37 = l_Lean_Expr_mkData(x_30, x_31, x_28, x_32, x_33, x_34, x_35, x_4, x_36);
lean_dec(x_31);
x_38 = lean_unbox_uint64(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_2);
lean_ctor_set(x_39, 2, x_3);
lean_ctor_set_uint64(x_39, sizeof(void*)*3, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 8, x_4);
return x_39;
}
else
{
uint8_t x_40; uint8_t x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; 
x_40 = 1;
x_41 = 0;
x_42 = l_Lean_Expr_mkData(x_30, x_31, x_28, x_32, x_33, x_34, x_40, x_4, x_41);
lean_dec(x_31);
x_43 = lean_unbox_uint64(x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_2);
lean_ctor_set(x_44, 2, x_3);
lean_ctor_set_uint64(x_44, sizeof(void*)*3, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*3 + 8, x_4);
return x_44;
}
}
else
{
if (x_26 == 0)
{
uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; 
x_45 = l_Lean_Expr_Data_hasLevelParam(x_8);
x_46 = 1;
x_47 = 0;
x_48 = l_Lean_Expr_mkData(x_30, x_31, x_28, x_32, x_33, x_46, x_45, x_4, x_47);
lean_dec(x_31);
x_49 = lean_unbox_uint64(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_2);
lean_ctor_set(x_50, 2, x_3);
lean_ctor_set_uint64(x_50, sizeof(void*)*3, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*3 + 8, x_4);
return x_50;
}
else
{
uint8_t x_51; uint8_t x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; 
x_51 = 1;
x_52 = 0;
x_53 = l_Lean_Expr_mkData(x_30, x_31, x_28, x_32, x_33, x_51, x_51, x_4, x_52);
lean_dec(x_31);
x_54 = lean_unbox_uint64(x_53);
lean_dec(x_53);
x_55 = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_2);
lean_ctor_set(x_55, 2, x_3);
lean_ctor_set_uint64(x_55, sizeof(void*)*3, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*3 + 8, x_4);
return x_55;
}
}
}
else
{
if (x_25 == 0)
{
uint8_t x_56; 
x_56 = l_Lean_Expr_Data_hasLevelMVar(x_8);
if (x_26 == 0)
{
uint8_t x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; 
x_57 = l_Lean_Expr_Data_hasLevelParam(x_8);
x_58 = 1;
x_59 = 0;
x_60 = l_Lean_Expr_mkData(x_30, x_31, x_28, x_32, x_58, x_56, x_57, x_4, x_59);
lean_dec(x_31);
x_61 = lean_unbox_uint64(x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_2);
lean_ctor_set(x_62, 2, x_3);
lean_ctor_set_uint64(x_62, sizeof(void*)*3, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*3 + 8, x_4);
return x_62;
}
else
{
uint8_t x_63; uint8_t x_64; lean_object* x_65; uint64_t x_66; lean_object* x_67; 
x_63 = 1;
x_64 = 0;
x_65 = l_Lean_Expr_mkData(x_30, x_31, x_28, x_32, x_63, x_56, x_63, x_4, x_64);
lean_dec(x_31);
x_66 = lean_unbox_uint64(x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_2);
lean_ctor_set(x_67, 2, x_3);
lean_ctor_set_uint64(x_67, sizeof(void*)*3, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*3 + 8, x_4);
return x_67;
}
}
else
{
if (x_26 == 0)
{
uint8_t x_68; uint8_t x_69; uint8_t x_70; lean_object* x_71; uint64_t x_72; lean_object* x_73; 
x_68 = l_Lean_Expr_Data_hasLevelParam(x_8);
x_69 = 1;
x_70 = 0;
x_71 = l_Lean_Expr_mkData(x_30, x_31, x_28, x_32, x_69, x_69, x_68, x_4, x_70);
lean_dec(x_31);
x_72 = lean_unbox_uint64(x_71);
lean_dec(x_71);
x_73 = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_2);
lean_ctor_set(x_73, 2, x_3);
lean_ctor_set_uint64(x_73, sizeof(void*)*3, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*3 + 8, x_4);
return x_73;
}
else
{
uint8_t x_74; uint8_t x_75; lean_object* x_76; uint64_t x_77; lean_object* x_78; 
x_74 = 1;
x_75 = 0;
x_76 = l_Lean_Expr_mkData(x_30, x_31, x_28, x_32, x_74, x_74, x_74, x_4, x_75);
lean_dec(x_31);
x_77 = lean_unbox_uint64(x_76);
lean_dec(x_76);
x_78 = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_2);
lean_ctor_set(x_78, 2, x_3);
lean_ctor_set_uint64(x_78, sizeof(void*)*3, x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*3 + 8, x_4);
return x_78;
}
}
}
}
block_128:
{
if (x_24 == 0)
{
uint8_t x_81; 
x_81 = l_Lean_Expr_Data_hasExprMVar(x_8);
if (x_25 == 0)
{
uint8_t x_82; 
x_82 = l_Lean_Expr_Data_hasLevelMVar(x_8);
if (x_26 == 0)
{
uint8_t x_83; uint8_t x_84; uint8_t x_85; lean_object* x_86; uint64_t x_87; lean_object* x_88; 
x_83 = l_Lean_Expr_Data_hasLevelParam(x_8);
x_84 = 1;
x_85 = 0;
x_86 = l_Lean_Expr_mkData(x_30, x_80, x_28, x_84, x_81, x_82, x_83, x_4, x_85);
lean_dec(x_80);
x_87 = lean_unbox_uint64(x_86);
lean_dec(x_86);
x_88 = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_2);
lean_ctor_set(x_88, 2, x_3);
lean_ctor_set_uint64(x_88, sizeof(void*)*3, x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*3 + 8, x_4);
return x_88;
}
else
{
uint8_t x_89; uint8_t x_90; lean_object* x_91; uint64_t x_92; lean_object* x_93; 
x_89 = 1;
x_90 = 0;
x_91 = l_Lean_Expr_mkData(x_30, x_80, x_28, x_89, x_81, x_82, x_89, x_4, x_90);
lean_dec(x_80);
x_92 = lean_unbox_uint64(x_91);
lean_dec(x_91);
x_93 = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_2);
lean_ctor_set(x_93, 2, x_3);
lean_ctor_set_uint64(x_93, sizeof(void*)*3, x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*3 + 8, x_4);
return x_93;
}
}
else
{
if (x_26 == 0)
{
uint8_t x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; uint64_t x_98; lean_object* x_99; 
x_94 = l_Lean_Expr_Data_hasLevelParam(x_8);
x_95 = 1;
x_96 = 0;
x_97 = l_Lean_Expr_mkData(x_30, x_80, x_28, x_95, x_81, x_95, x_94, x_4, x_96);
lean_dec(x_80);
x_98 = lean_unbox_uint64(x_97);
lean_dec(x_97);
x_99 = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(x_99, 0, x_1);
lean_ctor_set(x_99, 1, x_2);
lean_ctor_set(x_99, 2, x_3);
lean_ctor_set_uint64(x_99, sizeof(void*)*3, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*3 + 8, x_4);
return x_99;
}
else
{
uint8_t x_100; uint8_t x_101; lean_object* x_102; uint64_t x_103; lean_object* x_104; 
x_100 = 1;
x_101 = 0;
x_102 = l_Lean_Expr_mkData(x_30, x_80, x_28, x_100, x_81, x_100, x_100, x_4, x_101);
lean_dec(x_80);
x_103 = lean_unbox_uint64(x_102);
lean_dec(x_102);
x_104 = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_2);
lean_ctor_set(x_104, 2, x_3);
lean_ctor_set_uint64(x_104, sizeof(void*)*3, x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*3 + 8, x_4);
return x_104;
}
}
}
else
{
if (x_25 == 0)
{
uint8_t x_105; 
x_105 = l_Lean_Expr_Data_hasLevelMVar(x_8);
if (x_26 == 0)
{
uint8_t x_106; uint8_t x_107; uint8_t x_108; lean_object* x_109; uint64_t x_110; lean_object* x_111; 
x_106 = l_Lean_Expr_Data_hasLevelParam(x_8);
x_107 = 1;
x_108 = 0;
x_109 = l_Lean_Expr_mkData(x_30, x_80, x_28, x_107, x_107, x_105, x_106, x_4, x_108);
lean_dec(x_80);
x_110 = lean_unbox_uint64(x_109);
lean_dec(x_109);
x_111 = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(x_111, 0, x_1);
lean_ctor_set(x_111, 1, x_2);
lean_ctor_set(x_111, 2, x_3);
lean_ctor_set_uint64(x_111, sizeof(void*)*3, x_110);
lean_ctor_set_uint8(x_111, sizeof(void*)*3 + 8, x_4);
return x_111;
}
else
{
uint8_t x_112; uint8_t x_113; lean_object* x_114; uint64_t x_115; lean_object* x_116; 
x_112 = 1;
x_113 = 0;
x_114 = l_Lean_Expr_mkData(x_30, x_80, x_28, x_112, x_112, x_105, x_112, x_4, x_113);
lean_dec(x_80);
x_115 = lean_unbox_uint64(x_114);
lean_dec(x_114);
x_116 = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(x_116, 0, x_1);
lean_ctor_set(x_116, 1, x_2);
lean_ctor_set(x_116, 2, x_3);
lean_ctor_set_uint64(x_116, sizeof(void*)*3, x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*3 + 8, x_4);
return x_116;
}
}
else
{
if (x_26 == 0)
{
uint8_t x_117; uint8_t x_118; uint8_t x_119; lean_object* x_120; uint64_t x_121; lean_object* x_122; 
x_117 = l_Lean_Expr_Data_hasLevelParam(x_8);
x_118 = 1;
x_119 = 0;
x_120 = l_Lean_Expr_mkData(x_30, x_80, x_28, x_118, x_118, x_118, x_117, x_4, x_119);
lean_dec(x_80);
x_121 = lean_unbox_uint64(x_120);
lean_dec(x_120);
x_122 = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(x_122, 0, x_1);
lean_ctor_set(x_122, 1, x_2);
lean_ctor_set(x_122, 2, x_3);
lean_ctor_set_uint64(x_122, sizeof(void*)*3, x_121);
lean_ctor_set_uint8(x_122, sizeof(void*)*3 + 8, x_4);
return x_122;
}
else
{
uint8_t x_123; uint8_t x_124; lean_object* x_125; uint64_t x_126; lean_object* x_127; 
x_123 = 1;
x_124 = 0;
x_125 = l_Lean_Expr_mkData(x_30, x_80, x_28, x_123, x_123, x_123, x_123, x_4, x_124);
lean_dec(x_80);
x_126 = lean_unbox_uint64(x_125);
lean_dec(x_125);
x_127 = lean_alloc_ctor(7, 3, 9);
lean_ctor_set(x_127, 0, x_1);
lean_ctor_set(x_127, 1, x_2);
lean_ctor_set(x_127, 2, x_3);
lean_ctor_set_uint64(x_127, sizeof(void*)*3, x_126);
lean_ctor_set_uint8(x_127, sizeof(void*)*3 + 8, x_4);
return x_127;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
uint64_t x_6; uint8_t x_7; uint32_t x_8; uint64_t x_9; uint8_t x_10; uint32_t x_11; uint8_t x_12; uint64_t x_13; uint8_t x_14; uint32_t x_15; uint32_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint32_t x_22; lean_object* x_23; uint32_t x_24; lean_object* x_25; uint8_t x_26; uint32_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint32_t x_35; 
x_6 = lean_ctor_get_uint64(x_2, lean_ctor_num_objs(x_2)*sizeof(void*));
x_7 = l_Lean_Expr_Data_approxDepth(x_6);
x_8 = lean_uint8_to_uint32(x_7);
x_9 = lean_ctor_get_uint64(x_3, lean_ctor_num_objs(x_3)*sizeof(void*));
x_10 = l_Lean_Expr_Data_approxDepth(x_9);
x_11 = lean_uint8_to_uint32(x_10);
x_12 = lean_uint32_dec_lt(x_11, x_8);
x_13 = lean_ctor_get_uint64(x_4, lean_ctor_num_objs(x_4)*sizeof(void*));
x_14 = l_Lean_Expr_Data_approxDepth(x_13);
x_15 = lean_uint8_to_uint32(x_14);
x_16 = 1;
x_17 = l_Lean_Expr_Data_hash(x_6);
x_18 = l_Lean_Expr_Data_hash(x_9);
x_19 = l_Lean_Expr_Data_hash(x_13);
x_20 = lean_uint64_mix_hash(x_18, x_19);
x_21 = lean_uint64_mix_hash(x_17, x_20);
x_22 = l_Lean_Expr_Data_looseBVarRange(x_6);
x_23 = lean_uint32_to_nat(x_22);
x_24 = l_Lean_Expr_Data_looseBVarRange(x_9);
x_25 = lean_uint32_to_nat(x_24);
x_26 = lean_nat_dec_lt(x_25, x_23);
x_27 = l_Lean_Expr_Data_looseBVarRange(x_13);
x_28 = lean_uint32_to_nat(x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_28, x_29);
lean_dec(x_28);
x_31 = l_Lean_Expr_Data_hasFVar(x_6);
x_32 = l_Lean_Expr_Data_hasExprMVar(x_6);
x_33 = l_Lean_Expr_Data_hasLevelMVar(x_6);
x_34 = l_Lean_Expr_Data_hasLevelParam(x_6);
if (x_12 == 0)
{
uint8_t x_142; 
x_142 = lean_uint32_dec_lt(x_15, x_11);
if (x_142 == 0)
{
x_35 = x_15;
goto block_141;
}
else
{
x_35 = x_11;
goto block_141;
}
}
else
{
uint8_t x_143; 
x_143 = lean_uint32_dec_lt(x_15, x_8);
if (x_143 == 0)
{
x_35 = x_15;
goto block_141;
}
else
{
x_35 = x_8;
goto block_141;
}
}
block_141:
{
uint32_t x_36; uint64_t x_37; uint64_t x_38; lean_object* x_39; 
x_36 = lean_uint32_add(x_35, x_16);
x_37 = lean_uint32_to_uint64(x_36);
x_38 = lean_uint64_mix_hash(x_37, x_21);
if (x_26 == 0)
{
uint8_t x_139; 
lean_dec(x_23);
x_139 = lean_nat_dec_lt(x_30, x_25);
if (x_139 == 0)
{
lean_dec(x_25);
x_39 = x_30;
goto block_138;
}
else
{
lean_dec(x_30);
x_39 = x_25;
goto block_138;
}
}
else
{
uint8_t x_140; 
lean_dec(x_25);
x_140 = lean_nat_dec_lt(x_30, x_23);
if (x_140 == 0)
{
lean_dec(x_23);
x_39 = x_30;
goto block_138;
}
else
{
lean_dec(x_30);
x_39 = x_23;
goto block_138;
}
}
block_138:
{
uint8_t x_40; 
if (x_31 == 0)
{
uint8_t x_134; 
x_134 = l_Lean_Expr_Data_hasFVar(x_9);
if (x_134 == 0)
{
uint8_t x_135; 
x_135 = l_Lean_Expr_Data_hasFVar(x_13);
x_40 = x_135;
goto block_133;
}
else
{
uint8_t x_136; 
x_136 = 1;
x_40 = x_136;
goto block_133;
}
}
else
{
uint8_t x_137; 
x_137 = 1;
x_40 = x_137;
goto block_133;
}
block_133:
{
uint8_t x_41; 
if (x_32 == 0)
{
uint8_t x_78; 
x_78 = l_Lean_Expr_Data_hasExprMVar(x_9);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Expr_Data_hasExprMVar(x_13);
if (x_33 == 0)
{
x_41 = x_79;
goto block_77;
}
else
{
if (x_34 == 0)
{
uint8_t x_80; 
x_80 = l_Lean_Expr_Data_hasLevelParam(x_9);
if (x_80 == 0)
{
uint8_t x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; uint64_t x_85; lean_object* x_86; 
x_81 = l_Lean_Expr_Data_hasLevelParam(x_13);
x_82 = 1;
x_83 = 0;
x_84 = l_Lean_Expr_mkData(x_38, x_39, x_36, x_40, x_79, x_82, x_81, x_83, x_5);
lean_dec(x_39);
x_85 = lean_unbox_uint64(x_84);
lean_dec(x_84);
x_86 = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_2);
lean_ctor_set(x_86, 2, x_3);
lean_ctor_set(x_86, 3, x_4);
lean_ctor_set_uint64(x_86, sizeof(void*)*4, x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*4 + 8, x_5);
return x_86;
}
else
{
uint8_t x_87; uint8_t x_88; lean_object* x_89; uint64_t x_90; lean_object* x_91; 
x_87 = 1;
x_88 = 0;
x_89 = l_Lean_Expr_mkData(x_38, x_39, x_36, x_40, x_79, x_87, x_87, x_88, x_5);
lean_dec(x_39);
x_90 = lean_unbox_uint64(x_89);
lean_dec(x_89);
x_91 = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_2);
lean_ctor_set(x_91, 2, x_3);
lean_ctor_set(x_91, 3, x_4);
lean_ctor_set_uint64(x_91, sizeof(void*)*4, x_90);
lean_ctor_set_uint8(x_91, sizeof(void*)*4 + 8, x_5);
return x_91;
}
}
else
{
uint8_t x_92; uint8_t x_93; lean_object* x_94; uint64_t x_95; lean_object* x_96; 
x_92 = 1;
x_93 = 0;
x_94 = l_Lean_Expr_mkData(x_38, x_39, x_36, x_40, x_79, x_92, x_92, x_93, x_5);
lean_dec(x_39);
x_95 = lean_unbox_uint64(x_94);
lean_dec(x_94);
x_96 = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(x_96, 0, x_1);
lean_ctor_set(x_96, 1, x_2);
lean_ctor_set(x_96, 2, x_3);
lean_ctor_set(x_96, 3, x_4);
lean_ctor_set_uint64(x_96, sizeof(void*)*4, x_95);
lean_ctor_set_uint8(x_96, sizeof(void*)*4 + 8, x_5);
return x_96;
}
}
}
else
{
if (x_33 == 0)
{
uint8_t x_97; 
x_97 = 1;
x_41 = x_97;
goto block_77;
}
else
{
if (x_34 == 0)
{
uint8_t x_98; 
x_98 = l_Lean_Expr_Data_hasLevelParam(x_9);
if (x_98 == 0)
{
uint8_t x_99; uint8_t x_100; uint8_t x_101; lean_object* x_102; uint64_t x_103; lean_object* x_104; 
x_99 = l_Lean_Expr_Data_hasLevelParam(x_13);
x_100 = 1;
x_101 = 0;
x_102 = l_Lean_Expr_mkData(x_38, x_39, x_36, x_40, x_100, x_100, x_99, x_101, x_5);
lean_dec(x_39);
x_103 = lean_unbox_uint64(x_102);
lean_dec(x_102);
x_104 = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_2);
lean_ctor_set(x_104, 2, x_3);
lean_ctor_set(x_104, 3, x_4);
lean_ctor_set_uint64(x_104, sizeof(void*)*4, x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*4 + 8, x_5);
return x_104;
}
else
{
uint8_t x_105; uint8_t x_106; lean_object* x_107; uint64_t x_108; lean_object* x_109; 
x_105 = 1;
x_106 = 0;
x_107 = l_Lean_Expr_mkData(x_38, x_39, x_36, x_40, x_105, x_105, x_105, x_106, x_5);
lean_dec(x_39);
x_108 = lean_unbox_uint64(x_107);
lean_dec(x_107);
x_109 = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(x_109, 0, x_1);
lean_ctor_set(x_109, 1, x_2);
lean_ctor_set(x_109, 2, x_3);
lean_ctor_set(x_109, 3, x_4);
lean_ctor_set_uint64(x_109, sizeof(void*)*4, x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*4 + 8, x_5);
return x_109;
}
}
else
{
uint8_t x_110; uint8_t x_111; lean_object* x_112; uint64_t x_113; lean_object* x_114; 
x_110 = 1;
x_111 = 0;
x_112 = l_Lean_Expr_mkData(x_38, x_39, x_36, x_40, x_110, x_110, x_110, x_111, x_5);
lean_dec(x_39);
x_113 = lean_unbox_uint64(x_112);
lean_dec(x_112);
x_114 = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(x_114, 0, x_1);
lean_ctor_set(x_114, 1, x_2);
lean_ctor_set(x_114, 2, x_3);
lean_ctor_set(x_114, 3, x_4);
lean_ctor_set_uint64(x_114, sizeof(void*)*4, x_113);
lean_ctor_set_uint8(x_114, sizeof(void*)*4 + 8, x_5);
return x_114;
}
}
}
}
else
{
if (x_33 == 0)
{
uint8_t x_115; 
x_115 = 1;
x_41 = x_115;
goto block_77;
}
else
{
if (x_34 == 0)
{
uint8_t x_116; 
x_116 = l_Lean_Expr_Data_hasLevelParam(x_9);
if (x_116 == 0)
{
uint8_t x_117; uint8_t x_118; uint8_t x_119; lean_object* x_120; uint64_t x_121; lean_object* x_122; 
x_117 = l_Lean_Expr_Data_hasLevelParam(x_13);
x_118 = 1;
x_119 = 0;
x_120 = l_Lean_Expr_mkData(x_38, x_39, x_36, x_40, x_118, x_118, x_117, x_119, x_5);
lean_dec(x_39);
x_121 = lean_unbox_uint64(x_120);
lean_dec(x_120);
x_122 = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(x_122, 0, x_1);
lean_ctor_set(x_122, 1, x_2);
lean_ctor_set(x_122, 2, x_3);
lean_ctor_set(x_122, 3, x_4);
lean_ctor_set_uint64(x_122, sizeof(void*)*4, x_121);
lean_ctor_set_uint8(x_122, sizeof(void*)*4 + 8, x_5);
return x_122;
}
else
{
uint8_t x_123; uint8_t x_124; lean_object* x_125; uint64_t x_126; lean_object* x_127; 
x_123 = 1;
x_124 = 0;
x_125 = l_Lean_Expr_mkData(x_38, x_39, x_36, x_40, x_123, x_123, x_123, x_124, x_5);
lean_dec(x_39);
x_126 = lean_unbox_uint64(x_125);
lean_dec(x_125);
x_127 = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(x_127, 0, x_1);
lean_ctor_set(x_127, 1, x_2);
lean_ctor_set(x_127, 2, x_3);
lean_ctor_set(x_127, 3, x_4);
lean_ctor_set_uint64(x_127, sizeof(void*)*4, x_126);
lean_ctor_set_uint8(x_127, sizeof(void*)*4 + 8, x_5);
return x_127;
}
}
else
{
uint8_t x_128; uint8_t x_129; lean_object* x_130; uint64_t x_131; lean_object* x_132; 
x_128 = 1;
x_129 = 0;
x_130 = l_Lean_Expr_mkData(x_38, x_39, x_36, x_40, x_128, x_128, x_128, x_129, x_5);
lean_dec(x_39);
x_131 = lean_unbox_uint64(x_130);
lean_dec(x_130);
x_132 = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(x_132, 0, x_1);
lean_ctor_set(x_132, 1, x_2);
lean_ctor_set(x_132, 2, x_3);
lean_ctor_set(x_132, 3, x_4);
lean_ctor_set_uint64(x_132, sizeof(void*)*4, x_131);
lean_ctor_set_uint8(x_132, sizeof(void*)*4 + 8, x_5);
return x_132;
}
}
}
block_77:
{
uint8_t x_42; 
x_42 = l_Lean_Expr_Data_hasLevelMVar(x_9);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Expr_Data_hasLevelMVar(x_13);
if (x_34 == 0)
{
uint8_t x_44; 
x_44 = l_Lean_Expr_Data_hasLevelParam(x_9);
if (x_44 == 0)
{
uint8_t x_45; uint8_t x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; 
x_45 = l_Lean_Expr_Data_hasLevelParam(x_13);
x_46 = 0;
x_47 = l_Lean_Expr_mkData(x_38, x_39, x_36, x_40, x_41, x_43, x_45, x_46, x_5);
lean_dec(x_39);
x_48 = lean_unbox_uint64(x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_2);
lean_ctor_set(x_49, 2, x_3);
lean_ctor_set(x_49, 3, x_4);
lean_ctor_set_uint64(x_49, sizeof(void*)*4, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*4 + 8, x_5);
return x_49;
}
else
{
uint8_t x_50; uint8_t x_51; lean_object* x_52; uint64_t x_53; lean_object* x_54; 
x_50 = 1;
x_51 = 0;
x_52 = l_Lean_Expr_mkData(x_38, x_39, x_36, x_40, x_41, x_43, x_50, x_51, x_5);
lean_dec(x_39);
x_53 = lean_unbox_uint64(x_52);
lean_dec(x_52);
x_54 = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_2);
lean_ctor_set(x_54, 2, x_3);
lean_ctor_set(x_54, 3, x_4);
lean_ctor_set_uint64(x_54, sizeof(void*)*4, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*4 + 8, x_5);
return x_54;
}
}
else
{
uint8_t x_55; uint8_t x_56; lean_object* x_57; uint64_t x_58; lean_object* x_59; 
x_55 = 1;
x_56 = 0;
x_57 = l_Lean_Expr_mkData(x_38, x_39, x_36, x_40, x_41, x_43, x_55, x_56, x_5);
lean_dec(x_39);
x_58 = lean_unbox_uint64(x_57);
lean_dec(x_57);
x_59 = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_2);
lean_ctor_set(x_59, 2, x_3);
lean_ctor_set(x_59, 3, x_4);
lean_ctor_set_uint64(x_59, sizeof(void*)*4, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*4 + 8, x_5);
return x_59;
}
}
else
{
if (x_34 == 0)
{
uint8_t x_60; 
x_60 = l_Lean_Expr_Data_hasLevelParam(x_9);
if (x_60 == 0)
{
uint8_t x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; 
x_61 = l_Lean_Expr_Data_hasLevelParam(x_13);
x_62 = 1;
x_63 = 0;
x_64 = l_Lean_Expr_mkData(x_38, x_39, x_36, x_40, x_41, x_62, x_61, x_63, x_5);
lean_dec(x_39);
x_65 = lean_unbox_uint64(x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(x_66, 0, x_1);
lean_ctor_set(x_66, 1, x_2);
lean_ctor_set(x_66, 2, x_3);
lean_ctor_set(x_66, 3, x_4);
lean_ctor_set_uint64(x_66, sizeof(void*)*4, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*4 + 8, x_5);
return x_66;
}
else
{
uint8_t x_67; uint8_t x_68; lean_object* x_69; uint64_t x_70; lean_object* x_71; 
x_67 = 1;
x_68 = 0;
x_69 = l_Lean_Expr_mkData(x_38, x_39, x_36, x_40, x_41, x_67, x_67, x_68, x_5);
lean_dec(x_39);
x_70 = lean_unbox_uint64(x_69);
lean_dec(x_69);
x_71 = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_2);
lean_ctor_set(x_71, 2, x_3);
lean_ctor_set(x_71, 3, x_4);
lean_ctor_set_uint64(x_71, sizeof(void*)*4, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*4 + 8, x_5);
return x_71;
}
}
else
{
uint8_t x_72; uint8_t x_73; lean_object* x_74; uint64_t x_75; lean_object* x_76; 
x_72 = 1;
x_73 = 0;
x_74 = l_Lean_Expr_mkData(x_38, x_39, x_36, x_40, x_41, x_72, x_72, x_73, x_5);
lean_dec(x_39);
x_75 = lean_unbox_uint64(x_74);
lean_dec(x_74);
x_76 = lean_alloc_ctor(8, 4, 9);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_2);
lean_ctor_set(x_76, 2, x_3);
lean_ctor_set(x_76, 3, x_4);
lean_ctor_set_uint64(x_76, sizeof(void*)*4, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*4 + 8, x_5);
return x_76;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lit___override(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Expr_mdata___override(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint8_t x_4; uint32_t x_5; uint32_t x_6; uint32_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint32_t x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; 
x_3 = lean_ctor_get_uint64(x_2, lean_ctor_num_objs(x_2)*sizeof(void*));
x_4 = l_Lean_Expr_Data_approxDepth(x_3);
x_5 = lean_uint8_to_uint32(x_4);
x_6 = 1;
x_7 = lean_uint32_add(x_5, x_6);
x_8 = lean_uint32_to_uint64(x_7);
x_9 = l_Lean_Expr_Data_hash(x_3);
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = l_Lean_Expr_Data_looseBVarRange(x_3);
x_12 = lean_uint32_to_nat(x_11);
x_13 = l_Lean_Expr_Data_hasFVar(x_3);
x_14 = l_Lean_Expr_Data_hasExprMVar(x_3);
x_15 = l_Lean_Expr_Data_hasLevelMVar(x_3);
x_16 = l_Lean_Expr_Data_hasLevelParam(x_3);
x_17 = 0;
x_18 = 0;
x_19 = l_Lean_Expr_mkData(x_10, x_12, x_7, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_12);
x_20 = lean_unbox_uint64(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set_uint64(x_21, sizeof(void*)*2, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_proj___override(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint8_t x_5; uint32_t x_6; uint32_t x_7; uint32_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint32_t x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; uint64_t x_25; lean_object* x_26; 
x_4 = lean_ctor_get_uint64(x_3, lean_ctor_num_objs(x_3)*sizeof(void*));
x_5 = l_Lean_Expr_Data_approxDepth(x_4);
x_6 = lean_uint8_to_uint32(x_5);
x_7 = 1;
x_8 = lean_uint32_add(x_6, x_7);
x_9 = lean_uint32_to_uint64(x_8);
x_10 = l_Lean_Name_hash___override(x_1);
x_11 = lean_uint64_of_nat(x_2);
x_12 = l_Lean_Expr_Data_hash(x_4);
x_13 = lean_uint64_mix_hash(x_11, x_12);
x_14 = lean_uint64_mix_hash(x_10, x_13);
x_15 = lean_uint64_mix_hash(x_9, x_14);
x_16 = l_Lean_Expr_Data_looseBVarRange(x_4);
x_17 = lean_uint32_to_nat(x_16);
x_18 = l_Lean_Expr_Data_hasFVar(x_4);
x_19 = l_Lean_Expr_Data_hasExprMVar(x_4);
x_20 = l_Lean_Expr_Data_hasLevelMVar(x_4);
x_21 = l_Lean_Expr_Data_hasLevelParam(x_4);
x_22 = 0;
x_23 = 0;
x_24 = l_Lean_Expr_mkData(x_15, x_17, x_8, x_18, x_19, x_20, x_21, x_22, x_23);
lean_dec(x_17);
x_25 = lean_unbox_uint64(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_2);
lean_ctor_set(x_26, 2, x_3);
lean_ctor_set_uint64(x_26, sizeof(void*)*3, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Expr_const___override___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_List_foldl___at_Lean_Expr_const___override___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_Expr_const___override___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at_Lean_Expr_const___override___spec__2(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_Expr_const___override___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at_Lean_Expr_const___override___spec__3(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam___override___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Expr_lam___override(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forallE___override___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Expr_forallE___override(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_letE___override___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_Expr_letE___override(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_instInhabitedExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
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
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_962_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__3(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_962_(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_962_(x_8, x_9);
lean_inc(x_2);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
x_12 = l_Std_Format_joinSep___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__3(x_4, x_2);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[]", 2);
return x_1;
}
}
static lean_object* _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__4;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[", 1);
return x_1;
}
}
static lean_object* _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__6;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__7;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("]", 1);
return x_1;
}
}
static lean_object* _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__2;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_4 = l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__5;
x_5 = l_Std_Format_joinSep___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__3(x_1, x_4);
x_6 = l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__9;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__11;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__8;
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = 0;
x_13 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
return x_13;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.bvar", 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__2;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.fvar", 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__5;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.mvar", 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__8;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.sort", 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__11;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.const", 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__14;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.app", 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__17;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.lam", 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__20;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.forallE", 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__22;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__23;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.letE", 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__25;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__26;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__28;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instReprData__1___lambda__3___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.lit", 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__31;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__32;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.mdata", 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__34;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__35;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.proj", 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__37;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__38;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
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
x_8 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__3;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
if (x_5 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
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
x_15 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
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
case 1:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_unsigned_to_nat(1024u);
x_22 = lean_nat_dec_le(x_21, x_2);
x_23 = l_Lean_Name_reprPrec(x_20, x_21);
x_24 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__6;
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
if (x_22 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_26 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
x_27 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = 0;
x_29 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = l_Repr_addAppParen(x_29, x_2);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_31 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
x_32 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
x_33 = 0;
x_34 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = l_Repr_addAppParen(x_34, x_2);
return x_35;
}
}
case 2:
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_unsigned_to_nat(1024u);
x_38 = lean_nat_dec_le(x_37, x_2);
x_39 = l_Lean_Name_reprPrec(x_36, x_37);
x_40 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__9;
x_41 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
if (x_38 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_42 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
x_43 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = 0;
x_45 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = l_Repr_addAppParen(x_45, x_2);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_47 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
x_48 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_41);
x_49 = 0;
x_50 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
x_51 = l_Repr_addAppParen(x_50, x_2);
return x_51;
}
}
case 3:
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
lean_dec(x_1);
x_53 = lean_unsigned_to_nat(1024u);
x_54 = lean_nat_dec_le(x_53, x_2);
x_55 = l___private_Lean_Level_0__Lean_reprLevel____x40_Lean_Level___hyg_962_(x_52, x_53);
x_56 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__12;
x_57 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
if (x_54 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_58 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
x_59 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = 0;
x_61 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_62 = l_Repr_addAppParen(x_61, x_2);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_63 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
x_64 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_57);
x_65 = 0;
x_66 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_65);
x_67 = l_Repr_addAppParen(x_66, x_2);
return x_67;
}
}
case 4:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 1);
lean_inc(x_69);
lean_dec(x_1);
x_70 = lean_unsigned_to_nat(1024u);
x_71 = lean_nat_dec_le(x_70, x_2);
x_72 = l_Lean_Name_reprPrec(x_68, x_70);
x_73 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__15;
x_74 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_box(1);
x_76 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1(x_69, x_70);
x_78 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
if (x_71 == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_79 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
x_80 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = 0;
x_82 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_81);
x_83 = l_Repr_addAppParen(x_82, x_2);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
x_84 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
x_85 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_78);
x_86 = 0;
x_87 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_86);
x_88 = l_Repr_addAppParen(x_87, x_2);
return x_88;
}
}
case 5:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_89 = lean_ctor_get(x_1, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_1, 1);
lean_inc(x_90);
lean_dec(x_1);
x_91 = lean_unsigned_to_nat(1024u);
x_92 = lean_nat_dec_le(x_91, x_2);
x_93 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113_(x_89, x_91);
x_94 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__18;
x_95 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_box(1);
x_97 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113_(x_90, x_91);
x_99 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
if (x_92 == 0)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; 
x_100 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
x_101 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = 0;
x_103 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_102);
x_104 = l_Repr_addAppParen(x_103, x_2);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; 
x_105 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
x_106 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_99);
x_107 = 0;
x_108 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set_uint8(x_108, sizeof(void*)*1, x_107);
x_109 = l_Repr_addAppParen(x_108, x_2);
return x_109;
}
}
case 6:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_110 = lean_ctor_get(x_1, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_1, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_1, 2);
lean_inc(x_112);
x_113 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_114 = lean_unsigned_to_nat(1024u);
x_115 = lean_nat_dec_le(x_114, x_2);
x_116 = l_Lean_Name_reprPrec(x_110, x_114);
x_117 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__21;
x_118 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_box(1);
x_120 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113_(x_111, x_114);
x_122 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_119);
x_124 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113_(x_112, x_114);
x_125 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_119);
x_127 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387_(x_113, x_114);
x_128 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
if (x_115 == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; 
x_129 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
x_130 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = 0;
x_132 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_131);
x_133 = l_Repr_addAppParen(x_132, x_2);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; 
x_134 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
x_135 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_128);
x_136 = 0;
x_137 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set_uint8(x_137, sizeof(void*)*1, x_136);
x_138 = l_Repr_addAppParen(x_137, x_2);
return x_138;
}
}
case 7:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_139 = lean_ctor_get(x_1, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_1, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_1, 2);
lean_inc(x_141);
x_142 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_143 = lean_unsigned_to_nat(1024u);
x_144 = lean_nat_dec_le(x_143, x_2);
x_145 = l_Lean_Name_reprPrec(x_139, x_143);
x_146 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__24;
x_147 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
x_148 = lean_box(1);
x_149 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113_(x_140, x_143);
x_151 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_148);
x_153 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113_(x_141, x_143);
x_154 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_148);
x_156 = l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387_(x_142, x_143);
x_157 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
if (x_144 == 0)
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; 
x_158 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
x_159 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
x_160 = 0;
x_161 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set_uint8(x_161, sizeof(void*)*1, x_160);
x_162 = l_Repr_addAppParen(x_161, x_2);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; 
x_163 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
x_164 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_157);
x_165 = 0;
x_166 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set_uint8(x_166, sizeof(void*)*1, x_165);
x_167 = l_Repr_addAppParen(x_166, x_2);
return x_167;
}
}
case 8:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_168 = lean_ctor_get(x_1, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_1, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_1, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_1, 3);
lean_inc(x_171);
x_172 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_173 = lean_unsigned_to_nat(1024u);
x_174 = lean_nat_dec_le(x_173, x_2);
x_175 = l_Lean_Name_reprPrec(x_168, x_173);
x_176 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__27;
x_177 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
x_178 = lean_box(1);
x_179 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113_(x_169, x_173);
x_181 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_178);
x_183 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113_(x_170, x_173);
x_184 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_178);
x_186 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113_(x_171, x_173);
x_187 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_178);
if (x_174 == 0)
{
if (x_172 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; 
x_189 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__29;
x_190 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
x_192 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
x_193 = 0;
x_194 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set_uint8(x_194, sizeof(void*)*1, x_193);
x_195 = l_Repr_addAppParen(x_194, x_2);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; 
x_196 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__30;
x_197 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_197, 0, x_188);
lean_ctor_set(x_197, 1, x_196);
x_198 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
x_199 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = 0;
x_201 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*1, x_200);
x_202 = l_Repr_addAppParen(x_201, x_2);
return x_202;
}
}
else
{
if (x_172 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; 
x_203 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__29;
x_204 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_204, 0, x_188);
lean_ctor_set(x_204, 1, x_203);
x_205 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
x_206 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_204);
x_207 = 0;
x_208 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set_uint8(x_208, sizeof(void*)*1, x_207);
x_209 = l_Repr_addAppParen(x_208, x_2);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; 
x_210 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__30;
x_211 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_211, 0, x_188);
lean_ctor_set(x_211, 1, x_210);
x_212 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
x_213 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
x_214 = 0;
x_215 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set_uint8(x_215, sizeof(void*)*1, x_214);
x_216 = l_Repr_addAppParen(x_215, x_2);
return x_216;
}
}
}
case 9:
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_217 = lean_ctor_get(x_1, 0);
lean_inc(x_217);
lean_dec(x_1);
x_218 = lean_unsigned_to_nat(1024u);
x_219 = lean_nat_dec_le(x_218, x_2);
x_220 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113_(x_217, x_218);
x_221 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__33;
x_222 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_220);
if (x_219 == 0)
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; 
x_223 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
x_224 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_222);
x_225 = 0;
x_226 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set_uint8(x_226, sizeof(void*)*1, x_225);
x_227 = l_Repr_addAppParen(x_226, x_2);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; 
x_228 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
x_229 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_222);
x_230 = 0;
x_231 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set_uint8(x_231, sizeof(void*)*1, x_230);
x_232 = l_Repr_addAppParen(x_231, x_2);
return x_232;
}
}
case 10:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_233 = lean_ctor_get(x_1, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_1, 1);
lean_inc(x_234);
lean_dec(x_1);
x_235 = lean_unsigned_to_nat(1024u);
x_236 = lean_nat_dec_le(x_235, x_2);
x_237 = l___private_Lean_Data_KVMap_0__Lean_reprKVMap____x40_Lean_Data_KVMap___hyg_877_(x_233, x_235);
x_238 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__36;
x_239 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_237);
x_240 = lean_box(1);
x_241 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
x_242 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113_(x_234, x_235);
x_243 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
if (x_236 == 0)
{
lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; 
x_244 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
x_245 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_243);
x_246 = 0;
x_247 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set_uint8(x_247, sizeof(void*)*1, x_246);
x_248 = l_Repr_addAppParen(x_247, x_2);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; 
x_249 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
x_250 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_243);
x_251 = 0;
x_252 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set_uint8(x_252, sizeof(void*)*1, x_251);
x_253 = l_Repr_addAppParen(x_252, x_2);
return x_253;
}
}
default: 
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_254 = lean_ctor_get(x_1, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_1, 1);
lean_inc(x_255);
x_256 = lean_ctor_get(x_1, 2);
lean_inc(x_256);
lean_dec(x_1);
x_257 = lean_unsigned_to_nat(1024u);
x_258 = lean_nat_dec_le(x_257, x_2);
x_259 = l_Lean_Name_reprPrec(x_254, x_257);
x_260 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__39;
x_261 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_259);
x_262 = lean_box(1);
x_263 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
x_264 = l_Nat_repr(x_255);
x_265 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_265, 0, x_264);
x_266 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_262);
x_268 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113_(x_256, x_257);
x_269 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
if (x_258 == 0)
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; lean_object* x_274; 
x_270 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4;
x_271 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_269);
x_272 = 0;
x_273 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set_uint8(x_273, sizeof(void*)*1, x_272);
x_274 = l_Repr_addAppParen(x_273, x_2);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; 
x_275 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5;
x_276 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_269);
x_277 = 0;
x_278 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set_uint8(x_278, sizeof(void*)*1, x_277);
x_279 = l_Repr_addAppParen(x_278, x_2);
return x_279;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____boxed), 2, 0);
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
static lean_object* _init_l_Lean_Expr_ctorName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("bvar", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fvar", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mvar", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("sort", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("const", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("app", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lam", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("forallE", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("letE", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lit", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mdata", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_ctorName___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("proj", 4);
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
uint64_t x_2; uint64_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, lean_ctor_num_objs(x_1)*sizeof(void*));
x_3 = l_Lean_Expr_Data_hash(x_2);
return x_3;
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
uint64_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, lean_ctor_num_objs(x_1)*sizeof(void*));
x_3 = l_Lean_Expr_Data_hasFVar(x_2);
return x_3;
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
uint64_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, lean_ctor_num_objs(x_1)*sizeof(void*));
x_3 = l_Lean_Expr_Data_hasExprMVar(x_2);
return x_3;
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
uint64_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, lean_ctor_num_objs(x_1)*sizeof(void*));
x_3 = l_Lean_Expr_Data_hasLevelMVar(x_2);
return x_3;
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
uint64_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, lean_ctor_num_objs(x_1)*sizeof(void*));
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
uint64_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, lean_ctor_num_objs(x_1)*sizeof(void*));
x_3 = l_Lean_Expr_Data_hasLevelParam(x_2);
return x_3;
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
uint64_t x_2; uint8_t x_3; uint32_t x_4; 
x_2 = lean_ctor_get_uint64(x_1, lean_ctor_num_objs(x_1)*sizeof(void*));
x_3 = l_Lean_Expr_Data_approxDepth(x_2);
x_4 = lean_uint8_to_uint32(x_3);
return x_4;
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
uint64_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_ctor_get_uint64(x_1, lean_ctor_num_objs(x_1)*sizeof(void*));
x_3 = l_Lean_Expr_Data_looseBVarRange(x_2);
x_4 = lean_uint32_to_nat(x_3);
return x_4;
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
uint64_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, lean_ctor_num_objs(x_1)*sizeof(void*));
x_3 = (uint8_t)((x_2 << 24) >> 61);
return x_3;
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
uint64_t x_2; uint32_t x_3; 
x_2 = lean_ctor_get_uint64(x_1, lean_ctor_num_objs(x_1)*sizeof(void*));
lean_dec(x_1);
x_3 = l_Lean_Expr_Data_looseBVarRange(x_2);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_mkConst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Nat", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Literal_type___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Literal_type___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("String", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Literal_type___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Literal_type___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Literal_type___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
lean_object* x_2; 
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSort(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_fvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_mvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkMData(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_mdata___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProj(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkApp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_app___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLambda(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_lam___override(x_1, x_3, x_4, x_2);
return x_5;
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
lean_object* x_5; 
x_5 = l_Lean_Expr_forallE___override(x_1, x_3, x_4, x_2);
return x_5;
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
x_1 = lean_mk_string_from_bytes("Unit", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkSimpleThunkType___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkSimpleThunkType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkSimpleThunkType___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunkType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = l_Lean_mkSimpleThunkType___closed__3;
x_4 = 0;
x_5 = l_Lean_Expr_forallE___override(x_2, x_3, x_1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_mkSimpleThunk___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_mkSimpleThunk___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkSimpleThunk___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkSimpleThunk(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = l_Lean_mkSimpleThunk___closed__2;
x_3 = l_Lean_mkSimpleThunkType___closed__3;
x_4 = 0;
x_5 = l_Lean_Expr_lam___override(x_2, x_3, x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_letE___override(x_1, x_2, x_3, x_4, x_5);
return x_6;
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
x_4 = l_Lean_Expr_app___override(x_1, x_2);
x_5 = l_Lean_Expr_app___override(x_4, x_3);
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
x_6 = l_Lean_Expr_app___override(x_5, x_4);
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
x_8 = l_Lean_Expr_app___override(x_7, x_6);
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
lean_object* x_2; 
x_2 = l_Lean_Expr_lit___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRawNatLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = l_Lean_Expr_lit___override(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkNatLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("OfNat", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_mkNatLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkNatLit___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkNatLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofNat", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_mkNatLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkNatLit___closed__2;
x_2 = l_Lean_mkNatLit___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
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
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkNatLit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Literal_type___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_mkNatLit___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("instOfNatNat", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_mkNatLit___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkNatLit___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkNatLit___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkNatLit___closed__9;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_4 = l_Lean_Expr_app___override(x_3, x_2);
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
x_3 = l_Lean_Expr_lit___override(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_bvar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_fvar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_fvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mvar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_mvar___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_sort(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_const(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_app(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_app___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_lam___override(x_1, x_2, x_3, x_4);
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
x_5 = l_Lean_Expr_forallE___override(x_1, x_2, x_3, x_4);
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
x_6 = l_Lean_Expr_letE___override(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_lit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_lit___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_mdata(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_mdata___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_expr_mk_proj(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
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
x_7 = l_Lean_Expr_app___override(x_4, x_6);
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
x_10 = l_Lean_Expr_app___override(x_4, x_9);
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
x_9 = l_Lean_Expr_app___override(x_4, x_8);
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppNumArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_2);
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
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getAppArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_2);
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
x_3 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_2);
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
x_4 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_3);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Expr_traverseApp___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___rarg(x_2, x_3, x_6, x_7, x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Expr_traverseApp___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkAppN), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Expr_traverseApp___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_array_set(x_4, x_5, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_5, x_9);
lean_dec(x_5);
x_3 = x_6;
x_4 = x_8;
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_2);
x_16 = lean_apply_1(x_2, x_3);
x_17 = l_Lean_Expr_withAppAux___at_Lean_Expr_traverseApp___spec__1___rarg___closed__1;
x_18 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_17, x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Expr_traverseApp___spec__1___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_19, 0, x_4);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
x_20 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Expr_traverseApp___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Expr_traverseApp___spec__1___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_3, x_4);
x_6 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_5);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_5, x_8);
lean_dec(x_5);
x_10 = l_Lean_Expr_withAppAux___at_Lean_Expr_traverseApp___spec__1___rarg(x_1, x_2, x_3, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_traverseApp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_traverseApp___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Expr_traverseApp___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_withAppAux___at_Lean_Expr_traverseApp___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
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
x_4 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_3);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.getRevArg!", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid index", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_getRevArg_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_getRevArg_x21___closed__1;
x_3 = lean_unsigned_to_nat(925u);
x_4 = lean_unsigned_to_nat(20u);
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
LEAN_EXPORT uint8_t l_Lean_Expr_isAppOfArity_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
case 10:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 1);
x_1 = x_16;
goto _start;
}
default: 
{
uint8_t x_18; 
lean_dec(x_3);
x_18 = 0;
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isAppOfArity_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_isAppOfArity_x27(x_1, x_2, x_3);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.appFn!", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("application expected", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_appFn_x21___closed__1;
x_3 = lean_unsigned_to_nat(959u);
x_4 = lean_unsigned_to_nat(15u);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.appArg!", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_appArg_x21___closed__1;
x_3 = lean_unsigned_to_nat(963u);
x_4 = lean_unsigned_to_nat(15u);
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
static lean_object* _init_l_Lean_Expr_appFn_x21_x27___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.appFn!'", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_appFn_x21_x27___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_appFn_x21_x27___closed__1;
x_3 = lean_unsigned_to_nat(968u);
x_4 = lean_unsigned_to_nat(17u);
x_5 = l_Lean_Expr_appFn_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
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
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Expr_appFn_x21_x27___closed__2;
x_6 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_5);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appFn_x21_x27___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_appFn_x21_x27(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21_x27___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.appArg!'", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_appArg_x21_x27___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_appArg_x21_x27___closed__1;
x_3 = lean_unsigned_to_nat(973u);
x_4 = lean_unsigned_to_nat(17u);
x_5 = l_Lean_Expr_appFn_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
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
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Expr_appArg_x21_x27___closed__2;
x_6 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_5);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_appArg_x21_x27___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_appArg_x21_x27(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.sortLevel!", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("sort expected", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_sortLevel_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_sortLevel_x21___closed__1;
x_3 = lean_unsigned_to_nat(977u);
x_4 = lean_unsigned_to_nat(14u);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.litValue!", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("literal expected", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_litValue_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_litValue_x21___closed__1;
x_3 = lean_unsigned_to_nat(981u);
x_4 = lean_unsigned_to_nat(13u);
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
x_1 = lean_mk_string_from_bytes("Char", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_isCharLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_isCharLit___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_isCharLit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_isCharLit___closed__2;
x_2 = l_Lean_mkNatLit___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.constName!", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("constant expected", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_constName_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_constName_x21___closed__1;
x_3 = lean_unsigned_to_nat(1000u);
x_4 = lean_unsigned_to_nat(17u);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.constLevels!", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_constLevels_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_constLevels_x21___closed__1;
x_3 = lean_unsigned_to_nat(1008u);
x_4 = lean_unsigned_to_nat(18u);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.bvarIdx!", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("bvar expected", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_bvarIdx_x21___closed__1;
x_3 = lean_unsigned_to_nat(1012u);
x_4 = lean_unsigned_to_nat(16u);
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
x_4 = l_panic___at_Lean_TSyntax_getNat___spec__1(x_3);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.fvarId!", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fvar expected", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_fvarId_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_fvarId_x21___closed__1;
x_3 = lean_unsigned_to_nat(1016u);
x_4 = lean_unsigned_to_nat(14u);
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_mvarId_x21___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedMVarId;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.mvarId!", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mvar expected", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_mvarId_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_mvarId_x21___closed__1;
x_3 = lean_unsigned_to_nat(1020u);
x_4 = lean_unsigned_to_nat(14u);
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
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = l_Lean_Expr_mvarId_x21___closed__3;
x_4 = l_panic___at_Lean_Expr_mvarId_x21___spec__1(x_3);
return x_4;
}
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.bindingName!", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("binding expected", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_bindingName_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_bindingName_x21___closed__1;
x_3 = lean_unsigned_to_nat(1025u);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.bindingDomain!", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_bindingDomain_x21___closed__1;
x_3 = lean_unsigned_to_nat(1030u);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.bindingBody!", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_bindingBody_x21___closed__1;
x_3 = lean_unsigned_to_nat(1035u);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.bindingInfo!", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_bindingInfo_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_bindingInfo_x21___closed__1;
x_3 = lean_unsigned_to_nat(1040u);
x_4 = lean_unsigned_to_nat(24u);
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
uint8_t x_2; lean_object* x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
case 7:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = l_Lean_Expr_bindingInfo_x21___closed__2;
x_7 = l_panic___at_Lean_Expr_bindingInfo_x21___spec__1(x_6);
return x_7;
}
}
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.letName!", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("let expression expected", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_letName_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_letName_x21___closed__1;
x_3 = lean_unsigned_to_nat(1044u);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.letType!", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_letType_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_letType_x21___closed__1;
x_3 = lean_unsigned_to_nat(1048u);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.letValue!", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_letValue_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_letValue_x21___closed__1;
x_3 = lean_unsigned_to_nat(1052u);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.letBody!", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_letBody_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_letBody_x21___closed__1;
x_3 = lean_unsigned_to_nat(1056u);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.mdataExpr!", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mdata expression expected", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_mdataExpr_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_mdataExpr_x21___closed__1;
x_3 = lean_unsigned_to_nat(1064u);
x_4 = lean_unsigned_to_nat(17u);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.projExpr!", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("proj expression expected", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_projExpr_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_projExpr_x21___closed__1;
x_3 = lean_unsigned_to_nat(1068u);
x_4 = lean_unsigned_to_nat(18u);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.projIdx!", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_projIdx_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_projIdx_x21___closed__1;
x_3 = lean_unsigned_to_nat(1072u);
x_4 = lean_unsigned_to_nat(18u);
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
x_4 = l_panic___at_Lean_TSyntax_getNat___spec__1(x_3);
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_7 = l_Lean_BinderInfo_isExplicit(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_1 = x_5;
x_2 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = lean_expr_has_loose_bvar(x_4, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
lean_dec(x_2);
x_1 = x_5;
x_2 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = 1;
return x_15;
}
}
}
else
{
if (x_3 == 0)
{
uint8_t x_16; 
lean_dec(x_2);
x_16 = 0;
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_expr_has_loose_bvar(x_1, x_2);
lean_dec(x_2);
return x_17;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_2, x_10);
x_12 = l_Lean_Expr_inferImplicit(x_6, x_11, x_3);
lean_dec(x_11);
x_13 = l_Lean_BinderInfo_isExplicit(x_7);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Expr_forallE___override(x_4, x_5, x_12, x_7);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = l_Lean_Expr_hasLooseBVarInExplicitDomain(x_12, x_8, x_3);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Expr_forallE___override(x_4, x_5, x_12, x_7);
return x_16;
}
else
{
uint8_t x_17; lean_object* x_18; 
x_17 = 1;
x_18 = l_Lean_Expr_forallE___override(x_4, x_5, x_12, x_17);
return x_18;
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
x_4 = l_Lean_Expr_fvar___override(x_2);
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
x_1 = lean_mk_string_from_bytes("Decidable", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkDecIsTrue___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("isTrue", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkDecIsTrue___closed__2;
x_2 = l_Lean_mkDecIsTrue___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkDecIsTrue___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkDecIsTrue___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_1 = lean_mk_string_from_bytes("isFalse", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkDecIsTrue___closed__2;
x_2 = l_Lean_mkDecIsFalse___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkDecIsFalse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkDecIsFalse___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_1 = l_Lean_instInhabitedExpr___closed__1;
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
x_10 = l_Lean_Expr_app___override(x_3, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev_go(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 6:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_10 = lean_nat_dec_lt(x_9, x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_nat_sub(x_4, x_9);
lean_dec(x_9);
x_12 = lean_expr_instantiate_range(x_7, x_11, x_4, x_1);
lean_dec(x_7);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(x_1, x_13, x_12, x_11);
return x_14;
}
else
{
x_5 = x_7;
x_6 = x_9;
goto _start;
}
}
case 8:
{
if (x_2 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_nat_sub(x_4, x_6);
lean_dec(x_6);
x_17 = lean_expr_instantiate_range(x_5, x_16, x_4, x_1);
lean_dec(x_5);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(x_1, x_18, x_17, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_5, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 3);
lean_inc(x_21);
x_22 = lean_nat_dec_lt(x_6, x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_20);
x_23 = lean_nat_sub(x_4, x_6);
lean_dec(x_6);
x_24 = lean_expr_instantiate_range(x_5, x_23, x_4, x_1);
lean_dec(x_5);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(x_1, x_25, x_24, x_23);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_5);
x_27 = lean_expr_instantiate1(x_21, x_20);
lean_dec(x_20);
lean_dec(x_21);
x_5 = x_27;
goto _start;
}
}
}
case 10:
{
if (x_3 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_dec(x_5);
x_5 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_5, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_dec(x_5);
x_33 = lean_nat_sub(x_4, x_6);
lean_dec(x_6);
x_34 = lean_expr_instantiate_range(x_32, x_33, x_4, x_1);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(x_1, x_35, x_34, x_33);
x_37 = l_Lean_Expr_mdata___override(x_31, x_36);
return x_37;
}
}
default: 
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_nat_sub(x_4, x_6);
lean_dec(x_6);
x_39 = lean_expr_instantiate_range(x_5, x_38, x_4, x_1);
lean_dec(x_5);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l___private_Lean_Expr_0__Lean_Expr_mkAppRevRangeAux(x_1, x_40, x_39, x_38);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Lean_Expr_betaRev_go(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Expr_betaRev_go(x_2, x_3, x_4, x_5, x_1, x_6);
lean_dec(x_5);
return x_8;
}
else
{
lean_dec(x_5);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_betaRev___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Expr_betaRev(x_1, x_2, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_beta(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = l_Array_reverse___rarg(x_2);
x_4 = 0;
x_5 = l_Lean_Expr_betaRev(x_1, x_3, x_4, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTargetFn(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 8:
{
if (x_1 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 3);
x_2 = x_5;
goto _start;
}
}
case 10:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 1);
x_2 = x_7;
goto _start;
}
default: 
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTargetFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Expr_isHeadBetaTargetFn(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headBeta(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_getAppFn(x_1);
x_3 = 0;
x_4 = l_Lean_Expr_isHeadBetaTargetFn(x_3, x_2);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_5);
x_7 = lean_mk_empty_array_with_capacity(x_6);
lean_dec(x_6);
x_8 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_7);
x_9 = l_Lean_Expr_betaRev(x_2, x_8, x_3, x_3);
lean_dec(x_8);
return x_9;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Expr_getAppFn(x_1);
x_4 = l_Lean_Expr_isHeadBetaTargetFn(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isHeadBetaTarget___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Expr_isHeadBetaTarget(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
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
x_1 = lean_mk_string_from_bytes("optParam", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_getOptParamDefault_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_getOptParamDefault_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
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
x_1 = lean_mk_string_from_bytes("autoParam", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_getAutoParamTactic_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_getAutoParamTactic_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
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
static lean_object* _init_l_Lean_Expr_isOutParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("outParam", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_isOutParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_isOutParam___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_is_out_param(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_isOutParam___closed__2;
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isOutParam___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_is_out_param(x_1);
x_3 = lean_box(x_2);
return x_3;
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
LEAN_EXPORT lean_object* lean_expr_consume_type_annotations(lean_object* x_1) {
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
uint8_t x_4; 
lean_inc(x_1);
x_4 = lean_is_out_param(x_1);
if (x_4 == 0)
{
return x_1;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
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
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Expr_appFn_x21(x_1);
lean_dec(x_1);
x_11 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
x_1 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cleanupAnnotations(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_consumeMData(x_1);
x_3 = lean_expr_consume_type_annotations(x_2);
x_4 = lean_expr_eqv(x_3, x_1);
if (x_4 == 0)
{
lean_dec(x_1);
x_1 = x_3;
goto _start;
}
else
{
lean_dec(x_3);
return x_1;
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
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Expr.0.Lean.Expr.updateApp!Impl", 45);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1;
x_3 = lean_unsigned_to_nat(1422u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Expr_appFn_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ptr_addr(x_4);
x_7 = lean_ptr_addr(x_2);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Expr_app___override(x_2, x_3);
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = lean_ptr_addr(x_5);
x_11 = lean_ptr_addr(x_3);
x_12 = lean_usize_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Expr_app___override(x_2, x_3);
return x_13;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__2;
x_15 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Expr.0.Lean.Expr.updateConst!Impl", 47);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1;
x_3 = lean_unsigned_to_nat(1433u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Expr_constName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = l_ptrEqList___rarg(x_4, x_2);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Lean_Expr_const___override(x_3, x_2);
return x_6;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__2;
x_8 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_7);
return x_8;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Expr.0.Lean.Expr.updateSort!Impl", 46);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("level expected", 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1;
x_3 = lean_unsigned_to_nat(1444u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_3; size_t x_4; size_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ptr_addr(x_3);
x_5 = lean_ptr_addr(x_2);
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Expr_sort___override(x_2);
return x_7;
}
else
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__3;
x_9 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Expr.0.Lean.Expr.updateMData!Impl", 47);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mdata expected", 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1;
x_3 = lean_unsigned_to_nat(1455u);
x_4 = lean_unsigned_to_nat(17u);
x_5 = l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_6 = lean_ptr_addr(x_2);
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l_Lean_Expr_mdata___override(x_3, x_2);
return x_8;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__3;
x_10 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_9);
return x_10;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Expr.0.Lean.Expr.updateProj!Impl", 46);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("proj expected", 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1;
x_3 = lean_unsigned_to_nat(1466u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_7 = lean_ptr_addr(x_2);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Lean_Expr_proj___override(x_3, x_4, x_2);
return x_9;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__3;
x_11 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_10);
return x_11;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Expr.0.Lean.Expr.updateForall!Impl", 48);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("forall expected", 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1;
x_3 = lean_unsigned_to_nat(1481u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; size_t x_9; size_t x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_9 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_10 = lean_ptr_addr(x_3);
x_11 = lean_usize_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_1);
x_12 = l_Lean_Expr_forallE___override(x_5, x_3, x_4, x_2);
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_14 = lean_ptr_addr(x_4);
x_15 = lean_usize_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = l_Lean_Expr_forallE___override(x_5, x_3, x_4, x_2);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_8, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = l_Lean_Expr_forallE___override(x_5, x_3, x_4, x_2);
return x_18;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__3;
x_20 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.updateForallE!", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_updateForallE_x21___closed__1;
x_3 = lean_unsigned_to_nat(1492u);
x_4 = lean_unsigned_to_nat(24u);
x_5 = l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateForallE_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; size_t x_9; size_t x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Expr_forallE___override(x_4, x_5, x_6, x_7);
x_9 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_10 = lean_ptr_addr(x_2);
x_11 = lean_usize_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
x_12 = l_Lean_Expr_forallE___override(x_4, x_2, x_3, x_7);
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_14 = lean_ptr_addr(x_3);
x_15 = lean_usize_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_8);
x_16 = l_Lean_Expr_forallE___override(x_4, x_2, x_3, x_7);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_7, x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
x_18 = l_Lean_Expr_forallE___override(x_4, x_2, x_3, x_7);
return x_18;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Expr_updateForallE_x21___closed__2;
x_20 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_19);
return x_20;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Expr.0.Lean.Expr.updateLambda!Impl", 48);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lambda expected", 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1;
x_3 = lean_unsigned_to_nat(1501u);
x_4 = lean_unsigned_to_nat(19u);
x_5 = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; size_t x_9; size_t x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_9 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_10 = lean_ptr_addr(x_3);
x_11 = lean_usize_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_1);
x_12 = l_Lean_Expr_lam___override(x_5, x_3, x_4, x_2);
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_14 = lean_ptr_addr(x_4);
x_15 = lean_usize_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = l_Lean_Expr_lam___override(x_5, x_3, x_4, x_2);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_8, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = l_Lean_Expr_lam___override(x_5, x_3, x_4, x_2);
return x_18;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__3;
x_20 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.updateLambdaE!", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l_Lean_Expr_updateLambdaE_x21___closed__1;
x_3 = lean_unsigned_to_nat(1512u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; size_t x_9; size_t x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Expr_lam___override(x_4, x_5, x_6, x_7);
x_9 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_10 = lean_ptr_addr(x_2);
x_11 = lean_usize_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
x_12 = l_Lean_Expr_lam___override(x_4, x_2, x_3, x_7);
return x_12;
}
else
{
size_t x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_14 = lean_ptr_addr(x_3);
x_15 = lean_usize_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_8);
x_16 = l_Lean_Expr_lam___override(x_4, x_2, x_3, x_7);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_7, x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
x_18 = l_Lean_Expr_lam___override(x_4, x_2, x_3, x_7);
return x_18;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Expr_updateLambdaE_x21___closed__2;
x_20 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_19);
return x_20;
}
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Expr.0.Lean.Expr.updateLet!Impl", 45);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_mkData___closed__5;
x_2 = l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1;
x_3 = lean_unsigned_to_nat(1521u);
x_4 = lean_unsigned_to_nat(22u);
x_5 = l_Lean_Expr_letName_x21___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; size_t x_10; size_t x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
x_10 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_11 = lean_ptr_addr(x_2);
x_12 = lean_usize_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_13 = l_Lean_Expr_letE___override(x_5, x_2, x_3, x_4, x_9);
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_15 = lean_ptr_addr(x_3);
x_16 = lean_usize_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_1);
x_17 = l_Lean_Expr_letE___override(x_5, x_2, x_3, x_4, x_9);
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_19 = lean_ptr_addr(x_4);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = l_Lean_Expr_letE___override(x_5, x_2, x_3, x_4, x_9);
return x_21;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__2;
x_23 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_updateFn(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_3);
x_5 = l_Lean_Expr_updateFn(x_3, x_2);
x_6 = lean_ptr_addr(x_3);
lean_dec(x_3);
x_7 = lean_ptr_addr(x_5);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Lean_Expr_app___override(x_5, x_4);
return x_9;
}
else
{
size_t x_10; uint8_t x_11; 
x_10 = lean_ptr_addr(x_4);
x_11 = lean_usize_dec_eq(x_10, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = l_Lean_Expr_app___override(x_5, x_4);
return x_12;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_4);
x_6 = l_Lean_Expr_eta(x_4);
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; uint8_t x_14; 
lean_dec(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Expr_lam___override(x_2, x_3, x_4, x_5);
x_13 = lean_ptr_addr(x_3);
x_14 = lean_usize_dec_eq(x_13, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_4);
x_15 = l_Lean_Expr_lam___override(x_2, x_3, x_6, x_5);
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_17 = lean_ptr_addr(x_6);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_12);
x_19 = l_Lean_Expr_lam___override(x_2, x_3, x_6, x_5);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_5, x_5);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_12);
x_21 = l_Lean_Expr_lam___override(x_2, x_3, x_6, x_5);
return x_21;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
}
}
else
{
uint8_t x_22; 
x_22 = lean_expr_has_loose_bvar(x_8, x_10);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_expr_lower_loose_bvars(x_8, x_23, x_23);
lean_dec(x_8);
return x_24;
}
else
{
lean_object* x_25; size_t x_26; uint8_t x_27; 
lean_dec(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_25 = l_Lean_Expr_lam___override(x_2, x_3, x_4, x_5);
x_26 = lean_ptr_addr(x_3);
x_27 = lean_usize_dec_eq(x_26, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_25);
lean_dec(x_4);
x_28 = l_Lean_Expr_lam___override(x_2, x_3, x_6, x_5);
return x_28;
}
else
{
size_t x_29; size_t x_30; uint8_t x_31; 
x_29 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_30 = lean_ptr_addr(x_6);
x_31 = lean_usize_dec_eq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_25);
x_32 = l_Lean_Expr_lam___override(x_2, x_3, x_6, x_5);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_5, x_5);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_25);
x_34 = l_Lean_Expr_lam___override(x_2, x_3, x_6, x_5);
return x_34;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
}
}
}
}
}
else
{
lean_object* x_35; size_t x_36; uint8_t x_37; 
lean_dec(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_35 = l_Lean_Expr_lam___override(x_2, x_3, x_4, x_5);
x_36 = lean_ptr_addr(x_3);
x_37 = lean_usize_dec_eq(x_36, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_4);
x_38 = l_Lean_Expr_lam___override(x_2, x_3, x_6, x_5);
return x_38;
}
else
{
size_t x_39; size_t x_40; uint8_t x_41; 
x_39 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_40 = lean_ptr_addr(x_6);
x_41 = lean_usize_dec_eq(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_35);
x_42 = l_Lean_Expr_lam___override(x_2, x_3, x_6, x_5);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_5, x_5);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_35);
x_44 = l_Lean_Expr_lam___override(x_2, x_3, x_6, x_5);
return x_44;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_35;
}
}
}
}
}
else
{
lean_object* x_45; size_t x_46; uint8_t x_47; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_45 = l_Lean_Expr_lam___override(x_2, x_3, x_4, x_5);
x_46 = lean_ptr_addr(x_3);
x_47 = lean_usize_dec_eq(x_46, x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_45);
lean_dec(x_4);
x_48 = l_Lean_Expr_lam___override(x_2, x_3, x_6, x_5);
return x_48;
}
else
{
size_t x_49; size_t x_50; uint8_t x_51; 
x_49 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_50 = lean_ptr_addr(x_6);
x_51 = lean_usize_dec_eq(x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_45);
x_52 = l_Lean_Expr_lam___override(x_2, x_3, x_6, x_5);
return x_52;
}
else
{
uint8_t x_53; 
x_53 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_5, x_5);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_45);
x_54 = l_Lean_Expr_lam___override(x_2, x_3, x_6, x_5);
return x_54;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_45;
}
}
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
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_inc(x_4);
x_5 = l_Lean_Level_instantiateParams(x_1, x_4);
x_6 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_7 = lean_ptr_addr(x_5);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = l_Lean_Expr_sort___override(x_5);
return x_9;
}
else
{
lean_dec(x_5);
return x_2;
}
}
case 4:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Level_instantiateParams), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = lean_box(0);
lean_inc(x_11);
x_14 = l_List_mapTRAux___rarg(x_12, x_11, x_13);
x_15 = l_ptrEqList___rarg(x_11, x_14);
lean_dec(x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = l_Lean_Expr_const___override(x_10, x_14);
return x_16;
}
else
{
lean_dec(x_14);
lean_dec(x_10);
return x_2;
}
}
case 5:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_1);
x_19 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_17);
lean_inc(x_18);
x_20 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_18);
x_21 = lean_ptr_addr(x_17);
lean_dec(x_17);
x_22 = lean_ptr_addr(x_19);
x_23 = lean_usize_dec_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_2);
x_24 = l_Lean_Expr_app___override(x_19, x_20);
return x_24;
}
else
{
size_t x_25; size_t x_26; uint8_t x_27; 
x_25 = lean_ptr_addr(x_18);
lean_dec(x_18);
x_26 = lean_ptr_addr(x_20);
x_27 = lean_usize_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_2);
x_28 = l_Lean_Expr_app___override(x_19, x_20);
return x_28;
}
else
{
lean_dec(x_20);
lean_dec(x_19);
return x_2;
}
}
}
case 6:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; uint8_t x_38; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_30);
lean_inc(x_1);
x_33 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_30);
lean_inc(x_31);
x_34 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_31);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_35 = l_Lean_Expr_lam___override(x_29, x_30, x_31, x_32);
x_36 = lean_ptr_addr(x_30);
lean_dec(x_30);
x_37 = lean_ptr_addr(x_33);
x_38 = lean_usize_dec_eq(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_31);
x_39 = l_Lean_Expr_lam___override(x_29, x_33, x_34, x_32);
return x_39;
}
else
{
size_t x_40; size_t x_41; uint8_t x_42; 
x_40 = lean_ptr_addr(x_31);
lean_dec(x_31);
x_41 = lean_ptr_addr(x_34);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_35);
x_43 = l_Lean_Expr_lam___override(x_29, x_33, x_34, x_32);
return x_43;
}
else
{
uint8_t x_44; 
x_44 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_32, x_32);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_35);
x_45 = l_Lean_Expr_lam___override(x_29, x_33, x_34, x_32);
return x_45;
}
else
{
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
return x_35;
}
}
}
}
case 7:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; uint8_t x_55; 
x_46 = lean_ctor_get(x_2, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
lean_inc(x_47);
lean_inc(x_1);
x_50 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_47);
lean_inc(x_48);
x_51 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_48);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
x_52 = l_Lean_Expr_forallE___override(x_46, x_47, x_48, x_49);
x_53 = lean_ptr_addr(x_47);
lean_dec(x_47);
x_54 = lean_ptr_addr(x_50);
x_55 = lean_usize_dec_eq(x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_52);
lean_dec(x_48);
x_56 = l_Lean_Expr_forallE___override(x_46, x_50, x_51, x_49);
return x_56;
}
else
{
size_t x_57; size_t x_58; uint8_t x_59; 
x_57 = lean_ptr_addr(x_48);
lean_dec(x_48);
x_58 = lean_ptr_addr(x_51);
x_59 = lean_usize_dec_eq(x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_52);
x_60 = l_Lean_Expr_forallE___override(x_46, x_50, x_51, x_49);
return x_60;
}
else
{
uint8_t x_61; 
x_61 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_49, x_49);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_52);
x_62 = l_Lean_Expr_forallE___override(x_46, x_50, x_51, x_49);
return x_62;
}
else
{
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_46);
return x_52;
}
}
}
}
case 8:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; uint8_t x_73; 
x_63 = lean_ctor_get(x_2, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_2, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_2, 3);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_inc(x_64);
lean_inc(x_1);
x_68 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_64);
lean_inc(x_65);
lean_inc(x_1);
x_69 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_65);
lean_inc(x_66);
x_70 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_66);
x_71 = lean_ptr_addr(x_64);
lean_dec(x_64);
x_72 = lean_ptr_addr(x_68);
x_73 = lean_usize_dec_eq(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_2);
x_74 = l_Lean_Expr_letE___override(x_63, x_68, x_69, x_70, x_67);
return x_74;
}
else
{
size_t x_75; size_t x_76; uint8_t x_77; 
x_75 = lean_ptr_addr(x_65);
lean_dec(x_65);
x_76 = lean_ptr_addr(x_69);
x_77 = lean_usize_dec_eq(x_75, x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_66);
lean_dec(x_2);
x_78 = l_Lean_Expr_letE___override(x_63, x_68, x_69, x_70, x_67);
return x_78;
}
else
{
size_t x_79; size_t x_80; uint8_t x_81; 
x_79 = lean_ptr_addr(x_66);
lean_dec(x_66);
x_80 = lean_ptr_addr(x_70);
x_81 = lean_usize_dec_eq(x_79, x_80);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_2);
x_82 = l_Lean_Expr_letE___override(x_63, x_68, x_69, x_70, x_67);
return x_82;
}
else
{
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_63);
return x_2;
}
}
}
}
case 10:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; size_t x_86; size_t x_87; uint8_t x_88; 
x_83 = lean_ctor_get(x_2, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_2, 1);
lean_inc(x_84);
lean_inc(x_84);
x_85 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_84);
x_86 = lean_ptr_addr(x_84);
lean_dec(x_84);
x_87 = lean_ptr_addr(x_85);
x_88 = lean_usize_dec_eq(x_86, x_87);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_2);
x_89 = l_Lean_Expr_mdata___override(x_83, x_85);
return x_89;
}
else
{
lean_dec(x_85);
lean_dec(x_83);
return x_2;
}
}
case 11:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; size_t x_94; size_t x_95; uint8_t x_96; 
x_90 = lean_ctor_get(x_2, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_2, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_2, 2);
lean_inc(x_92);
lean_inc(x_92);
x_93 = l_Lean_Expr_instantiateLevelParamsCore_visit(x_1, x_92);
x_94 = lean_ptr_addr(x_92);
lean_dec(x_92);
x_95 = lean_ptr_addr(x_93);
x_96 = lean_usize_dec_eq(x_94, x_95);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_2);
x_97 = l_Lean_Expr_proj___override(x_90, x_91, x_93);
return x_97;
}
else
{
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_90);
return x_2;
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
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Lean_Level_hasParam(x_3);
if (x_5 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_6 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_4);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_ptr_addr(x_6);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Level_succ___override(x_6);
return x_10;
}
else
{
lean_dec(x_6);
lean_inc(x_3);
return x_3;
}
}
}
case 2:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = l_Lean_Level_hasParam(x_3);
if (x_13 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; uint8_t x_18; 
x_14 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_11);
x_15 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_12);
x_16 = lean_ptr_addr(x_11);
x_17 = lean_ptr_addr(x_14);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_mkLevelMax_x27(x_14, x_15);
return x_19;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_ptr_addr(x_12);
x_21 = lean_ptr_addr(x_15);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_mkLevelMax_x27(x_14, x_15);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = l_Lean_simpLevelMax_x27(x_14, x_15, x_3);
lean_dec(x_15);
lean_dec(x_14);
return x_24;
}
}
}
}
case 3:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
x_27 = l_Lean_Level_hasParam(x_3);
if (x_27 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; uint8_t x_32; 
x_28 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_25);
x_29 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_26);
x_30 = lean_ptr_addr(x_25);
x_31 = lean_ptr_addr(x_28);
x_32 = lean_usize_dec_eq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Lean_mkLevelIMax_x27(x_28, x_29);
return x_33;
}
else
{
size_t x_34; size_t x_35; uint8_t x_36; 
x_34 = lean_ptr_addr(x_26);
x_35 = lean_ptr_addr(x_29);
x_36 = lean_usize_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lean_mkLevelIMax_x27(x_28, x_29);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = l_Lean_simpLevelIMax_x27(x_28, x_29, x_3);
return x_38;
}
}
}
}
case 4:
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_3, 0);
x_40 = l___private_Lean_Expr_0__Lean_Expr_getParamSubst(x_1, x_2, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
return x_41;
}
}
default: 
{
lean_inc(x_3);
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
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Lean_Level_hasParam(x_3);
if (x_5 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_6 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_4);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_ptr_addr(x_6);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Level_succ___override(x_6);
return x_10;
}
else
{
lean_dec(x_6);
lean_inc(x_3);
return x_3;
}
}
}
case 2:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = l_Lean_Level_hasParam(x_3);
if (x_13 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; uint8_t x_18; 
x_14 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_11);
x_15 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_12);
x_16 = lean_ptr_addr(x_11);
x_17 = lean_ptr_addr(x_14);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_mkLevelMax_x27(x_14, x_15);
return x_19;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_ptr_addr(x_12);
x_21 = lean_ptr_addr(x_15);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_mkLevelMax_x27(x_14, x_15);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = l_Lean_simpLevelMax_x27(x_14, x_15, x_3);
lean_dec(x_15);
lean_dec(x_14);
return x_24;
}
}
}
}
case 3:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
x_27 = l_Lean_Level_hasParam(x_3);
if (x_27 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; uint8_t x_32; 
x_28 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_25);
x_29 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__3(x_1, x_2, x_26);
x_30 = lean_ptr_addr(x_25);
x_31 = lean_ptr_addr(x_28);
x_32 = lean_usize_dec_eq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Lean_mkLevelIMax_x27(x_28, x_29);
return x_33;
}
else
{
size_t x_34; size_t x_35; uint8_t x_36; 
x_34 = lean_ptr_addr(x_26);
x_35 = lean_ptr_addr(x_29);
x_36 = lean_usize_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lean_mkLevelIMax_x27(x_28, x_29);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = l_Lean_simpLevelIMax_x27(x_28, x_29, x_3);
return x_38;
}
}
}
}
case 4:
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_3, 0);
x_40 = l___private_Lean_Expr_0__Lean_Expr_getParamSubst(x_1, x_2, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
return x_41;
}
}
default: 
{
lean_inc(x_3);
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
lean_dec(x_7);
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
lean_dec(x_11);
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
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParams___spec__2(x_1, x_2, x_5);
x_7 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_8 = lean_ptr_addr(x_6);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = l_Lean_Expr_sort___override(x_6);
return x_10;
}
else
{
lean_dec(x_6);
return x_3;
}
}
case 4:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_13 = lean_box(0);
lean_inc(x_12);
x_14 = l_List_mapTRAux___at_Lean_Expr_instantiateLevelParams___spec__4(x_1, x_2, x_12, x_13);
x_15 = l_ptrEqList___rarg(x_12, x_14);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = l_Lean_Expr_const___override(x_11, x_14);
return x_16;
}
else
{
lean_dec(x_14);
lean_dec(x_11);
return x_3;
}
}
case 5:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
x_19 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_17);
lean_inc(x_18);
x_20 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_18);
x_21 = lean_ptr_addr(x_17);
lean_dec(x_17);
x_22 = lean_ptr_addr(x_19);
x_23 = lean_usize_dec_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_3);
x_24 = l_Lean_Expr_app___override(x_19, x_20);
return x_24;
}
else
{
size_t x_25; size_t x_26; uint8_t x_27; 
x_25 = lean_ptr_addr(x_18);
lean_dec(x_18);
x_26 = lean_ptr_addr(x_20);
x_27 = lean_usize_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_3);
x_28 = l_Lean_Expr_app___override(x_19, x_20);
return x_28;
}
else
{
lean_dec(x_20);
lean_dec(x_19);
return x_3;
}
}
}
case 6:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; uint8_t x_38; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 2);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_dec(x_3);
lean_inc(x_30);
x_33 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_30);
lean_inc(x_31);
x_34 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_31);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_35 = l_Lean_Expr_lam___override(x_29, x_30, x_31, x_32);
x_36 = lean_ptr_addr(x_30);
lean_dec(x_30);
x_37 = lean_ptr_addr(x_33);
x_38 = lean_usize_dec_eq(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_31);
x_39 = l_Lean_Expr_lam___override(x_29, x_33, x_34, x_32);
return x_39;
}
else
{
size_t x_40; size_t x_41; uint8_t x_42; 
x_40 = lean_ptr_addr(x_31);
lean_dec(x_31);
x_41 = lean_ptr_addr(x_34);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_35);
x_43 = l_Lean_Expr_lam___override(x_29, x_33, x_34, x_32);
return x_43;
}
else
{
uint8_t x_44; 
x_44 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_32, x_32);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_35);
x_45 = l_Lean_Expr_lam___override(x_29, x_33, x_34, x_32);
return x_45;
}
else
{
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
return x_35;
}
}
}
}
case 7:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; uint8_t x_55; 
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_dec(x_3);
lean_inc(x_47);
x_50 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_47);
lean_inc(x_48);
x_51 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_48);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
x_52 = l_Lean_Expr_forallE___override(x_46, x_47, x_48, x_49);
x_53 = lean_ptr_addr(x_47);
lean_dec(x_47);
x_54 = lean_ptr_addr(x_50);
x_55 = lean_usize_dec_eq(x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_52);
lean_dec(x_48);
x_56 = l_Lean_Expr_forallE___override(x_46, x_50, x_51, x_49);
return x_56;
}
else
{
size_t x_57; size_t x_58; uint8_t x_59; 
x_57 = lean_ptr_addr(x_48);
lean_dec(x_48);
x_58 = lean_ptr_addr(x_51);
x_59 = lean_usize_dec_eq(x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_52);
x_60 = l_Lean_Expr_forallE___override(x_46, x_50, x_51, x_49);
return x_60;
}
else
{
uint8_t x_61; 
x_61 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_49, x_49);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_52);
x_62 = l_Lean_Expr_forallE___override(x_46, x_50, x_51, x_49);
return x_62;
}
else
{
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_46);
return x_52;
}
}
}
}
case 8:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; uint8_t x_73; 
x_63 = lean_ctor_get(x_3, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_3, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_3, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_3, 3);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 8);
lean_inc(x_64);
x_68 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_64);
lean_inc(x_65);
x_69 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_65);
lean_inc(x_66);
x_70 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_66);
x_71 = lean_ptr_addr(x_64);
lean_dec(x_64);
x_72 = lean_ptr_addr(x_68);
x_73 = lean_usize_dec_eq(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_3);
x_74 = l_Lean_Expr_letE___override(x_63, x_68, x_69, x_70, x_67);
return x_74;
}
else
{
size_t x_75; size_t x_76; uint8_t x_77; 
x_75 = lean_ptr_addr(x_65);
lean_dec(x_65);
x_76 = lean_ptr_addr(x_69);
x_77 = lean_usize_dec_eq(x_75, x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_66);
lean_dec(x_3);
x_78 = l_Lean_Expr_letE___override(x_63, x_68, x_69, x_70, x_67);
return x_78;
}
else
{
size_t x_79; size_t x_80; uint8_t x_81; 
x_79 = lean_ptr_addr(x_66);
lean_dec(x_66);
x_80 = lean_ptr_addr(x_70);
x_81 = lean_usize_dec_eq(x_79, x_80);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_3);
x_82 = l_Lean_Expr_letE___override(x_63, x_68, x_69, x_70, x_67);
return x_82;
}
else
{
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_63);
return x_3;
}
}
}
}
case 10:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; size_t x_86; size_t x_87; uint8_t x_88; 
x_83 = lean_ctor_get(x_3, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_3, 1);
lean_inc(x_84);
lean_inc(x_84);
x_85 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_84);
x_86 = lean_ptr_addr(x_84);
lean_dec(x_84);
x_87 = lean_ptr_addr(x_85);
x_88 = lean_usize_dec_eq(x_86, x_87);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_3);
x_89 = l_Lean_Expr_mdata___override(x_83, x_85);
return x_89;
}
else
{
lean_dec(x_85);
lean_dec(x_83);
return x_3;
}
}
case 11:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; size_t x_94; size_t x_95; uint8_t x_96; 
x_90 = lean_ctor_get(x_3, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_3, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_3, 2);
lean_inc(x_92);
lean_inc(x_92);
x_93 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParams___spec__1(x_1, x_2, x_92);
x_94 = lean_ptr_addr(x_92);
lean_dec(x_92);
x_95 = lean_ptr_addr(x_93);
x_96 = lean_usize_dec_eq(x_94, x_95);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_3);
x_97 = l_Lean_Expr_proj___override(x_90, x_91, x_93);
return x_97;
}
else
{
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_90);
return x_3;
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Lean_Level_hasParam(x_3);
if (x_5 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_6 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_4);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_ptr_addr(x_6);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Level_succ___override(x_6);
return x_10;
}
else
{
lean_dec(x_6);
lean_inc(x_3);
return x_3;
}
}
}
case 2:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = l_Lean_Level_hasParam(x_3);
if (x_13 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; uint8_t x_18; 
x_14 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_11);
x_15 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_12);
x_16 = lean_ptr_addr(x_11);
x_17 = lean_ptr_addr(x_14);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_mkLevelMax_x27(x_14, x_15);
return x_19;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_ptr_addr(x_12);
x_21 = lean_ptr_addr(x_15);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_mkLevelMax_x27(x_14, x_15);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = l_Lean_simpLevelMax_x27(x_14, x_15, x_3);
lean_dec(x_15);
lean_dec(x_14);
return x_24;
}
}
}
}
case 3:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
x_27 = l_Lean_Level_hasParam(x_3);
if (x_27 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; uint8_t x_32; 
x_28 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_25);
x_29 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_26);
x_30 = lean_ptr_addr(x_25);
x_31 = lean_ptr_addr(x_28);
x_32 = lean_usize_dec_eq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Lean_mkLevelIMax_x27(x_28, x_29);
return x_33;
}
else
{
size_t x_34; size_t x_35; uint8_t x_36; 
x_34 = lean_ptr_addr(x_26);
x_35 = lean_ptr_addr(x_29);
x_36 = lean_usize_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lean_mkLevelIMax_x27(x_28, x_29);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = l_Lean_simpLevelIMax_x27(x_28, x_29, x_3);
return x_38;
}
}
}
}
case 4:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_3, 0);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l___private_Lean_Expr_0__Lean_Expr_getParamSubstArray(x_1, x_2, x_39, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
return x_42;
}
}
default: 
{
lean_inc(x_3);
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
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Lean_Level_hasParam(x_3);
if (x_5 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_6 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_4);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_ptr_addr(x_6);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Level_succ___override(x_6);
return x_10;
}
else
{
lean_dec(x_6);
lean_inc(x_3);
return x_3;
}
}
}
case 2:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = l_Lean_Level_hasParam(x_3);
if (x_13 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; uint8_t x_18; 
x_14 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_11);
x_15 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_12);
x_16 = lean_ptr_addr(x_11);
x_17 = lean_ptr_addr(x_14);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_mkLevelMax_x27(x_14, x_15);
return x_19;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_ptr_addr(x_12);
x_21 = lean_ptr_addr(x_15);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_mkLevelMax_x27(x_14, x_15);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = l_Lean_simpLevelMax_x27(x_14, x_15, x_3);
lean_dec(x_15);
lean_dec(x_14);
return x_24;
}
}
}
}
case 3:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
x_27 = l_Lean_Level_hasParam(x_3);
if (x_27 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; uint8_t x_32; 
x_28 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_25);
x_29 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__3(x_1, x_2, x_26);
x_30 = lean_ptr_addr(x_25);
x_31 = lean_ptr_addr(x_28);
x_32 = lean_usize_dec_eq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Lean_mkLevelIMax_x27(x_28, x_29);
return x_33;
}
else
{
size_t x_34; size_t x_35; uint8_t x_36; 
x_34 = lean_ptr_addr(x_26);
x_35 = lean_ptr_addr(x_29);
x_36 = lean_usize_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lean_mkLevelIMax_x27(x_28, x_29);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = l_Lean_simpLevelIMax_x27(x_28, x_29, x_3);
return x_38;
}
}
}
}
case 4:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_3, 0);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l___private_Lean_Expr_0__Lean_Expr_getParamSubstArray(x_1, x_2, x_39, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
return x_42;
}
}
default: 
{
lean_inc(x_3);
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
lean_dec(x_7);
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
lean_dec(x_11);
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
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = l_Lean_Level_instantiateParams___at_Lean_Expr_instantiateLevelParamsArray___spec__2(x_1, x_2, x_5);
x_7 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_8 = lean_ptr_addr(x_6);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = l_Lean_Expr_sort___override(x_6);
return x_10;
}
else
{
lean_dec(x_6);
return x_3;
}
}
case 4:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_13 = lean_box(0);
lean_inc(x_12);
x_14 = l_List_mapTRAux___at_Lean_Expr_instantiateLevelParamsArray___spec__4(x_1, x_2, x_12, x_13);
x_15 = l_ptrEqList___rarg(x_12, x_14);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = l_Lean_Expr_const___override(x_11, x_14);
return x_16;
}
else
{
lean_dec(x_14);
lean_dec(x_11);
return x_3;
}
}
case 5:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
x_19 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_17);
lean_inc(x_18);
x_20 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_18);
x_21 = lean_ptr_addr(x_17);
lean_dec(x_17);
x_22 = lean_ptr_addr(x_19);
x_23 = lean_usize_dec_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_3);
x_24 = l_Lean_Expr_app___override(x_19, x_20);
return x_24;
}
else
{
size_t x_25; size_t x_26; uint8_t x_27; 
x_25 = lean_ptr_addr(x_18);
lean_dec(x_18);
x_26 = lean_ptr_addr(x_20);
x_27 = lean_usize_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_3);
x_28 = l_Lean_Expr_app___override(x_19, x_20);
return x_28;
}
else
{
lean_dec(x_20);
lean_dec(x_19);
return x_3;
}
}
}
case 6:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; uint8_t x_38; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 2);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_dec(x_3);
lean_inc(x_30);
x_33 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_30);
lean_inc(x_31);
x_34 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_31);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_35 = l_Lean_Expr_lam___override(x_29, x_30, x_31, x_32);
x_36 = lean_ptr_addr(x_30);
lean_dec(x_30);
x_37 = lean_ptr_addr(x_33);
x_38 = lean_usize_dec_eq(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_31);
x_39 = l_Lean_Expr_lam___override(x_29, x_33, x_34, x_32);
return x_39;
}
else
{
size_t x_40; size_t x_41; uint8_t x_42; 
x_40 = lean_ptr_addr(x_31);
lean_dec(x_31);
x_41 = lean_ptr_addr(x_34);
x_42 = lean_usize_dec_eq(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_35);
x_43 = l_Lean_Expr_lam___override(x_29, x_33, x_34, x_32);
return x_43;
}
else
{
uint8_t x_44; 
x_44 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_32, x_32);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_35);
x_45 = l_Lean_Expr_lam___override(x_29, x_33, x_34, x_32);
return x_45;
}
else
{
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
return x_35;
}
}
}
}
case 7:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; uint8_t x_55; 
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_dec(x_3);
lean_inc(x_47);
x_50 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_47);
lean_inc(x_48);
x_51 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_48);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
x_52 = l_Lean_Expr_forallE___override(x_46, x_47, x_48, x_49);
x_53 = lean_ptr_addr(x_47);
lean_dec(x_47);
x_54 = lean_ptr_addr(x_50);
x_55 = lean_usize_dec_eq(x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_52);
lean_dec(x_48);
x_56 = l_Lean_Expr_forallE___override(x_46, x_50, x_51, x_49);
return x_56;
}
else
{
size_t x_57; size_t x_58; uint8_t x_59; 
x_57 = lean_ptr_addr(x_48);
lean_dec(x_48);
x_58 = lean_ptr_addr(x_51);
x_59 = lean_usize_dec_eq(x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_52);
x_60 = l_Lean_Expr_forallE___override(x_46, x_50, x_51, x_49);
return x_60;
}
else
{
uint8_t x_61; 
x_61 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_49, x_49);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_52);
x_62 = l_Lean_Expr_forallE___override(x_46, x_50, x_51, x_49);
return x_62;
}
else
{
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_46);
return x_52;
}
}
}
}
case 8:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; uint8_t x_73; 
x_63 = lean_ctor_get(x_3, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_3, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_3, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_3, 3);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 8);
lean_inc(x_64);
x_68 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_64);
lean_inc(x_65);
x_69 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_65);
lean_inc(x_66);
x_70 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_66);
x_71 = lean_ptr_addr(x_64);
lean_dec(x_64);
x_72 = lean_ptr_addr(x_68);
x_73 = lean_usize_dec_eq(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_3);
x_74 = l_Lean_Expr_letE___override(x_63, x_68, x_69, x_70, x_67);
return x_74;
}
else
{
size_t x_75; size_t x_76; uint8_t x_77; 
x_75 = lean_ptr_addr(x_65);
lean_dec(x_65);
x_76 = lean_ptr_addr(x_69);
x_77 = lean_usize_dec_eq(x_75, x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_66);
lean_dec(x_3);
x_78 = l_Lean_Expr_letE___override(x_63, x_68, x_69, x_70, x_67);
return x_78;
}
else
{
size_t x_79; size_t x_80; uint8_t x_81; 
x_79 = lean_ptr_addr(x_66);
lean_dec(x_66);
x_80 = lean_ptr_addr(x_70);
x_81 = lean_usize_dec_eq(x_79, x_80);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_3);
x_82 = l_Lean_Expr_letE___override(x_63, x_68, x_69, x_70, x_67);
return x_82;
}
else
{
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_63);
return x_3;
}
}
}
}
case 10:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; size_t x_86; size_t x_87; uint8_t x_88; 
x_83 = lean_ctor_get(x_3, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_3, 1);
lean_inc(x_84);
lean_inc(x_84);
x_85 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_84);
x_86 = lean_ptr_addr(x_84);
lean_dec(x_84);
x_87 = lean_ptr_addr(x_85);
x_88 = lean_usize_dec_eq(x_86, x_87);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_3);
x_89 = l_Lean_Expr_mdata___override(x_83, x_85);
return x_89;
}
else
{
lean_dec(x_85);
lean_dec(x_83);
return x_3;
}
}
case 11:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; size_t x_94; size_t x_95; uint8_t x_96; 
x_90 = lean_ctor_get(x_3, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_3, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_3, 2);
lean_inc(x_92);
lean_inc(x_92);
x_93 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_1, x_2, x_92);
x_94 = lean_ptr_addr(x_92);
lean_dec(x_92);
x_95 = lean_ptr_addr(x_93);
x_96 = lean_usize_dec_eq(x_94, x_95);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_3);
x_97 = l_Lean_Expr_proj___override(x_90, x_91, x_93);
return x_97;
}
else
{
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_90);
return x_3;
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
lean_dec(x_3);
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
lean_dec(x_3);
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
x_9 = l_Lean_Expr_mdata___override(x_8, x_1);
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
x_7 = l_Lean_Expr_mdata___override(x_6, x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Expr_setPPExplicit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pp", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_setPPExplicit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_setPPExplicit___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_setPPExplicit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("explicit", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_setPPExplicit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_setPPExplicit___closed__2;
x_2 = l_Lean_Expr_setPPExplicit___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
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
x_1 = lean_mk_string_from_bytes("universes", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_setPPUniverses___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_setPPExplicit___closed__2;
x_2 = l_Lean_Expr_setPPUniverses___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
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
x_6 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_5);
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
x_6 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_5);
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
x_6 = l_Lean_Expr_mdata___override(x_5, x_2);
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
x_1 = lean_mk_string_from_bytes("let_fun", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_mkLetFunAnnotation___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkLetFunAnnotation___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
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
x_1 = lean_mk_string_from_bytes("_inaccessible", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_mkInaccessible___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkInaccessible___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
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
static lean_object* _init_l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_patWithRef", 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Expr_0__Lean_patternRefAnnotationKey() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l___private_Lean_Expr_0__Lean_patternRefAnnotationKey;
x_4 = l_Lean_KVMap_findCore(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Expr_mdataExpr_x21(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; 
lean_free_object(x_4);
lean_dec(x_7);
x_11 = lean_box(0);
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
if (lean_obj_tag(x_12) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Expr_mdataExpr_x21(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
x_17 = lean_box(0);
return x_17;
}
}
}
}
else
{
lean_object* x_18; 
x_18 = lean_box(0);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternWithRef_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_patternWithRef_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPatternWithRef(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_patternWithRef_x3f(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Lean_KVMap_empty;
x_6 = l___private_Lean_Expr_0__Lean_patternRefAnnotationKey;
x_7 = l_Lean_KVMap_insertCore(x_5, x_6, x_4);
x_8 = l_Lean_Expr_mdata___override(x_7, x_1);
return x_8;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_inaccessible_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_patternWithRef_x3f(x_1);
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
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_patternAnnotation_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_patternAnnotation_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkLHSGoal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_lhsGoal", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_mkLHSGoal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkLHSGoal___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
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
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_isLHSGoal_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_isLHSGoal_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___rarg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkFreshLMVarId___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_mkNot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Not", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_mkNot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkNot___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkNot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkNot___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkNot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkNot___closed__3;
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_mkOr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Or", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_mkOr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkOr___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkOr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkOr___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_1 = lean_mk_string_from_bytes("And", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkAnd___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkAnd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkAnd___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_1 = lean_mk_string_from_bytes("Classical", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_mkEM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkEM___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkEM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("em", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_mkEM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkEM___closed__2;
x_2 = l_Lean_mkEM___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkEM___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkEM___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkEM(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkEM___closed__5;
x_3 = l_Lean_Expr_app___override(x_2, x_1);
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
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__1 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__1);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__2 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__2);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__3 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__3();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__3);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__4);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__5);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__6 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__6();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__6);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__7 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__7();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__7);
l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__8 = _init_l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__8();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113____closed__8);
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
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__1 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__1);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__2 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__2);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__3 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__3();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__3);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__4 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__4();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__4);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__5 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__5();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__5);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__6 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__6();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__6);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__7 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__7();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__7);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__8 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__8();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__8);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__9 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__9();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__9);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__10 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__10();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__10);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__11 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__11();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__11);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__12 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__12();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__12);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__13 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__13();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__13);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__14 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__14();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__14);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__15 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__15();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__15);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__16 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__16();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__16);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__17 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__17();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__17);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__18 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__18();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__18);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__19 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__19();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__19);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__20 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__20();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__20);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__21 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__21();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__21);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__22 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__22();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__22);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__23 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__23();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__23);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__24 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__24();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__24);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__25 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__25();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__25);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__26 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__26();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__26);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__27 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__27();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__27);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__28 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__28();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__28);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__29 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__29();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__29);
l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__30 = _init_l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__30();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprBinderInfo____x40_Lean_Expr___hyg_387____closed__30);
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
l_Lean_Expr_mkData___closed__6 = _init_l_Lean_Expr_mkData___closed__6();
lean_mark_persistent(l_Lean_Expr_mkData___closed__6);
l_Lean_Expr_mkData___closed__7 = _init_l_Lean_Expr_mkData___closed__7();
lean_mark_persistent(l_Lean_Expr_mkData___closed__7);
l_Lean_Expr_mkAppData___closed__1 = _init_l_Lean_Expr_mkAppData___closed__1();
l_Lean_Expr_mkAppData___closed__2 = _init_l_Lean_Expr_mkAppData___closed__2();
lean_mark_persistent(l_Lean_Expr_mkAppData___closed__2);
l_Lean_Expr_mkAppData___closed__3 = _init_l_Lean_Expr_mkAppData___closed__3();
lean_mark_persistent(l_Lean_Expr_mkAppData___closed__3);
l_Lean_Expr_mkAppData___closed__4 = _init_l_Lean_Expr_mkAppData___closed__4();
lean_mark_persistent(l_Lean_Expr_mkAppData___closed__4);
l_Lean_Expr_mkAppData___closed__5 = _init_l_Lean_Expr_mkAppData___closed__5();
lean_mark_persistent(l_Lean_Expr_mkAppData___closed__5);
l_Lean_Expr_mkAppData___closed__6 = _init_l_Lean_Expr_mkAppData___closed__6();
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
l_Lean_instInhabitedMVarId = _init_l_Lean_instInhabitedMVarId();
lean_mark_persistent(l_Lean_instInhabitedMVarId);
l_Lean_instBEqMVarId___closed__1 = _init_l_Lean_instBEqMVarId___closed__1();
lean_mark_persistent(l_Lean_instBEqMVarId___closed__1);
l_Lean_instBEqMVarId = _init_l_Lean_instBEqMVarId();
lean_mark_persistent(l_Lean_instBEqMVarId);
l_Lean_instHashableMVarId___closed__1 = _init_l_Lean_instHashableMVarId___closed__1();
lean_mark_persistent(l_Lean_instHashableMVarId___closed__1);
l_Lean_instHashableMVarId = _init_l_Lean_instHashableMVarId();
lean_mark_persistent(l_Lean_instHashableMVarId);
l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__1 = _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__1);
l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__2 = _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__2);
l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__3 = _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__3();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__3);
l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__4 = _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__4();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__4);
l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__5 = _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__5();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__5);
l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__6 = _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__6();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__6);
l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__7 = _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__7();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__7);
l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__8 = _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__8();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__8);
l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__9 = _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__9();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__9);
l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__10 = _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__10();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__10);
l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__11 = _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__11();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__11);
l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__12 = _init_l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__12();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprMVarId____x40_Lean_Expr___hyg_2167____closed__12);
l_Lean_instReprMVarId___closed__1 = _init_l_Lean_instReprMVarId___closed__1();
lean_mark_persistent(l_Lean_instReprMVarId___closed__1);
l_Lean_instReprMVarId = _init_l_Lean_instReprMVarId();
lean_mark_persistent(l_Lean_instReprMVarId);
l_Lean_instMVarIdSetInhabited = _init_l_Lean_instMVarIdSetInhabited();
lean_mark_persistent(l_Lean_instMVarIdSetInhabited);
l_Lean_instMVarIdSetEmptyCollection = _init_l_Lean_instMVarIdSetEmptyCollection();
lean_mark_persistent(l_Lean_instMVarIdSetEmptyCollection);
l_Lean_instForInMVarIdMapProdMVarId___closed__1 = _init_l_Lean_instForInMVarIdMapProdMVarId___closed__1();
lean_mark_persistent(l_Lean_instForInMVarIdMapProdMVarId___closed__1);
l_Lean_instInhabitedExpr___closed__1 = _init_l_Lean_instInhabitedExpr___closed__1();
lean_mark_persistent(l_Lean_instInhabitedExpr___closed__1);
l_Lean_instInhabitedExpr = _init_l_Lean_instInhabitedExpr();
lean_mark_persistent(l_Lean_instInhabitedExpr);
l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__1 = _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__1();
lean_mark_persistent(l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__1);
l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__2 = _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__2();
lean_mark_persistent(l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__2);
l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__3 = _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__3();
lean_mark_persistent(l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__3);
l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__4 = _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__4();
lean_mark_persistent(l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__4);
l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__5 = _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__5();
lean_mark_persistent(l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__5);
l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__6 = _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__6();
lean_mark_persistent(l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__6);
l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__7 = _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__7();
lean_mark_persistent(l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__7);
l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__8 = _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__8();
lean_mark_persistent(l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__8);
l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__9 = _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__9();
lean_mark_persistent(l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__9);
l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__10 = _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__10();
lean_mark_persistent(l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__10);
l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__11 = _init_l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__11();
lean_mark_persistent(l_List_repr___at___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____spec__1___closed__11);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__1 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__1);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__2 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__2);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__3 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__3();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__3);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__4 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__4();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__4);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__5 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__5();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__5);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__6 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__6();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__6);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__7 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__7();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__7);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__8 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__8();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__8);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__9 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__9();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__9);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__10 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__10();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__10);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__11 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__11();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__11);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__12 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__12();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__12);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__13 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__13();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__13);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__14 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__14();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__14);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__15 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__15();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__15);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__16 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__16();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__16);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__17 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__17();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__17);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__18 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__18();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__18);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__19 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__19();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__19);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__20 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__20();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__20);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__21 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__21();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__21);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__22 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__22();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__22);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__23 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__23();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__23);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__24 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__24();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__24);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__25 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__25();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__25);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__26 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__26();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__26);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__27 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__27();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__27);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__28 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__28();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__28);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__29 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__29();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__29);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__30 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__30();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__30);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__31 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__31();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__31);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__32 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__32();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__32);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__33 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__33();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__33);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__34 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__34();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__34);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__35 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__35();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__35);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__36 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__36();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__36);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__37 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__37();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__37);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__38 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__38();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__38);
l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__39 = _init_l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__39();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_reprExpr____x40_Lean_Expr___hyg_3113____closed__39);
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
l_Lean_Expr_withAppAux___at_Lean_Expr_traverseApp___spec__1___rarg___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Expr_traverseApp___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Expr_traverseApp___spec__1___rarg___closed__1);
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
l_Lean_Expr_appFn_x21_x27___closed__1 = _init_l_Lean_Expr_appFn_x21_x27___closed__1();
lean_mark_persistent(l_Lean_Expr_appFn_x21_x27___closed__1);
l_Lean_Expr_appFn_x21_x27___closed__2 = _init_l_Lean_Expr_appFn_x21_x27___closed__2();
lean_mark_persistent(l_Lean_Expr_appFn_x21_x27___closed__2);
l_Lean_Expr_appArg_x21_x27___closed__1 = _init_l_Lean_Expr_appArg_x21_x27___closed__1();
lean_mark_persistent(l_Lean_Expr_appArg_x21_x27___closed__1);
l_Lean_Expr_appArg_x21_x27___closed__2 = _init_l_Lean_Expr_appArg_x21_x27___closed__2();
lean_mark_persistent(l_Lean_Expr_appArg_x21_x27___closed__2);
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
l_Lean_Expr_isOutParam___closed__1 = _init_l_Lean_Expr_isOutParam___closed__1();
lean_mark_persistent(l_Lean_Expr_isOutParam___closed__1);
l_Lean_Expr_isOutParam___closed__2 = _init_l_Lean_Expr_isOutParam___closed__2();
lean_mark_persistent(l_Lean_Expr_isOutParam___closed__2);
l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1 = _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__1);
l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__2 = _init_l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___closed__2);
l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1 = _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__1);
l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__2 = _init_l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateConst_x21Impl___closed__2);
l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1 = _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__1);
l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2 = _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__2);
l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__3 = _init_l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__3();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateSort_x21Impl___closed__3);
l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1 = _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__1);
l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2 = _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__2);
l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__3 = _init_l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__3();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl___closed__3);
l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1 = _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__1);
l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2 = _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__2);
l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__3 = _init_l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__3();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl___closed__3);
l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1 = _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__1);
l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2 = _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__2);
l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__3 = _init_l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__3();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateForall_x21Impl___closed__3);
l_Lean_Expr_updateForallE_x21___closed__1 = _init_l_Lean_Expr_updateForallE_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateForallE_x21___closed__1);
l_Lean_Expr_updateForallE_x21___closed__2 = _init_l_Lean_Expr_updateForallE_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_updateForallE_x21___closed__2);
l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1 = _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__1);
l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2 = _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__2);
l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__3 = _init_l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__3();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateLambda_x21Impl___closed__3);
l_Lean_Expr_updateLambdaE_x21___closed__1 = _init_l_Lean_Expr_updateLambdaE_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateLambdaE_x21___closed__1);
l_Lean_Expr_updateLambdaE_x21___closed__2 = _init_l_Lean_Expr_updateLambdaE_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_updateLambdaE_x21___closed__2);
l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1 = _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__1);
l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__2 = _init_l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_Expr_updateLet_x21Impl___closed__2);
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
l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__1 = _init_l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__1();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__1);
l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__2 = _init_l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__2();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey___closed__2);
l___private_Lean_Expr_0__Lean_patternRefAnnotationKey = _init_l___private_Lean_Expr_0__Lean_patternRefAnnotationKey();
lean_mark_persistent(l___private_Lean_Expr_0__Lean_patternRefAnnotationKey);
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
