// Lean compiler output
// Module: Init.Lean.Expr
// Imports: Init.Lean.Level Init.Lean.KVMap Init.Data.HashMap.Default Init.Data.HashSet Init.Data.PersistentHashMap.Default Init.Data.PersistentHashSet
#include "runtime/lean.h"
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
uint8_t l_Lean_ExprCachedData_hasLevelMVar(uint64_t);
lean_object* l_Lean_Expr_hasLooseBVars___boxed(lean_object*);
lean_object* lean_expr_mk_mdata(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN___boxed(lean_object*, lean_object*);
uint8_t lean_expr_has_fvar(lean_object*);
uint64_t l_UInt32_toUInt64(uint32_t);
lean_object* l_Lean_Expr_getAppNumArgsAux___main___boxed(lean_object*, lean_object*);
uint64_t l_Lean_mkExprCachedData___closed__2;
uint32_t l_Lean_ExprCachedData_looseBVarRange(uint64_t);
lean_object* l_Lean_Expr_lam___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Literal_type___closed__5;
uint8_t lean_expr_quick_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Lean_Expr_bvarIdx_x21___closed__2;
lean_object* l___private_Init_Lean_Expr_6__withAppRevAux___main(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_Literal_type___boxed(lean_object*);
lean_object* l_Lean_Expr_updateProj___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21___boxed(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_HasRepr(lean_object*);
lean_object* l_Lean_MData_empty;
lean_object* lean_expr_mk_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_expr_mk_sort(lean_object*);
extern lean_object* l_Nat_Inhabited;
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateSort___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getLooseBVarRange___boxed(lean_object*);
lean_object* l_Lean_Expr_getAppRevArgs(lean_object*);
lean_object* l_Lean_Expr_updateConst___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isLambda___boxed(lean_object*);
lean_object* l_Lean_Expr_withApp(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* l_Lean_Expr_bvarIdx_x21(lean_object*);
lean_object* l_Lean_Literal_type___closed__2;
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_forallE___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_mkAppRev___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_mkExprCachedData___closed__4;
lean_object* l_Lean_Expr_HasBeq___closed__1;
lean_object* l_Lean_Expr_bindingBody_x21___boxed(lean_object*);
lean_object* l_Lean_Expr_isAppOfArity___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateLambda_x21(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_7__mkAppRevRangeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_ExprCachedData_hash___boxed(lean_object*);
lean_object* l_Lean_BinderInfo_isAuxDecl___boxed(lean_object*);
lean_object* l_Lean_Expr_updateMData_x21___closed__2;
lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_exprToExprStructEq(lean_object*);
size_t lean_expr_hash(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21___boxed(lean_object*);
extern lean_object* l_List_get_x21___main___rarg___closed__2;
lean_object* l_Lean_Expr_updateLambda_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hasLooseBVar___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_Hashable;
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* lean_expr_mk_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiate1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_8__betaRevAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_BinderInfo_toUInt64(uint8_t);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkDecIsTrue___closed__4;
uint8_t l_Lean_ExprCachedData_hasLevelParam(uint64_t);
lean_object* l_Lean_Expr_withAppRev(lean_object*);
uint8_t l_UInt64_decEq(uint64_t, uint64_t);
lean_object* l_Lean_ExprStructEq_HasBeq___closed__1;
lean_object* lean_expr_get_loose_bvar_range(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21___closed__2;
lean_object* l_Lean_Expr_isBVar___boxed(lean_object*);
lean_object* lean_expr_instantiate(lean_object*, lean_object*);
uint8_t l_Lean_ExprCachedData_hasExprMVar(uint64_t);
lean_object* l_Lean_Expr_letName_x21___closed__2;
lean_object* l_Lean_Expr_getAppNumArgsAux___boxed(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_mk_app(lean_object*, lean_object*);
lean_object* l_Lean_Expr_quickLt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object*);
lean_object* l_Lean_Expr_isAppOf___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateLet_x21(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_BinderInfo_toUInt64___boxed(lean_object*);
lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_mkLet(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_7__mkAppRevRangeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_exprToExprStructEq___boxed(lean_object*);
uint64_t l_Lean_ExprCachedData_inhabited;
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
extern lean_object* l_Lean_Inhabited;
lean_object* l_Lean_mkDecIsFalse___closed__1;
lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_Literal_type(lean_object*);
lean_object* l_Lean_mkDecIsTrue___closed__3;
lean_object* l_Lean_Expr_isProj___boxed(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Expr_equal___boxed(lean_object*, lean_object*);
uint64_t l_UInt64_add(uint64_t, uint64_t);
lean_object* l_Lean_Expr_isConstOf___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Literal_Inhabited___closed__1;
lean_object* l_Lean_Expr_hasMVar___boxed(lean_object*);
uint64_t l_Lean_mkExprCachedData(size_t, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* l_Lean_Expr_sort___boxed(lean_object*);
lean_object* l_Lean_Expr_HasToString___closed__1;
uint64_t l_Bool_toUInt64(uint8_t);
lean_object* l_Lean_ExprStructEq_HasToString(lean_object*);
lean_object* l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__1;
lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_mkAppRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateMData_x21(lean_object*, lean_object*);
lean_object* lean_expr_mk_fvar(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_withAppAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21___closed__1;
lean_object* l___private_Init_Lean_Expr_10__etaExpandedAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___boxed(lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_8__betaRevAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__4;
lean_object* l_Lean_ExprCachedData_hasLevelParam___boxed(lean_object*);
lean_object* l_Lean_Expr_constName_x21___closed__2;
uint64_t l_Lean_mkExprCachedData___closed__1;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_BinderInfo_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ExprCachedData_nonDepLet___boxed(lean_object*);
lean_object* l_Lean_mkCAppN(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
uint64_t l_UInt64_shiftRight(uint64_t, uint64_t);
lean_object* l_Lean_Expr_bvarIdx_x21___closed__1;
extern uint64_t l_UInt64_Inhabited;
lean_object* l_Lean_Expr_updateFn___main___boxed(lean_object*, lean_object*);
uint32_t l_UInt64_toUInt32(uint64_t);
lean_object* l_Lean_Expr_getRevArgD(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkExprCachedData___boxed__const__1;
lean_object* lean_expr_mk_proj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateForall_x21___closed__1;
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
uint8_t l_Lean_BinderInfo_isAuxDecl(uint8_t);
lean_object* l_Lean_Expr_isMData___boxed(lean_object*);
lean_object* lean_expr_mk_const(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___boxed(lean_object*);
lean_object* l_Lean_Expr_updateForall_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_Hashable___closed__1;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateMData___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___main___closed__1;
lean_object* l_Lean_Expr_withAppRev___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21___boxed(lean_object*);
lean_object* l_Lean_MData_HasEmptyc;
lean_object* l_Lean_Expr_updateForall_x21(lean_object*, uint8_t, lean_object*, lean_object*);
uint64_t l_UInt64_shiftLeft(uint64_t, uint64_t);
lean_object* l_Lean_ExprStructEq_HasBeq;
lean_object* l_Lean_Expr_updateProj_x21___closed__1;
lean_object* l_Lean_Expr_isApp___boxed(lean_object*);
lean_object* l___private_Init_Lean_Expr_7__mkAppRevRangeAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21___boxed(lean_object*);
lean_object* l_Lean_Expr_getArgD(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_HasRepr___boxed(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Literal_type___closed__6;
lean_object* l_Lean_BinderInfo_HasBeq;
lean_object* l_Lean_Expr_dbgToString___boxed(lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateSort_x21___closed__2;
lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Expr_appFn_x21___closed__1;
uint64_t l_Lean_mkExprCachedDataForLet(size_t, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* l_Lean_Expr_updateForallE_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withApp___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_5__getAppRevArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiate___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21___closed__1;
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Literal_Inhabited;
lean_object* lean_expr_update_const(lean_object*, lean_object*);
uint8_t l_Lean_ExprCachedData_binderInfo(uint64_t);
lean_object* l_Lean_mkExprCachedDataForLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkExprCachedDataForBinder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letName_x21(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_mkDecIsTrue___closed__1;
lean_object* l_Lean_Expr_constName_x21___boxed(lean_object*);
lean_object* l___private_Init_Lean_Expr_3__mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateFn(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux(lean_object*);
lean_object* l_Lean_mkDecIsFalse(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___boxed(lean_object*);
lean_object* l_Lean_Expr_HasRepr;
uint8_t l_Lean_ExprCachedData_nonDepLet(uint64_t);
lean_object* l___private_Init_Lean_Expr_3__mkAppRangeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateApp_x21___closed__1;
lean_object* l_Lean_Expr_constLevels_x21___closed__1;
lean_object* l_Lean_mkExprCachedDataForLet___boxed__const__1;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_mkExprCachedData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_8__betaRevAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ExprCachedData_looseBVarRange___boxed(lean_object*);
lean_object* l_Lean_Expr_updateLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___boxed(lean_object*, lean_object*);
uint64_t l_Lean_mkExprCachedData___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateLet_x21___closed__1;
lean_object* l_Lean_mkDecIsTrue___closed__2;
lean_object* l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__3;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_mkAppRev___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
size_t l_UInt32_toUSize(uint32_t);
lean_object* l_Lean_Expr_getAppArgs(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArgD___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_8__betaRevAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main___boxed(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_mkCAppN___boxed(lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21___closed__1;
lean_object* l_Lean_ExprStructEq_hash___boxed(lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21___boxed(lean_object*);
lean_object* l_Lean_Expr_updateLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateConst_x21___closed__1;
lean_object* l_Lean_mkDecIsTrue___closed__5;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hasFVar___boxed(lean_object*);
lean_object* l_Lean_Expr_inhabited;
lean_object* l___private_Init_Lean_Expr_2__mkExprCachedDataCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_HasToString;
lean_object* l_Lean_ExprCachedData_hasFVar___boxed(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isBinding(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21___closed__2;
lean_object* l_Lean_Expr_appFn_x21___closed__2;
lean_object* lean_expr_mk_mvar(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_expr_mk_bvar(lean_object*);
lean_object* l_Lean_Expr_letName_x21___boxed(lean_object*);
lean_object* l_Lean_Expr_getArg_x21___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_lparams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main(lean_object*);
lean_object* l_Lean_Expr_letName_x21___closed__1;
lean_object* l___private_Init_Lean_Expr_6__withAppRevAux___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateLambda_x21___closed__2;
lean_object* l_Lean_Expr_appArg_x21___boxed(lean_object*);
lean_object* l_Lean_Expr_updateConst_x21(lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateLambda_x21___closed__1;
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_BinderInfo_HasBeq___closed__1;
lean_object* l_Lean_mkMData(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_7__mkAppRevRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_lt(lean_object*, lean_object*);
uint64_t l___private_Init_Lean_Expr_2__mkExprCachedDataCore(size_t, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* l_Lean_Expr_getRevArg_x21___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21___closed__1;
uint64_t l_Lean_mkExprCachedDataForBinder(size_t, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t);
lean_object* l___private_Init_Lean_Expr_9__etaExpandedBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ExprCachedData_hasLevelMVar___boxed(lean_object*);
lean_object* l_Lean_Expr_bvarIdx_x21___boxed(lean_object*);
lean_object* l___private_Init_Lean_Expr_6__withAppRevAux(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_mkCAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21___boxed(lean_object*);
lean_object* l_Lean_mkDecIsTrue(lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_abstract___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_5__getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21___closed__2;
lean_object* l_Lean_Expr_updateSort_x21(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_4__getAppArgsAux(lean_object*, lean_object*, lean_object*);
size_t l_Lean_ExprStructEq_hash(lean_object*);
size_t l_Lean_ExprCachedData_hash(uint64_t);
lean_object* l_Lean_Expr_getRevArgD___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_9__etaExpandedBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateProj_x21(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21___closed__1;
lean_object* l_Lean_Expr_updateLambdaE_x21___closed__1;
lean_object* l_Lean_Expr_inhabited___closed__1;
lean_object* l___private_Init_Lean_Expr_3__mkAppRangeAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateApp_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppRange(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
lean_object* l_Lean_Expr_abstractRange___boxed(lean_object*, lean_object*, lean_object*);
uint32_t l_USize_toUInt32(size_t);
lean_object* l_Lean_Expr_fvar___boxed(lean_object*);
lean_object* l_Lean_ExprStructEq_HasToString___boxed(lean_object*);
lean_object* lean_expr_mk_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateFn___main(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Literal_type___closed__4;
lean_object* l_Lean_Expr_mdata___boxed(lean_object*, lean_object*);
uint8_t l_Lean_ExprCachedData_hasFVar(uint64_t);
lean_object* l_Lean_Expr_HasBeq;
lean_object* l_Lean_Expr_getRevArgD___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
lean_object* l___private_Init_Lean_Expr_6__withAppRevAux___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppRev___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
lean_object* l_Lean_Expr_updateSort_x21___closed__1;
lean_object* l_Lean_Expr_isBinding___boxed(lean_object*);
uint8_t lean_expr_has_expr_mvar(lean_object*);
lean_object* l_Lean_Expr_Hashable;
lean_object* l_Lean_Expr_updateMData_x21___closed__1;
lean_object* l_Lean_ExprCachedData_hasExprMVar___boxed(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object*);
lean_object* l_Lean_Expr_mvar___boxed(lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Expr_updateForall_x21___closed__2;
lean_object* l_Lean_Expr_getArgD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isSort___boxed(lean_object*);
lean_object* l_Lean_Expr_instantiateRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
lean_object* l_Lean_mkExprCachedDataForBinder___boxed__const__1;
uint8_t l_Lean_Expr_isProj(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object*);
lean_object* l_Lean_Expr_getArg_x21(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_4__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isLet___boxed(lean_object*);
lean_object* l_Lean_Expr_updateProj_x21___closed__2;
lean_object* l_Lean_Expr_getAppFn___boxed(lean_object*);
lean_object* l_Lean_ExprCachedData_binderInfo___boxed(lean_object*);
lean_object* l_Lean_Expr_updateForallE_x21___closed__1;
lean_object* l_Lean_mkLit(lean_object*);
lean_object* l_Lean_Expr_mkAppRevRange(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isForall___boxed(lean_object*);
lean_object* l_Lean_Literal_type___closed__1;
uint64_t l_UInt64_land(uint64_t, uint64_t);
lean_object* l_Lean_Expr_mkAppRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21___closed__1;
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_isMVar___boxed(lean_object*);
lean_object* l_Lean_ExprStructEq_Inhabited;
lean_object* l_Lean_mkDecIsFalse___closed__3;
lean_object* l_Lean_mkForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_2__mkExprCachedDataCore___boxed__const__1;
lean_object* lean_expr_mk_lit(lean_object*);
lean_object* l_Lean_mkDecIsFalse___closed__2;
lean_object* l___private_Init_Lean_Expr_10__etaExpandedAux(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_Expr_isConst___boxed(lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParams___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Literal_type___closed__3;
lean_object* l_Lean_Expr_lt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ExprStructEq_Hashable___closed__1;
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_level_mvar(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l___private_Init_Lean_Expr_3__mkAppRangeAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_BinderInfo_beq(uint8_t x_1, uint8_t x_2) {
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
lean_object* l_Lean_BinderInfo_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_BinderInfo_beq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* _init_l_Lean_BinderInfo_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_BinderInfo_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_BinderInfo_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_BinderInfo_HasBeq___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_MData_empty() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* _init_l_Lean_MData_HasEmptyc() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
uint64_t _init_l_Lean_ExprCachedData_inhabited() {
_start:
{
uint64_t x_1; 
x_1 = l_UInt64_Inhabited;
return x_1;
}
}
size_t l_Lean_ExprCachedData_hash(uint64_t x_1) {
_start:
{
uint32_t x_2; size_t x_3; 
x_2 = ((uint32_t)x_1);
x_3 = x_2;
return x_3;
}
}
lean_object* l_Lean_ExprCachedData_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_ExprCachedData_hash(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
uint32_t l_Lean_ExprCachedData_looseBVarRange(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint32_t x_4; 
x_2 = 40;
x_3 = x_1 >> x_2;
x_4 = ((uint32_t)x_3);
return x_4;
}
}
lean_object* l_Lean_ExprCachedData_looseBVarRange___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_ExprCachedData_looseBVarRange(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
uint8_t l_Lean_ExprCachedData_hasFVar(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint8_t x_6; 
x_2 = 1;
x_3 = 32;
x_4 = x_1 >> x_3;
x_5 = x_4 & x_2;
x_6 = x_5 == x_2;
return x_6;
}
}
lean_object* l_Lean_ExprCachedData_hasFVar___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_ExprCachedData_hasFVar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_ExprCachedData_hasExprMVar(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint8_t x_6; 
x_2 = 1;
x_3 = 33;
x_4 = x_1 >> x_3;
x_5 = x_4 & x_2;
x_6 = x_5 == x_2;
return x_6;
}
}
lean_object* l_Lean_ExprCachedData_hasExprMVar___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_ExprCachedData_hasExprMVar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_ExprCachedData_hasLevelMVar(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint8_t x_6; 
x_2 = 1;
x_3 = 34;
x_4 = x_1 >> x_3;
x_5 = x_4 & x_2;
x_6 = x_5 == x_2;
return x_6;
}
}
lean_object* l_Lean_ExprCachedData_hasLevelMVar___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_ExprCachedData_hasLevelMVar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_ExprCachedData_hasLevelParam(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint8_t x_6; 
x_2 = 1;
x_3 = 35;
x_4 = x_1 >> x_3;
x_5 = x_4 & x_2;
x_6 = x_5 == x_2;
return x_6;
}
}
lean_object* l_Lean_ExprCachedData_hasLevelParam___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_ExprCachedData_hasLevelParam(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_ExprCachedData_nonDepLet(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint8_t x_6; 
x_2 = 1;
x_3 = 36;
x_4 = x_1 >> x_3;
x_5 = x_4 & x_2;
x_6 = x_5 == x_2;
return x_6;
}
}
lean_object* l_Lean_ExprCachedData_nonDepLet___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_ExprCachedData_nonDepLet(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_ExprCachedData_binderInfo___boxed(lean_object* x_1) {
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
lean_object* _init_l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(16777216u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Lean.Expr");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bound variable index is too big");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(108u);
x_3 = lean_unsigned_to_nat(42u);
x_4 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__3;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l___private_Init_Lean_Expr_2__mkExprCachedDataCore___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lean_ExprCachedData_inhabited;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
uint64_t l___private_Init_Lean_Expr_2__mkExprCachedDataCore(size_t x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__1;
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
x_41 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__4;
x_42 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___boxed__const__1;
x_43 = lean_panic_fn(x_41);
x_44 = lean_unbox_uint64(x_43);
lean_dec(x_43);
return x_44;
}
}
}
lean_object* l___private_Init_Lean_Expr_2__mkExprCachedDataCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_16 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore(x_9, x_2, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_2);
x_17 = lean_box_uint64(x_16);
return x_17;
}
}
uint64_t _init_l_Lean_mkExprCachedData___closed__1() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 0;
x_2 = (uint64_t)x_1;
return x_2;
}
}
uint64_t _init_l_Lean_mkExprCachedData___closed__2() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 36;
x_2 = l_Lean_mkExprCachedData___closed__1;
x_3 = x_2 << x_1;
return x_3;
}
}
uint64_t _init_l_Lean_mkExprCachedData___closed__3() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 0;
x_2 = (uint64_t)x_1;
return x_2;
}
}
uint64_t _init_l_Lean_mkExprCachedData___closed__4() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 37;
x_2 = l_Lean_mkExprCachedData___closed__3;
x_3 = x_2 << x_1;
return x_3;
}
}
lean_object* _init_l_Lean_mkExprCachedData___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lean_ExprCachedData_inhabited;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
uint64_t l_Lean_mkExprCachedData(size_t x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__1;
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
x_27 = l_Lean_mkExprCachedData___closed__2;
x_28 = x_26 + x_27;
x_29 = l_Lean_mkExprCachedData___closed__4;
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
x_35 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__4;
x_36 = l_Lean_mkExprCachedData___boxed__const__1;
x_37 = lean_panic_fn(x_35);
x_38 = lean_unbox_uint64(x_37);
lean_dec(x_37);
return x_38;
}
}
}
lean_object* l_Lean_mkExprCachedData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_12 = l_Lean_mkExprCachedData(x_7, x_2, x_8, x_9, x_10, x_11);
lean_dec(x_2);
x_13 = lean_box_uint64(x_12);
return x_13;
}
}
lean_object* _init_l_Lean_mkExprCachedDataForBinder___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lean_ExprCachedData_inhabited;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
uint64_t l_Lean_mkExprCachedDataForBinder(size_t x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__1;
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
x_28 = l_Lean_mkExprCachedData___closed__2;
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
x_38 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__4;
x_39 = l_Lean_mkExprCachedDataForBinder___boxed__const__1;
x_40 = lean_panic_fn(x_38);
x_41 = lean_unbox_uint64(x_40);
lean_dec(x_40);
return x_41;
}
}
}
lean_object* l_Lean_mkExprCachedDataForBinder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_14 = l_Lean_mkExprCachedDataForBinder(x_8, x_2, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
x_15 = lean_box_uint64(x_14);
return x_15;
}
}
lean_object* _init_l_Lean_mkExprCachedDataForLet___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lean_ExprCachedData_inhabited;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
uint64_t l_Lean_mkExprCachedDataForLet(size_t x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__1;
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
x_32 = l_Lean_mkExprCachedData___closed__4;
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
x_38 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__4;
x_39 = l_Lean_mkExprCachedDataForLet___boxed__const__1;
x_40 = lean_panic_fn(x_38);
x_41 = lean_unbox_uint64(x_40);
lean_dec(x_40);
return x_41;
}
}
}
lean_object* l_Lean_mkExprCachedDataForLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_14 = l_Lean_mkExprCachedDataForLet(x_8, x_2, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
x_15 = lean_box_uint64(x_14);
return x_15;
}
}
lean_object* _init_l_Lean_Expr_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Expr_bvar___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_mk_bvar(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_fvar___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_mk_fvar(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_mvar___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_mk_mvar(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_sort___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_mk_sort(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_const___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_mk_const(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_app___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_mk_app(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_lam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_expr_mk_lambda(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Expr_forallE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_expr_mk_forall(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Expr_letE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_expr_mk_let(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_lit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_mk_lit(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_mdata___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_mk_mdata(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_proj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_mk_proj(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_mkLit(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_mk_lit(x_1);
return x_2;
}
}
lean_object* l_Lean_mkNatLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_expr_mk_lit(x_2);
return x_3;
}
}
lean_object* l_Lean_mkStrLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_expr_mk_lit(x_2);
return x_3;
}
}
lean_object* l_Lean_mkConst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_mk_const(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Literal_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Literal_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Literal_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Literal_type___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Nat");
return x_1;
}
}
lean_object* _init_l_Lean_Literal_type___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Literal_type___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Literal_type___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Literal_type___closed__2;
x_3 = lean_expr_mk_const(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Literal_type___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("String");
return x_1;
}
}
lean_object* _init_l_Lean_Literal_type___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Literal_type___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Literal_type___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Literal_type___closed__5;
x_3 = lean_expr_mk_const(x_2, x_1);
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
x_3 = l_Lean_Literal_type___closed__6;
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
lean_object* l_Lean_mkBVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_mk_bvar(x_1);
return x_2;
}
}
lean_object* l_Lean_mkSort(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_mk_sort(x_1);
return x_2;
}
}
lean_object* l_Lean_mkFVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_mk_fvar(x_1);
return x_2;
}
}
lean_object* l_Lean_mkMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_mk_mvar(x_1);
return x_2;
}
}
lean_object* l_Lean_mkMData(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_mk_mdata(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkProj(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_mk_proj(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_mkApp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_mk_app(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = lean_expr_mk_app(x_4, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Lean_mkAppN(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_2, x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
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
lean_object* l_Lean_mkLambda(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_expr_mk_lambda(x_1, x_2, x_3, x_4);
return x_5;
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
lean_object* x_5; 
x_5 = lean_expr_mk_forall(x_1, x_2, x_3, x_4);
return x_5;
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
lean_object* l_Lean_mkLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_expr_mk_let(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Expr_3__mkAppRangeAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_Lean_Expr_inhabited;
x_9 = lean_array_get(x_8, x_2, x_3);
lean_dec(x_3);
x_10 = lean_expr_mk_app(x_4, x_9);
x_3 = x_7;
x_4 = x_10;
goto _start;
}
}
}
lean_object* l___private_Init_Lean_Expr_3__mkAppRangeAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Expr_3__mkAppRangeAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Expr_3__mkAppRangeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Expr_3__mkAppRangeAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Expr_3__mkAppRangeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Expr_3__mkAppRangeAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_mkAppRange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Expr_3__mkAppRangeAux___main(x_3, x_4, x_2, x_1);
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
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_mkAppRev___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = lean_expr_mk_app(x_5, x_10);
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
lean_object* l_Lean_mkAppRev(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_mkAppRev___spec__1(x_2, x_2, x_3, lean_box(0), x_1);
return x_4;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_mkAppRev___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_mkAppRev___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
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
lean_object* l_Lean_Expr_hash___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_expr_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_Hashable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_hash___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Expr_Hashable() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_Hashable___closed__1;
return x_1;
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
lean_object* _init_l_Lean_Expr_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_eqv___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Expr_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_HasBeq___closed__1;
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
lean_object* l_Lean_Expr_hasExprMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_expr_mvar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_hasLevelMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_level_mvar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_hasMVar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_expr_has_expr_mvar(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = lean_expr_has_level_mvar(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 1;
return x_4;
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
lean_object* l_Lean_Expr_hasFVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_fvar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
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
uint8_t l_Lean_Expr_isConstOf(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_name_dec_eq(x_3, x_2);
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
lean_object* l_Lean_Expr_getAppFn___main(lean_object* x_1) {
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
lean_object* l_Lean_Expr_getAppFn___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAppFn___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_getAppFn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAppFn___main(x_1);
return x_2;
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
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Expr_getAppNumArgsAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_2);
return x_3;
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
x_3 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_2);
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
lean_object* l___private_Init_Lean_Expr_4__getAppArgsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Init_Lean_Expr_4__getAppArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Expr_4__getAppArgsAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_getAppArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_2);
x_4 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_3);
x_5 = lean_mk_array(x_3, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = l___private_Init_Lean_Expr_4__getAppArgsAux___main(x_1, x_5, x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Expr_5__getAppRevArgsAux___main(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Init_Lean_Expr_5__getAppRevArgsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Expr_5__getAppRevArgsAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_getAppRevArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_2);
x_4 = lean_mk_empty_array_with_capacity(x_3);
lean_dec(x_3);
x_5 = l___private_Init_Lean_Expr_5__getAppRevArgsAux___main(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_withAppAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Expr_withAppAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_withAppAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
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
x_4 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_3);
x_5 = l_Lean_Expr_inhabited___closed__1;
lean_inc(x_4);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
x_9 = l_Lean_Expr_withAppAux___main___rarg(x_2, x_1, x_6, x_8);
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
lean_object* l___private_Init_Lean_Expr_6__withAppRevAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Init_Lean_Expr_6__withAppRevAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Expr_6__withAppRevAux___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Expr_6__withAppRevAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Expr_6__withAppRevAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Expr_6__withAppRevAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Expr_6__withAppRevAux___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppRev___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_3);
x_5 = lean_mk_empty_array_with_capacity(x_4);
lean_dec(x_4);
x_6 = l___private_Init_Lean_Expr_6__withAppRevAux___main___rarg(x_2, x_1, x_5);
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
lean_object* l_Lean_Expr_getRevArgD___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Expr_getRevArgD___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_getRevArgD___main(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Expr_getRevArgD(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_getRevArgD___main(x_1, x_2, x_3);
return x_4;
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
lean_object* _init_l_Lean_Expr_getRevArg_x21___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(368u);
x_3 = lean_unsigned_to_nat(18u);
x_4 = l_List_get_x21___main___rarg___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object* x_1, lean_object* x_2) {
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
x_10 = l_Lean_Expr_inhabited;
x_11 = l_Lean_Expr_getRevArg_x21___main___closed__1;
x_12 = lean_panic_fn(x_11);
return x_12;
}
}
}
lean_object* l_Lean_Expr_getRevArg_x21___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getRevArg_x21___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_getRevArg_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getRevArg_x21___main(x_1, x_2);
return x_3;
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
x_7 = l_Lean_Expr_getRevArg_x21___main(x_1, x_6);
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
x_8 = l_Lean_Expr_getRevArgD___main(x_1, x_7, x_3);
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
uint8_t l_Lean_Expr_isAppOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_name_dec_eq(x_4, x_2);
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
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_name_dec_eq(x_4, x_2);
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
lean_object* l_Lean_Expr_isAppOfArity___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_isAppOfArity___main(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Lean_Expr_isAppOfArity(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_isAppOfArity___main(x_1, x_2, x_3);
return x_4;
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
lean_object* _init_l_Lean_Expr_appFn_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("application expected");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_appFn_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(388u);
x_3 = lean_unsigned_to_nat(13u);
x_4 = l_Lean_Expr_appFn_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
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
x_3 = l_Lean_Expr_inhabited;
x_4 = l_Lean_Expr_appFn_x21___closed__2;
x_5 = lean_panic_fn(x_4);
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
lean_object* _init_l_Lean_Expr_appArg_x21___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(392u);
x_3 = lean_unsigned_to_nat(13u);
x_4 = l_Lean_Expr_appFn_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
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
x_3 = l_Lean_Expr_inhabited;
x_4 = l_Lean_Expr_appArg_x21___closed__1;
x_5 = lean_panic_fn(x_4);
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
lean_object* _init_l_Lean_Expr_constName_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constant expected");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_constName_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(396u);
x_3 = lean_unsigned_to_nat(15u);
x_4 = l_Lean_Expr_constName_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
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
x_3 = l_Lean_Inhabited;
x_4 = l_Lean_Expr_constName_x21___closed__2;
x_5 = lean_panic_fn(x_4);
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
lean_object* _init_l_Lean_Expr_constLevels_x21___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(400u);
x_3 = lean_unsigned_to_nat(16u);
x_4 = l_Lean_Expr_constName_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
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
x_4 = l_Lean_Expr_constLevels_x21___closed__1;
x_5 = lean_panic_fn(x_4);
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
lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bvar expected");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_bvarIdx_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(404u);
x_3 = lean_unsigned_to_nat(14u);
x_4 = l_Lean_Expr_bvarIdx_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
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
x_3 = l_Nat_Inhabited;
x_4 = l_Lean_Expr_bvarIdx_x21___closed__2;
x_5 = lean_panic_fn(x_4);
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
lean_object* _init_l_Lean_Expr_fvarId_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fvar expected");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_fvarId_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(408u);
x_3 = lean_unsigned_to_nat(12u);
x_4 = l_Lean_Expr_fvarId_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
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
x_3 = l_Lean_Inhabited;
x_4 = l_Lean_Expr_fvarId_x21___closed__2;
x_5 = lean_panic_fn(x_4);
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
lean_object* _init_l_Lean_Expr_mvarId_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mvar expected");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_mvarId_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(412u);
x_3 = lean_unsigned_to_nat(12u);
x_4 = l_Lean_Expr_mvarId_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
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
x_3 = l_Lean_Inhabited;
x_4 = l_Lean_Expr_mvarId_x21___closed__2;
x_5 = lean_panic_fn(x_4);
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
lean_object* _init_l_Lean_Expr_bindingName_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("binding expected");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_bindingName_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(417u);
x_3 = lean_unsigned_to_nat(21u);
x_4 = l_Lean_Expr_bindingName_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
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
x_4 = l_Lean_Inhabited;
x_5 = l_Lean_Expr_bindingName_x21___closed__2;
x_6 = lean_panic_fn(x_5);
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
lean_object* _init_l_Lean_Expr_bindingDomain_x21___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(422u);
x_3 = lean_unsigned_to_nat(21u);
x_4 = l_Lean_Expr_bindingName_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
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
x_4 = l_Lean_Expr_inhabited;
x_5 = l_Lean_Expr_bindingDomain_x21___closed__1;
x_6 = lean_panic_fn(x_5);
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
lean_object* _init_l_Lean_Expr_bindingBody_x21___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(427u);
x_3 = lean_unsigned_to_nat(21u);
x_4 = l_Lean_Expr_bindingName_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
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
x_4 = l_Lean_Expr_inhabited;
x_5 = l_Lean_Expr_bindingBody_x21___closed__1;
x_6 = lean_panic_fn(x_5);
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
lean_object* _init_l_Lean_Expr_letName_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("let expression expected");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_letName_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(431u);
x_3 = lean_unsigned_to_nat(18u);
x_4 = l_Lean_Expr_letName_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
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
x_3 = l_Lean_Inhabited;
x_4 = l_Lean_Expr_letName_x21___closed__2;
x_5 = lean_panic_fn(x_4);
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
lean_object* l_Lean_Expr_getLooseBVarRange___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_get_loose_bvar_range(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_Expr_hasLooseBVars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_expr_get_loose_bvar_range(x_1);
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
lean_object* l_Lean_Expr_instantiateLevelParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_instantiate_lparams(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Expr_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_dbgToString___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Expr_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_HasToString___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Expr_HasRepr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_HasToString___closed__1;
return x_1;
}
}
lean_object* l_Lean_mkCAppN(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_expr_mk_const(x_1, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_2, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_mkCAppN___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkCAppN(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_mkAppB(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_expr_mk_app(x_1, x_2);
x_5 = lean_expr_mk_app(x_4, x_3);
return x_5;
}
}
lean_object* l_Lean_mkCAppB(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_expr_mk_const(x_1, x_4);
x_6 = l_Lean_mkAppB(x_5, x_2, x_3);
return x_6;
}
}
lean_object* _init_l_Lean_mkDecIsTrue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Decidable");
return x_1;
}
}
lean_object* _init_l_Lean_mkDecIsTrue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkDecIsTrue___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_mkDecIsTrue___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isTrue");
return x_1;
}
}
lean_object* _init_l_Lean_mkDecIsTrue___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkDecIsTrue___closed__2;
x_2 = l_Lean_mkDecIsTrue___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_mkDecIsTrue___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkDecIsTrue___closed__4;
x_3 = lean_expr_mk_const(x_2, x_1);
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
lean_object* _init_l_Lean_mkDecIsFalse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isFalse");
return x_1;
}
}
lean_object* _init_l_Lean_mkDecIsFalse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkDecIsTrue___closed__2;
x_2 = l_Lean_mkDecIsFalse___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_mkDecIsFalse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkDecIsFalse___closed__2;
x_3 = lean_expr_mk_const(x_2, x_1);
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
lean_object* l_Lean_exprToExprStructEq(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_exprToExprStructEq___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_exprToExprStructEq(x_1);
lean_dec(x_1);
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
size_t l_Lean_ExprStructEq_hash(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = lean_expr_hash(x_1);
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
lean_object* _init_l_Lean_ExprStructEq_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_ExprStructEq_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ExprStructEq_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_ExprStructEq_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ExprStructEq_HasBeq___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_ExprStructEq_Hashable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ExprStructEq_hash___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_ExprStructEq_Hashable() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ExprStructEq_Hashable___closed__1;
return x_1;
}
}
lean_object* l_Lean_ExprStructEq_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_dbg_to_string(x_1);
return x_2;
}
}
lean_object* l_Lean_ExprStructEq_HasToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ExprStructEq_HasToString(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_ExprStructEq_HasRepr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_dbg_to_string(x_1);
return x_2;
}
}
lean_object* l_Lean_ExprStructEq_HasRepr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ExprStructEq_HasRepr(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Expr_7__mkAppRevRangeAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_Lean_Expr_inhabited;
x_9 = lean_array_get(x_8, x_1, x_7);
x_10 = lean_expr_mk_app(x_3, x_9);
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
lean_object* l___private_Init_Lean_Expr_7__mkAppRevRangeAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Expr_7__mkAppRevRangeAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Expr_7__mkAppRevRangeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Expr_7__mkAppRevRangeAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Expr_7__mkAppRevRangeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Expr_7__mkAppRevRangeAux(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Expr_mkAppRevRange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Expr_7__mkAppRevRangeAux___main(x_4, x_2, x_1, x_3);
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
lean_object* l___private_Init_Lean_Expr_8__betaRevAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
if (lean_obj_tag(x_3) == 6)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_14 = lean_nat_dec_lt(x_13, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_nat_sub(x_2, x_13);
lean_dec(x_13);
lean_inc(x_1);
x_16 = lean_expr_instantiate_range(x_11, x_15, x_2, x_1);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Init_Lean_Expr_7__mkAppRevRangeAux___main(x_1, x_17, x_16, x_15);
lean_dec(x_1);
return x_18;
}
else
{
x_3 = x_11;
x_4 = x_13;
goto _start;
}
}
else
{
lean_object* x_20; 
x_20 = lean_box(0);
x_5 = x_20;
goto block_10;
}
block_10:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_6 = lean_nat_sub(x_2, x_4);
lean_dec(x_4);
lean_inc(x_1);
x_7 = lean_expr_instantiate_range(x_3, x_6, x_2, x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Init_Lean_Expr_7__mkAppRevRangeAux___main(x_1, x_8, x_7, x_6);
lean_dec(x_1);
return x_9;
}
}
}
lean_object* l___private_Init_Lean_Expr_8__betaRevAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Expr_8__betaRevAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Init_Lean_Expr_8__betaRevAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Expr_8__betaRevAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Expr_8__betaRevAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Expr_8__betaRevAux(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_6 = l___private_Init_Lean_Expr_8__betaRevAux___main(x_2, x_3, x_1, x_4);
lean_dec(x_3);
return x_6;
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
lean_object* l_Lean_Expr_betaRev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_betaRev(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Expr_9__etaExpandedBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_2, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_2, x_14);
lean_dec(x_2);
x_16 = lean_nat_dec_eq(x_11, x_3);
lean_dec(x_11);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_3);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_nat_add(x_3, x_14);
lean_dec(x_3);
x_1 = x_10;
x_2 = x_15;
x_3 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_box(0);
x_4 = x_20;
goto block_8;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_2, x_21);
lean_dec(x_2);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_box(0);
x_4 = x_24;
goto block_8;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_3);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_2, x_25);
lean_dec(x_2);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_1);
x_27 = lean_box(0);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = lean_box(0);
x_4 = x_28;
goto block_8;
}
}
block_8:
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
}
}
}
lean_object* l___private_Init_Lean_Expr_9__etaExpandedBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Expr_9__etaExpandedBody___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Expr_10__etaExpandedAux___main(lean_object* x_1, lean_object* x_2) {
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
x_8 = l___private_Init_Lean_Expr_9__etaExpandedBody___main(x_1, x_2, x_7);
return x_8;
}
}
}
lean_object* l___private_Init_Lean_Expr_10__etaExpandedAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Expr_10__etaExpandedAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_etaExpanded_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Init_Lean_Expr_10__etaExpandedAux___main(x_1, x_2);
return x_3;
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
lean_object* _init_l_Lean_Expr_updateApp_x21___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(600u);
x_3 = lean_unsigned_to_nat(16u);
x_4 = l_Lean_Expr_appFn_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_updateApp_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; 
x_4 = lean_expr_update_app(x_1, x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = l_Lean_Expr_inhabited;
x_6 = l_Lean_Expr_updateApp_x21___closed__1;
x_7 = lean_panic_fn(x_6);
return x_7;
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
lean_object* _init_l_Lean_Expr_updateConst_x21___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(609u);
x_3 = lean_unsigned_to_nat(16u);
x_4 = l_Lean_Expr_constName_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_updateConst_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_3; 
x_3 = lean_expr_update_const(x_1, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = l_Lean_Expr_inhabited;
x_5 = l_Lean_Expr_updateConst_x21___closed__1;
x_6 = lean_panic_fn(x_5);
return x_6;
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
lean_object* _init_l_Lean_Expr_updateSort_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("level expected");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_updateSort_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(618u);
x_3 = lean_unsigned_to_nat(12u);
x_4 = l_Lean_Expr_updateSort_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_updateSort_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_3; 
x_3 = lean_expr_update_sort(x_1, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = l_Lean_Expr_inhabited;
x_5 = l_Lean_Expr_updateSort_x21___closed__2;
x_6 = lean_panic_fn(x_5);
return x_6;
}
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
lean_object* l_Lean_Expr_updateMData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_update_mdata(x_1, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Expr_updateMData_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mdata expected");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_updateMData_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(635u);
x_3 = lean_unsigned_to_nat(15u);
x_4 = l_Lean_Expr_updateMData_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_updateMData_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_3; 
x_3 = lean_expr_update_mdata(x_1, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = l_Lean_Expr_inhabited;
x_5 = l_Lean_Expr_updateMData_x21___closed__2;
x_6 = lean_panic_fn(x_5);
return x_6;
}
}
}
lean_object* _init_l_Lean_Expr_updateProj_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("proj expected");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_updateProj_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(640u);
x_3 = lean_unsigned_to_nat(16u);
x_4 = l_Lean_Expr_updateProj_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_updateProj_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_3; 
x_3 = lean_expr_update_proj(x_1, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = l_Lean_Expr_inhabited;
x_5 = l_Lean_Expr_updateProj_x21___closed__2;
x_6 = lean_panic_fn(x_5);
return x_6;
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
lean_object* _init_l_Lean_Expr_updateForall_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("forall expected");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_updateForall_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(649u);
x_3 = lean_unsigned_to_nat(22u);
x_4 = l_Lean_Expr_updateForall_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_updateForall_x21(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_5; 
x_5 = lean_expr_update_forall(x_1, x_2, x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_6 = l_Lean_Expr_inhabited;
x_7 = l_Lean_Expr_updateForall_x21___closed__2;
x_8 = lean_panic_fn(x_7);
return x_8;
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
lean_object* _init_l_Lean_Expr_updateForallE_x21___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(654u);
x_3 = lean_unsigned_to_nat(22u);
x_4 = l_Lean_Expr_updateForall_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_updateForallE_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_5 = lean_expr_update_forall(x_1, x_4, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_Expr_inhabited;
x_7 = l_Lean_Expr_updateForallE_x21___closed__1;
x_8 = lean_panic_fn(x_7);
return x_8;
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
lean_object* _init_l_Lean_Expr_updateLambda_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lambda expected");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_updateLambda_x21___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(663u);
x_3 = lean_unsigned_to_nat(18u);
x_4 = l_Lean_Expr_updateLambda_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_updateLambda_x21(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_5; 
x_5 = lean_expr_update_lambda(x_1, x_2, x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_6 = l_Lean_Expr_inhabited;
x_7 = l_Lean_Expr_updateLambda_x21___closed__2;
x_8 = lean_panic_fn(x_7);
return x_8;
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
lean_object* _init_l_Lean_Expr_updateLambdaE_x21___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(668u);
x_3 = lean_unsigned_to_nat(18u);
x_4 = l_Lean_Expr_updateLambda_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_updateLambdaE_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_5 = lean_expr_update_lambda(x_1, x_4, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_Expr_inhabited;
x_7 = l_Lean_Expr_updateLambdaE_x21___closed__1;
x_8 = lean_panic_fn(x_7);
return x_8;
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
lean_object* _init_l_Lean_Expr_updateLet_x21___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2;
x_2 = lean_unsigned_to_nat(677u);
x_3 = lean_unsigned_to_nat(18u);
x_4 = l_Lean_Expr_letName_x21___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_updateLet_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_5; 
x_5 = lean_expr_update_let(x_1, x_2, x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_Expr_inhabited;
x_7 = l_Lean_Expr_updateLet_x21___closed__1;
x_8 = lean_panic_fn(x_7);
return x_8;
}
}
}
lean_object* l_Lean_Expr_updateFn___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Expr_updateFn___main(x_3, x_2);
x_6 = lean_expr_mk_app(x_5, x_4);
return x_6;
}
else
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
lean_object* l_Lean_Expr_updateFn___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_updateFn___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_updateFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_updateFn___main(x_1, x_2);
return x_3;
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
lean_object* initialize_Init_Lean_Level(lean_object*);
lean_object* initialize_Init_Lean_KVMap(lean_object*);
lean_object* initialize_Init_Data_HashMap_Default(lean_object*);
lean_object* initialize_Init_Data_HashSet(lean_object*);
lean_object* initialize_Init_Data_PersistentHashMap_Default(lean_object*);
lean_object* initialize_Init_Data_PersistentHashSet(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Expr(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Level(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_KVMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_HashMap_Default(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_HashSet(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_PersistentHashMap_Default(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_PersistentHashSet(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_BinderInfo_HasBeq___closed__1 = _init_l_Lean_BinderInfo_HasBeq___closed__1();
lean_mark_persistent(l_Lean_BinderInfo_HasBeq___closed__1);
l_Lean_BinderInfo_HasBeq = _init_l_Lean_BinderInfo_HasBeq();
lean_mark_persistent(l_Lean_BinderInfo_HasBeq);
l_Lean_MData_empty = _init_l_Lean_MData_empty();
lean_mark_persistent(l_Lean_MData_empty);
l_Lean_MData_HasEmptyc = _init_l_Lean_MData_HasEmptyc();
lean_mark_persistent(l_Lean_MData_HasEmptyc);
l_Lean_ExprCachedData_inhabited = _init_l_Lean_ExprCachedData_inhabited();
l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__1 = _init_l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__1();
lean_mark_persistent(l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__1);
l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2 = _init_l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2();
lean_mark_persistent(l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__2);
l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__3 = _init_l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__3();
lean_mark_persistent(l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__3);
l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__4 = _init_l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__4();
lean_mark_persistent(l___private_Init_Lean_Expr_2__mkExprCachedDataCore___closed__4);
l___private_Init_Lean_Expr_2__mkExprCachedDataCore___boxed__const__1 = _init_l___private_Init_Lean_Expr_2__mkExprCachedDataCore___boxed__const__1();
lean_mark_persistent(l___private_Init_Lean_Expr_2__mkExprCachedDataCore___boxed__const__1);
l_Lean_mkExprCachedData___closed__1 = _init_l_Lean_mkExprCachedData___closed__1();
l_Lean_mkExprCachedData___closed__2 = _init_l_Lean_mkExprCachedData___closed__2();
l_Lean_mkExprCachedData___closed__3 = _init_l_Lean_mkExprCachedData___closed__3();
l_Lean_mkExprCachedData___closed__4 = _init_l_Lean_mkExprCachedData___closed__4();
l_Lean_mkExprCachedData___boxed__const__1 = _init_l_Lean_mkExprCachedData___boxed__const__1();
lean_mark_persistent(l_Lean_mkExprCachedData___boxed__const__1);
l_Lean_mkExprCachedDataForBinder___boxed__const__1 = _init_l_Lean_mkExprCachedDataForBinder___boxed__const__1();
lean_mark_persistent(l_Lean_mkExprCachedDataForBinder___boxed__const__1);
l_Lean_mkExprCachedDataForLet___boxed__const__1 = _init_l_Lean_mkExprCachedDataForLet___boxed__const__1();
lean_mark_persistent(l_Lean_mkExprCachedDataForLet___boxed__const__1);
l_Lean_Expr_inhabited___closed__1 = _init_l_Lean_Expr_inhabited___closed__1();
lean_mark_persistent(l_Lean_Expr_inhabited___closed__1);
l_Lean_Expr_inhabited = _init_l_Lean_Expr_inhabited();
lean_mark_persistent(l_Lean_Expr_inhabited);
l_Lean_Literal_Inhabited___closed__1 = _init_l_Lean_Literal_Inhabited___closed__1();
lean_mark_persistent(l_Lean_Literal_Inhabited___closed__1);
l_Lean_Literal_Inhabited = _init_l_Lean_Literal_Inhabited();
lean_mark_persistent(l_Lean_Literal_Inhabited);
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
l_Lean_Expr_Hashable___closed__1 = _init_l_Lean_Expr_Hashable___closed__1();
lean_mark_persistent(l_Lean_Expr_Hashable___closed__1);
l_Lean_Expr_Hashable = _init_l_Lean_Expr_Hashable();
lean_mark_persistent(l_Lean_Expr_Hashable);
l_Lean_Expr_HasBeq___closed__1 = _init_l_Lean_Expr_HasBeq___closed__1();
lean_mark_persistent(l_Lean_Expr_HasBeq___closed__1);
l_Lean_Expr_HasBeq = _init_l_Lean_Expr_HasBeq();
lean_mark_persistent(l_Lean_Expr_HasBeq);
l_Lean_Expr_getRevArg_x21___main___closed__1 = _init_l_Lean_Expr_getRevArg_x21___main___closed__1();
lean_mark_persistent(l_Lean_Expr_getRevArg_x21___main___closed__1);
l_Lean_Expr_appFn_x21___closed__1 = _init_l_Lean_Expr_appFn_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_appFn_x21___closed__1);
l_Lean_Expr_appFn_x21___closed__2 = _init_l_Lean_Expr_appFn_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_appFn_x21___closed__2);
l_Lean_Expr_appArg_x21___closed__1 = _init_l_Lean_Expr_appArg_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_appArg_x21___closed__1);
l_Lean_Expr_constName_x21___closed__1 = _init_l_Lean_Expr_constName_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_constName_x21___closed__1);
l_Lean_Expr_constName_x21___closed__2 = _init_l_Lean_Expr_constName_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_constName_x21___closed__2);
l_Lean_Expr_constLevels_x21___closed__1 = _init_l_Lean_Expr_constLevels_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_constLevels_x21___closed__1);
l_Lean_Expr_bvarIdx_x21___closed__1 = _init_l_Lean_Expr_bvarIdx_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_bvarIdx_x21___closed__1);
l_Lean_Expr_bvarIdx_x21___closed__2 = _init_l_Lean_Expr_bvarIdx_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_bvarIdx_x21___closed__2);
l_Lean_Expr_fvarId_x21___closed__1 = _init_l_Lean_Expr_fvarId_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_fvarId_x21___closed__1);
l_Lean_Expr_fvarId_x21___closed__2 = _init_l_Lean_Expr_fvarId_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_fvarId_x21___closed__2);
l_Lean_Expr_mvarId_x21___closed__1 = _init_l_Lean_Expr_mvarId_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_mvarId_x21___closed__1);
l_Lean_Expr_mvarId_x21___closed__2 = _init_l_Lean_Expr_mvarId_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_mvarId_x21___closed__2);
l_Lean_Expr_bindingName_x21___closed__1 = _init_l_Lean_Expr_bindingName_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_bindingName_x21___closed__1);
l_Lean_Expr_bindingName_x21___closed__2 = _init_l_Lean_Expr_bindingName_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_bindingName_x21___closed__2);
l_Lean_Expr_bindingDomain_x21___closed__1 = _init_l_Lean_Expr_bindingDomain_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_bindingDomain_x21___closed__1);
l_Lean_Expr_bindingBody_x21___closed__1 = _init_l_Lean_Expr_bindingBody_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_bindingBody_x21___closed__1);
l_Lean_Expr_letName_x21___closed__1 = _init_l_Lean_Expr_letName_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_letName_x21___closed__1);
l_Lean_Expr_letName_x21___closed__2 = _init_l_Lean_Expr_letName_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_letName_x21___closed__2);
l_Lean_Expr_HasToString___closed__1 = _init_l_Lean_Expr_HasToString___closed__1();
lean_mark_persistent(l_Lean_Expr_HasToString___closed__1);
l_Lean_Expr_HasToString = _init_l_Lean_Expr_HasToString();
lean_mark_persistent(l_Lean_Expr_HasToString);
l_Lean_Expr_HasRepr = _init_l_Lean_Expr_HasRepr();
lean_mark_persistent(l_Lean_Expr_HasRepr);
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
l_Lean_ExprStructEq_Inhabited = _init_l_Lean_ExprStructEq_Inhabited();
lean_mark_persistent(l_Lean_ExprStructEq_Inhabited);
l_Lean_ExprStructEq_HasBeq___closed__1 = _init_l_Lean_ExprStructEq_HasBeq___closed__1();
lean_mark_persistent(l_Lean_ExprStructEq_HasBeq___closed__1);
l_Lean_ExprStructEq_HasBeq = _init_l_Lean_ExprStructEq_HasBeq();
lean_mark_persistent(l_Lean_ExprStructEq_HasBeq);
l_Lean_ExprStructEq_Hashable___closed__1 = _init_l_Lean_ExprStructEq_Hashable___closed__1();
lean_mark_persistent(l_Lean_ExprStructEq_Hashable___closed__1);
l_Lean_ExprStructEq_Hashable = _init_l_Lean_ExprStructEq_Hashable();
lean_mark_persistent(l_Lean_ExprStructEq_Hashable);
l_Lean_Expr_updateApp_x21___closed__1 = _init_l_Lean_Expr_updateApp_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateApp_x21___closed__1);
l_Lean_Expr_updateConst_x21___closed__1 = _init_l_Lean_Expr_updateConst_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateConst_x21___closed__1);
l_Lean_Expr_updateSort_x21___closed__1 = _init_l_Lean_Expr_updateSort_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateSort_x21___closed__1);
l_Lean_Expr_updateSort_x21___closed__2 = _init_l_Lean_Expr_updateSort_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_updateSort_x21___closed__2);
l_Lean_Expr_updateMData_x21___closed__1 = _init_l_Lean_Expr_updateMData_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateMData_x21___closed__1);
l_Lean_Expr_updateMData_x21___closed__2 = _init_l_Lean_Expr_updateMData_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_updateMData_x21___closed__2);
l_Lean_Expr_updateProj_x21___closed__1 = _init_l_Lean_Expr_updateProj_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateProj_x21___closed__1);
l_Lean_Expr_updateProj_x21___closed__2 = _init_l_Lean_Expr_updateProj_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_updateProj_x21___closed__2);
l_Lean_Expr_updateForall_x21___closed__1 = _init_l_Lean_Expr_updateForall_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateForall_x21___closed__1);
l_Lean_Expr_updateForall_x21___closed__2 = _init_l_Lean_Expr_updateForall_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_updateForall_x21___closed__2);
l_Lean_Expr_updateForallE_x21___closed__1 = _init_l_Lean_Expr_updateForallE_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateForallE_x21___closed__1);
l_Lean_Expr_updateLambda_x21___closed__1 = _init_l_Lean_Expr_updateLambda_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateLambda_x21___closed__1);
l_Lean_Expr_updateLambda_x21___closed__2 = _init_l_Lean_Expr_updateLambda_x21___closed__2();
lean_mark_persistent(l_Lean_Expr_updateLambda_x21___closed__2);
l_Lean_Expr_updateLambdaE_x21___closed__1 = _init_l_Lean_Expr_updateLambdaE_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateLambdaE_x21___closed__1);
l_Lean_Expr_updateLet_x21___closed__1 = _init_l_Lean_Expr_updateLet_x21___closed__1();
lean_mark_persistent(l_Lean_Expr_updateLet_x21___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
