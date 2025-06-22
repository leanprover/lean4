// Lean compiler output
// Module: Lean.Meta.InferType
// Imports: Lean.Data.LBool Lean.Meta.Basic
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
static lean_object* l_Lean_Meta_typeFormerTypeLevel_go___closed__0;
lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_arrowDomainsN___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1;
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2___redArg(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__4;
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Expr_instantiateBetaRevRange_visit_spec__6___redArg(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__1;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__4;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Literal_type(lean_object*);
static lean_object* l_Lean_Meta_throwTypeExcepted___redArg___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__2;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_arrowDomainsN_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
static lean_object* l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__5;
lean_object* l_Lean_Meta_instBEqExprConfigCacheKey___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Meta_mkExprConfigCacheKey___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_arrowDomainsN___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwFunctionExpected___redArg___closed__2;
lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_arrowDomainsN_spec__3(lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0;
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object*);
static lean_object* l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__5;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Expr_instantiateBetaRevRange_visit_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Expr_instantiateBetaRevRange_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_instantiateBetaRevRange_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__6;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__6;
static lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1;
static lean_object* l_Lean_Meta_inferTypeImp_infer___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___Lean_Meta_arrowDomainsN_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_instDecidableEqProjReductionKind(uint8_t, uint8_t);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwFunctionExpected___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Expr_instantiateBetaRevRange_visit_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__5;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__1;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_consume_type_annotations(lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0;
static lean_object* l_Lean_Meta_throwFunctionExpected___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateLevelMVars___at___Lean_Meta_normalizeLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_throwUnknown___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp_infer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Expr_instantiateBetaRevRange_visit_spec__5___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadStateCacheT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Expr_instantiateBetaRevRange_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__7;
static lean_object* l_Lean_Meta_arrowDomainsN___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___Lean_Expr_instantiateBetaRevRange_visit_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
static lean_object* l_Lean_Meta_arrowDomainsN___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f_spec__0___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_inferTypeImp_infer___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Meta_arrowDomainsN___lam__0___closed__2;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_throwUnknownMVar___redArg___closed__0;
lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___Lean_Expr_instantiateBetaRevRange_visit_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_arrowDomainsN___lam__0___closed__1;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwTypeExcepted___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__2;
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_instantiateBetaRevRange_visit_spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_instantiateBetaRevRange_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Expr_instantiateBetaRevRange_visit_spec__6___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isPropFormerType___closed__0;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__4;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__2;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Meta_isPropFormerType_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_instantiateBetaRevRange_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_throwUnknownMVar___redArg___closed__1;
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__6;
lean_object* l_Lean_Level_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwFunctionExpected___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Expr_instantiateBetaRevRange_visit_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__7;
lean_object* l_Lean_Meta_getConfig___redArg(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Meta_isPropFormerType_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(uint8_t, uint8_t);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__2;
lean_object* l_Lean_Meta_instHashableExprConfigCacheKey___lam__0___boxed(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Expr_instantiateBetaRevRange_visit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_6, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_11 = lean_array_uget(x_7, x_6);
lean_inc(x_4);
x_12 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_11, x_4, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_array_uset(x_7, x_6, x_15);
x_17 = 1;
x_18 = lean_usize_add(x_6, x_17);
x_19 = lean_array_uset(x_16, x_6, x_13);
x_6 = x_18;
x_7 = x_19;
x_8 = x_14;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_instantiateBetaRevRange_visit_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_expr_equal(x_10, x_12);
if (x_14 == 0)
{
x_7 = x_14;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_eq(x_11, x_13);
x_7 = x_15;
goto block_9;
}
block_9:
{
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_7;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_instantiateBetaRevRange_visit_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_instantiateBetaRevRange_visit_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_Expr_hash(x_6);
lean_dec(x_6);
x_10 = lean_uint64_of_nat(x_7);
lean_dec(x_7);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_1, x_22);
lean_ctor_set(x_2, 2, x_23);
x_24 = lean_array_uset(x_1, x_22, x_2);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; size_t x_41; size_t x_42; size_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
x_31 = lean_array_get_size(x_1);
x_32 = l_Lean_Expr_hash(x_29);
lean_dec(x_29);
x_33 = lean_uint64_of_nat(x_30);
lean_dec(x_30);
x_34 = lean_uint64_mix_hash(x_32, x_33);
x_35 = 32;
x_36 = lean_uint64_shift_right(x_34, x_35);
x_37 = lean_uint64_xor(x_34, x_36);
x_38 = 16;
x_39 = lean_uint64_shift_right(x_37, x_38);
x_40 = lean_uint64_xor(x_37, x_39);
x_41 = lean_uint64_to_usize(x_40);
x_42 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_43 = 1;
x_44 = lean_usize_sub(x_42, x_43);
x_45 = lean_usize_land(x_41, x_44);
x_46 = lean_array_uget(x_1, x_45);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_27);
lean_ctor_set(x_47, 2, x_46);
x_48 = lean_array_uset(x_1, x_45, x_47);
x_1 = x_48;
x_2 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__2_spec__2___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Expr_instantiateBetaRevRange_visit_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_expr_equal(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
x_8 = x_17;
goto block_12;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_eq(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
x_8 = x_18;
goto block_12;
}
block_12:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Expr_instantiateBetaRevRange_visit_spec__5___redArg(x_1, x_2, x_6);
if (lean_is_scalar(x_7)) {
 x_10 = lean_alloc_ctor(1, 3, 0);
} else {
 x_10 = x_7;
}
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_7)) {
 x_11 = lean_alloc_ctor(1, 3, 0);
} else {
 x_11 = x_7;
}
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_6);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Expr_instantiateBetaRevRange_visit_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Expr_instantiateBetaRevRange_visit_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Expr_instantiateBetaRevRange_visit_spec__6___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_expr_equal(x_11, x_13);
if (x_15 == 0)
{
x_7 = x_15;
goto block_10;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_eq(x_12, x_14);
x_7 = x_16;
goto block_10;
}
block_10:
{
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Expr_instantiateBetaRevRange_visit_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Expr_instantiateBetaRevRange_visit_spec__6___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__0;
x_4 = l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__1;
x_5 = l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__2;
x_6 = l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__3;
x_7 = l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__4;
x_8 = l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__5;
x_9 = l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__6;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
x_11 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 3, x_7);
lean_ctor_set(x_11, 4, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = l_Lean_MonadStateCacheT_instMonad___redArg(x_12);
x_14 = l_Lean_instInhabitedExpr;
x_15 = l_instInhabitedOfMonad___redArg(x_13, x_14);
x_16 = lean_panic_fn(x_15, x_1);
x_17 = lean_apply_1(x_16, x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___Lean_Expr_instantiateBetaRevRange_visit_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_array_push(x_6, x_9);
x_5 = x_8;
x_6 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
lean_inc(x_4);
lean_inc(x_5);
x_12 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_5, x_4, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_size(x_6);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at___Lean_Expr_instantiateBetaRevRange_visit_spec__0(x_1, x_2, x_3, x_4, x_15, x_16, x_6, x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_Expr_isBVar(x_5);
lean_dec(x_5);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = l_Lean_mkAppRev(x_13, x_19);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
x_24 = lean_unbox(x_22);
x_25 = l_Lean_Expr_betaRev(x_13, x_19, x_23, x_24);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = l_Lean_Expr_isBVar(x_5);
lean_dec(x_5);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_mkAppRev(x_13, x_26);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
x_33 = lean_unbox(x_31);
x_34 = l_Lean_Expr_betaRev(x_13, x_26, x_32, x_33);
lean_dec(x_26);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.InferType", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Expr.instantiateBetaRevRange.visit", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__2;
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_unsigned_to_nat(63u);
x_4 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__1;
x_5 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__2;
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_unsigned_to_nat(64u);
x_4 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__1;
x_5 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__2;
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_unsigned_to_nat(65u);
x_4 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__1;
x_5 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__2;
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_unsigned_to_nat(62u);
x_4 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__1;
x_5 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__2;
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_unsigned_to_nat(66u);
x_4 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__1;
x_5 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Expr_looseBVarRange(x_4);
x_8 = lean_nat_dec_le(x_7, x_5);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_54; lean_object* x_55; lean_object* x_59; lean_object* x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; size_t x_73; size_t x_74; size_t x_75; size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_5);
x_63 = lean_array_get_size(x_10);
x_64 = l_Lean_Expr_hash(x_4);
x_65 = lean_uint64_of_nat(x_5);
x_66 = lean_uint64_mix_hash(x_64, x_65);
x_67 = 32;
x_68 = lean_uint64_shift_right(x_66, x_67);
x_69 = lean_uint64_xor(x_66, x_68);
x_70 = 16;
x_71 = lean_uint64_shift_right(x_69, x_70);
x_72 = lean_uint64_xor(x_69, x_71);
x_73 = lean_uint64_to_usize(x_72);
x_74 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_75 = 1;
x_76 = lean_usize_sub(x_74, x_75);
x_77 = lean_usize_land(x_73, x_76);
x_78 = lean_array_uget(x_10, x_77);
x_79 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Expr_instantiateBetaRevRange_visit_spec__6___redArg(x_11, x_78);
lean_dec(x_78);
if (lean_obj_tag(x_79) == 0)
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_6);
x_80 = lean_ctor_get(x_4, 0);
lean_inc(x_80);
x_81 = lean_nat_sub(x_2, x_1);
x_82 = lean_nat_add(x_5, x_81);
x_83 = lean_nat_dec_lt(x_80, x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_nat_sub(x_80, x_81);
lean_dec(x_81);
lean_dec(x_80);
x_85 = l_Lean_Expr_bvar___override(x_84);
x_12 = x_85;
x_13 = x_9;
x_14 = x_10;
goto block_53;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_81);
x_86 = l_Lean_instInhabitedExpr;
x_87 = lean_nat_sub(x_80, x_5);
lean_dec(x_80);
x_88 = lean_nat_sub(x_2, x_87);
lean_dec(x_87);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_sub(x_88, x_89);
lean_dec(x_88);
x_91 = lean_array_get(x_86, x_3, x_90);
lean_dec(x_90);
x_92 = lean_unsigned_to_nat(0u);
x_93 = lean_expr_lift_loose_bvars(x_91, x_92, x_5);
lean_dec(x_91);
x_12 = x_93;
x_13 = x_9;
x_14 = x_10;
goto block_53;
}
}
case 1:
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_10);
lean_dec(x_9);
x_94 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__3;
x_95 = l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7(x_94, x_6);
x_59 = x_95;
goto block_62;
}
case 2:
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_10);
lean_dec(x_9);
x_96 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__4;
x_97 = l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7(x_96, x_6);
x_59 = x_97;
goto block_62;
}
case 3:
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_10);
lean_dec(x_9);
x_98 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__5;
x_99 = l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7(x_98, x_6);
x_59 = x_99;
goto block_62;
}
case 4:
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_10);
lean_dec(x_9);
x_100 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
x_101 = l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7(x_100, x_6);
x_59 = x_101;
goto block_62;
}
case 5:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_10);
lean_dec(x_9);
x_102 = l_Lean_Expr_getAppNumArgs(x_4);
x_103 = lean_mk_empty_array_with_capacity(x_102);
lean_dec(x_102);
lean_inc(x_4);
lean_inc(x_5);
x_104 = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___Lean_Expr_instantiateBetaRevRange_visit_spec__8(x_1, x_2, x_3, x_5, x_4, x_103, x_6);
x_59 = x_104;
goto block_62;
}
case 6:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; size_t x_122; size_t x_123; uint8_t x_124; 
lean_dec(x_10);
lean_dec(x_9);
x_105 = lean_ctor_get(x_4, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_4, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_4, 2);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
lean_inc(x_5);
lean_inc(x_106);
x_109 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_106, x_5, x_6);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_unsigned_to_nat(1u);
x_113 = lean_nat_add(x_5, x_112);
lean_inc(x_107);
x_114 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_107, x_113, x_111);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_122 = lean_ptr_addr(x_106);
lean_dec(x_106);
x_123 = lean_ptr_addr(x_110);
x_124 = lean_usize_dec_eq(x_122, x_123);
if (x_124 == 0)
{
lean_dec(x_107);
x_117 = x_124;
goto block_121;
}
else
{
size_t x_125; size_t x_126; uint8_t x_127; 
x_125 = lean_ptr_addr(x_107);
lean_dec(x_107);
x_126 = lean_ptr_addr(x_115);
x_127 = lean_usize_dec_eq(x_125, x_126);
x_117 = x_127;
goto block_121;
}
block_121:
{
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = l_Lean_Expr_lam___override(x_105, x_110, x_115, x_108);
x_54 = x_118;
x_55 = x_116;
goto block_58;
}
else
{
uint8_t x_119; 
x_119 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_108, x_108);
if (x_119 == 0)
{
lean_object* x_120; 
x_120 = l_Lean_Expr_lam___override(x_105, x_110, x_115, x_108);
x_54 = x_120;
x_55 = x_116;
goto block_58;
}
else
{
lean_dec(x_115);
lean_dec(x_110);
lean_dec(x_105);
lean_inc(x_4);
x_54 = x_4;
x_55 = x_116;
goto block_58;
}
}
}
}
case 7:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; size_t x_145; size_t x_146; uint8_t x_147; 
lean_dec(x_10);
lean_dec(x_9);
x_128 = lean_ctor_get(x_4, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_4, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_4, 2);
lean_inc(x_130);
x_131 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
lean_inc(x_5);
lean_inc(x_129);
x_132 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_129, x_5, x_6);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_nat_add(x_5, x_135);
lean_inc(x_130);
x_137 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_130, x_136, x_134);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_145 = lean_ptr_addr(x_129);
lean_dec(x_129);
x_146 = lean_ptr_addr(x_133);
x_147 = lean_usize_dec_eq(x_145, x_146);
if (x_147 == 0)
{
lean_dec(x_130);
x_140 = x_147;
goto block_144;
}
else
{
size_t x_148; size_t x_149; uint8_t x_150; 
x_148 = lean_ptr_addr(x_130);
lean_dec(x_130);
x_149 = lean_ptr_addr(x_138);
x_150 = lean_usize_dec_eq(x_148, x_149);
x_140 = x_150;
goto block_144;
}
block_144:
{
if (x_140 == 0)
{
lean_object* x_141; 
x_141 = l_Lean_Expr_forallE___override(x_128, x_133, x_138, x_131);
x_54 = x_141;
x_55 = x_139;
goto block_58;
}
else
{
uint8_t x_142; 
x_142 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_131, x_131);
if (x_142 == 0)
{
lean_object* x_143; 
x_143 = l_Lean_Expr_forallE___override(x_128, x_133, x_138, x_131);
x_54 = x_143;
x_55 = x_139;
goto block_58;
}
else
{
lean_dec(x_138);
lean_dec(x_133);
lean_dec(x_128);
lean_inc(x_4);
x_54 = x_4;
x_55 = x_139;
goto block_58;
}
}
}
}
case 8:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; size_t x_174; size_t x_175; uint8_t x_176; 
lean_dec(x_10);
lean_dec(x_9);
x_151 = lean_ctor_get(x_4, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_4, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_4, 2);
lean_inc(x_153);
x_154 = lean_ctor_get(x_4, 3);
lean_inc(x_154);
x_155 = lean_ctor_get_uint8(x_4, sizeof(void*)*4 + 8);
lean_inc(x_5);
lean_inc(x_152);
x_156 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_152, x_5, x_6);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
lean_inc(x_5);
lean_inc(x_153);
x_159 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_153, x_5, x_158);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_unsigned_to_nat(1u);
x_163 = lean_nat_add(x_5, x_162);
lean_inc(x_154);
x_164 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_154, x_163, x_161);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_174 = lean_ptr_addr(x_152);
lean_dec(x_152);
x_175 = lean_ptr_addr(x_157);
x_176 = lean_usize_dec_eq(x_174, x_175);
if (x_176 == 0)
{
lean_dec(x_153);
x_167 = x_176;
goto block_173;
}
else
{
size_t x_177; size_t x_178; uint8_t x_179; 
x_177 = lean_ptr_addr(x_153);
lean_dec(x_153);
x_178 = lean_ptr_addr(x_160);
x_179 = lean_usize_dec_eq(x_177, x_178);
x_167 = x_179;
goto block_173;
}
block_173:
{
if (x_167 == 0)
{
lean_object* x_168; 
lean_dec(x_154);
x_168 = l_Lean_Expr_letE___override(x_151, x_157, x_160, x_165, x_155);
x_54 = x_168;
x_55 = x_166;
goto block_58;
}
else
{
size_t x_169; size_t x_170; uint8_t x_171; 
x_169 = lean_ptr_addr(x_154);
lean_dec(x_154);
x_170 = lean_ptr_addr(x_165);
x_171 = lean_usize_dec_eq(x_169, x_170);
if (x_171 == 0)
{
lean_object* x_172; 
x_172 = l_Lean_Expr_letE___override(x_151, x_157, x_160, x_165, x_155);
x_54 = x_172;
x_55 = x_166;
goto block_58;
}
else
{
lean_dec(x_165);
lean_dec(x_160);
lean_dec(x_157);
lean_dec(x_151);
lean_inc(x_4);
x_54 = x_4;
x_55 = x_166;
goto block_58;
}
}
}
}
case 9:
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_10);
lean_dec(x_9);
x_180 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__7;
x_181 = l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7(x_180, x_6);
x_59 = x_181;
goto block_62;
}
case 10:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; size_t x_187; size_t x_188; uint8_t x_189; 
lean_dec(x_10);
lean_dec(x_9);
x_182 = lean_ctor_get(x_4, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_4, 1);
lean_inc(x_183);
lean_inc(x_5);
lean_inc(x_183);
x_184 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_183, x_5, x_6);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_ptr_addr(x_183);
lean_dec(x_183);
x_188 = lean_ptr_addr(x_185);
x_189 = lean_usize_dec_eq(x_187, x_188);
if (x_189 == 0)
{
lean_object* x_190; 
x_190 = l_Lean_Expr_mdata___override(x_182, x_185);
x_54 = x_190;
x_55 = x_186;
goto block_58;
}
else
{
lean_dec(x_185);
lean_dec(x_182);
lean_inc(x_4);
x_54 = x_4;
x_55 = x_186;
goto block_58;
}
}
default: 
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; size_t x_197; size_t x_198; uint8_t x_199; 
lean_dec(x_10);
lean_dec(x_9);
x_191 = lean_ctor_get(x_4, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_4, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_4, 2);
lean_inc(x_193);
lean_inc(x_5);
lean_inc(x_193);
x_194 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_193, x_5, x_6);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_ptr_addr(x_193);
lean_dec(x_193);
x_198 = lean_ptr_addr(x_195);
x_199 = lean_usize_dec_eq(x_197, x_198);
if (x_199 == 0)
{
lean_object* x_200; 
x_200 = l_Lean_Expr_proj___override(x_191, x_192, x_195);
x_54 = x_200;
x_55 = x_196;
goto block_58;
}
else
{
lean_dec(x_195);
lean_dec(x_192);
lean_dec(x_191);
lean_inc(x_4);
x_54 = x_4;
x_55 = x_196;
goto block_58;
}
}
}
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_201 = lean_ctor_get(x_79, 0);
lean_inc(x_201);
lean_dec(x_79);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_6);
return x_202;
}
block_53:
{
lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
x_15 = lean_array_get_size(x_14);
x_16 = l_Lean_Expr_hash(x_4);
lean_dec(x_4);
x_17 = lean_uint64_of_nat(x_5);
lean_dec(x_5);
x_18 = lean_uint64_mix_hash(x_16, x_17);
x_19 = 32;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = 16;
x_23 = lean_uint64_shift_right(x_21, x_22);
x_24 = lean_uint64_xor(x_21, x_23);
x_25 = lean_uint64_to_usize(x_24);
x_26 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_27 = 1;
x_28 = lean_usize_sub(x_26, x_27);
x_29 = lean_usize_land(x_25, x_28);
x_30 = lean_array_uget(x_14, x_29);
x_31 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_instantiateBetaRevRange_visit_spec__1___redArg(x_11, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_13, x_32);
lean_dec(x_13);
lean_inc(x_12);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_11);
lean_ctor_set(x_34, 1, x_12);
lean_ctor_set(x_34, 2, x_30);
x_35 = lean_array_uset(x_14, x_29, x_34);
x_36 = lean_unsigned_to_nat(4u);
x_37 = lean_nat_mul(x_33, x_36);
x_38 = lean_unsigned_to_nat(3u);
x_39 = lean_nat_div(x_37, x_38);
lean_dec(x_37);
x_40 = lean_array_get_size(x_35);
x_41 = lean_nat_dec_le(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2___redArg(x_35);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_12);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_35);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_12);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_box(0);
x_48 = lean_array_uset(x_14, x_29, x_47);
lean_inc(x_12);
x_49 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Expr_instantiateBetaRevRange_visit_spec__5___redArg(x_11, x_12, x_30);
x_50 = lean_array_uset(x_48, x_29, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_13);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
block_58:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_12 = x_54;
x_13 = x_56;
x_14 = x_57;
goto block_53;
}
block_62:
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_54 = x_60;
x_55 = x_61;
goto block_58;
}
}
else
{
lean_object* x_203; 
lean_dec(x_5);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_4);
lean_ctor_set(x_203, 1, x_6);
return x_203;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Expr_instantiateBetaRevRange_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Expr_instantiateBetaRevRange_visit_spec__0(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_instantiateBetaRevRange_visit_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_instantiateBetaRevRange_visit_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_instantiateBetaRevRange_visit_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_instantiateBetaRevRange_visit_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Expr_instantiateBetaRevRange_visit_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Expr_instantiateBetaRevRange_visit_spec__6___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Expr_instantiateBetaRevRange_visit_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Expr_instantiateBetaRevRange_visit_spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___Lean_Expr_instantiateBetaRevRange_visit_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___Lean_Expr_instantiateBetaRevRange_visit_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Expr.instantiateBetaRevRange", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: stop ≤ args.size\n    ", 44, 42);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange___closed__1;
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(28u);
x_4 = l_Lean_Expr_instantiateBetaRevRange___closed__0;
x_5 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Expr_instantiateBetaRevRange___closed__3;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instantiateBetaRevRange___closed__4;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_instantiateBetaRevRange___closed__5;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_instantiateBetaRevRange___closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_15; 
x_15 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_15 == 0)
{
x_5 = x_15;
goto block_14;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_lt(x_2, x_3);
x_5 = x_16;
goto block_14;
}
block_14:
{
if (x_5 == 0)
{
return x_1;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_le(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = l_Lean_Expr_instantiateBetaRevRange___closed__2;
x_9 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Expr_instantiateBetaRevRange___closed__7;
x_12 = l_Lean_Expr_instantiateBetaRevRange_visit(x_2, x_3, x_4, x_1, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_instantiateBetaRevRange(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("function expected", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwFunctionExpected___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwFunctionExpected___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_Meta_throwFunctionExpected___redArg___closed__1;
x_8 = l_Lean_indentExpr(x_1);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Meta_throwFunctionExpected___redArg___closed__3;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_throwFunctionExpected___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_throwFunctionExpected___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_throwFunctionExpected(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_20; 
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_20 = lean_nat_dec_lt(x_7, x_13);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 7)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_6, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_22, 2);
lean_inc(x_25);
lean_dec(x_22);
lean_ctor_set(x_6, 0, x_25);
x_15 = x_6;
x_16 = x_12;
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_ctor_get(x_22, 2);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_15 = x_28;
x_16 = x_12;
goto block_19;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_6);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_6, 1);
x_31 = lean_ctor_get(x_6, 0);
lean_dec(x_31);
x_32 = l_Lean_Expr_instantiateBetaRevRange(x_22, x_30, x_7, x_1);
lean_dec(x_30);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_33 = lean_whnf(x_32, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 7)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 2);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_7);
lean_ctor_set(x_6, 1, x_7);
lean_ctor_set(x_6, 0, x_36);
x_15 = x_6;
x_16 = x_35;
goto block_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_34);
lean_free_object(x_6);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_nat_add(x_7, x_2);
lean_dec(x_7);
x_39 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_38, x_1, x_3, x_4);
lean_dec(x_38);
x_40 = l_Lean_Meta_throwFunctionExpected___redArg(x_39, x_8, x_9, x_10, x_11, x_37);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
}
else
{
uint8_t x_45; 
lean_free_object(x_6);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_33);
if (x_45 == 0)
{
return x_33;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_33, 0);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_33);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_6, 1);
lean_inc(x_49);
lean_dec(x_6);
x_50 = l_Lean_Expr_instantiateBetaRevRange(x_22, x_49, x_7, x_1);
lean_dec(x_49);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_51 = lean_whnf(x_50, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 7)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 2);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_7);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_7);
x_15 = x_55;
x_16 = x_53;
goto block_19;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_52);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_dec(x_51);
x_57 = lean_nat_add(x_7, x_2);
lean_dec(x_7);
x_58 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_57, x_1, x_3, x_4);
lean_dec(x_57);
x_59 = l_Lean_Meta_throwFunctionExpected___redArg(x_58, x_8, x_9, x_10, x_11, x_56);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_64 = lean_ctor_get(x_51, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_51, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_66 = x_51;
} else {
 lean_dec_ref(x_51);
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
}
block_19:
{
lean_object* x_17; 
x_17 = lean_nat_add(x_7, x_14);
lean_dec(x_7);
x_6 = x_15;
x_7 = x_17;
x_12 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_2);
x_13 = lean_unsigned_to_nat(1u);
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_8, 1, x_11);
x_15 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(x_2, x_13, x_11, x_1, x_14, x_8, x_11, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_instantiateBetaRevRange(x_18, x_19, x_12, x_2);
lean_dec(x_12);
lean_dec(x_19);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_Expr_instantiateBetaRevRange(x_23, x_24, x_12, x_2);
lean_dec(x_12);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_array_get_size(x_2);
x_35 = lean_unsigned_to_nat(1u);
lean_inc(x_34);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
x_38 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(x_2, x_35, x_33, x_1, x_36, x_37, x_33, x_3, x_4, x_5, x_6, x_32);
lean_dec(x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l_Lean_Expr_instantiateBetaRevRange(x_42, x_43, x_34, x_2);
lean_dec(x_34);
lean_dec(x_43);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_34);
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_48 = x_38;
} else {
 lean_dec_ref(x_38);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("incorrect number of universe levels ", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1;
x_9 = l_Lean_Expr_const___override(x_1, x_2);
x_10 = l_Lean_MessageData_ofExpr(x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_throwFunctionExpected___redArg___closed__3;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_throwIncorrectNumberOfLevels(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
static lean_object* _init_l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown constant '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
lean_inc(x_1);
x_14 = l_Lean_Environment_findConstVal_x3f(x_11, x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_7);
x_15 = l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__1;
x_16 = lean_box(0);
x_17 = l_Lean_Expr_const___override(x_1, x_16);
x_18 = l_Lean_MessageData_ofExpr(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__3;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_21, x_2, x_3, x_4, x_5, x_10);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
lean_ctor_set(x_7, 0, x_23);
return x_7;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = lean_unbox(x_27);
lean_inc(x_1);
x_29 = l_Lean_Environment_findConstVal_x3f(x_26, x_1, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__1;
x_31 = lean_box(0);
x_32 = l_Lean_Expr_const___override(x_1, x_31);
x_33 = l_Lean_MessageData_ofExpr(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__3;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_36, x_2, x_3, x_4, x_5, x_25);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_25);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = l_List_lengthTR___redArg(x_11);
lean_dec(x_11);
x_13 = l_List_lengthTR___redArg(x_2);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_9);
x_15 = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = l_Lean_Core_instantiateTypeLevelParams___redArg(x_9, x_2, x_6, x_10);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_19; 
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_19 = lean_nat_dec_lt(x_6, x_12);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
else
{
lean_object* x_21; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = lean_whnf(x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 7)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 2);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Expr_hasLooseBVars(x_24);
if (x_25 == 0)
{
x_14 = x_24;
x_15 = x_23;
goto block_18;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_inc(x_2);
lean_inc(x_6);
lean_inc(x_1);
x_26 = l_Lean_Expr_proj___override(x_1, x_6, x_2);
x_27 = lean_expr_instantiate1(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
x_14 = x_27;
x_15 = x_23;
goto block_18;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_box(0);
lean_inc(x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_30 = lean_apply_7(x_3, lean_box(0), x_29, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_14 = x_22;
x_15 = x_31;
goto block_18;
}
else
{
uint8_t x_32; 
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_30);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
}
block_18:
{
lean_object* x_16; 
x_16 = lean_nat_add(x_6, x_13);
lean_dec(x_6);
x_5 = x_14;
x_6 = x_16;
x_11 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid projection", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nfrom type", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1;
x_13 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_14 = l_Lean_indentExpr(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_indentExpr(x_4);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_throwFunctionExpected___redArg___closed__3;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_21, x_7, x_8, x_9, x_10, x_11);
return x_22;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_infer_type(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = lean_whnf(x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed), 11, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_13);
x_16 = l_Lean_Expr_getAppFn(x_13);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_7, x_14);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_unbox(x_26);
x_28 = l_Lean_Environment_find_x3f(x_25, x_17, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_18);
lean_dec(x_15);
x_29 = lean_box(0);
x_30 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_13, lean_box(0), x_29, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
if (lean_obj_tag(x_31) == 5)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 4);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_15);
goto block_24;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 2);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
lean_dec(x_33);
x_39 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_38, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 6)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_110; uint8_t x_111; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_110 = lean_ctor_get(x_35, 0);
lean_inc(x_110);
lean_dec(x_35);
x_111 = lean_name_eq(x_110, x_1);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
lean_dec(x_42);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_18);
lean_dec(x_15);
x_112 = lean_box(0);
x_113 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_13, lean_box(0), x_112, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
return x_113;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_113, 0);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_113);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
else
{
x_43 = x_4;
x_44 = x_5;
x_45 = x_6;
x_46 = x_7;
x_47 = x_41;
goto block_109;
}
block_109:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_48 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0;
x_49 = l_Lean_Expr_getAppNumArgs(x_13);
lean_inc(x_49);
x_50 = lean_mk_array(x_49, x_48);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_sub(x_49, x_51);
lean_dec(x_49);
lean_inc(x_13);
x_53 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_13, x_50, x_52);
x_54 = lean_nat_add(x_36, x_37);
lean_dec(x_37);
x_55 = lean_array_get_size(x_53);
x_56 = lean_nat_dec_eq(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_53);
lean_dec(x_42);
lean_dec(x_36);
lean_dec(x_18);
lean_dec(x_15);
x_57 = lean_box(0);
x_58 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_13, lean_box(0), x_57, x_43, x_44, x_45, x_46, x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
return x_58;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_42, 0);
lean_inc(x_59);
lean_dec(x_42);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 2);
lean_dec(x_62);
x_63 = lean_ctor_get(x_59, 1);
lean_dec(x_63);
x_64 = l_Lean_Expr_const___override(x_61, x_18);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Array_toSubarray___redArg(x_53, x_65, x_36);
x_67 = l_Array_ofSubarray___redArg(x_66);
lean_dec(x_66);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
x_68 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_64, x_67, x_43, x_44, x_45, x_46, x_47);
lean_dec(x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_2);
lean_ctor_set(x_59, 2, x_51);
lean_ctor_set(x_59, 1, x_2);
lean_ctor_set(x_59, 0, x_65);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_3);
lean_inc(x_1);
x_71 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___redArg(x_1, x_3, x_15, x_59, x_69, x_65, x_43, x_44, x_45, x_46, x_70);
lean_dec(x_59);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
x_74 = lean_whnf(x_72, x_43, x_44, x_45, x_46, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 7)
{
uint8_t x_76; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_74, 0);
lean_dec(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_expr_consume_type_annotations(x_78);
lean_ctor_set(x_74, 0, x_79);
return x_74;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
lean_dec(x_74);
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
lean_dec(x_75);
x_82 = lean_expr_consume_type_annotations(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_75);
x_84 = lean_ctor_get(x_74, 1);
lean_inc(x_84);
lean_dec(x_74);
x_85 = lean_box(0);
x_86 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_13, lean_box(0), x_85, x_43, x_44, x_45, x_46, x_84);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
return x_86;
}
}
else
{
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_74;
}
}
else
{
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_71;
}
}
else
{
lean_free_object(x_59);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_68;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_59, 0);
lean_inc(x_87);
lean_dec(x_59);
x_88 = l_Lean_Expr_const___override(x_87, x_18);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_Array_toSubarray___redArg(x_53, x_89, x_36);
x_91 = l_Array_ofSubarray___redArg(x_90);
lean_dec(x_90);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
x_92 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_88, x_91, x_43, x_44, x_45, x_46, x_47);
lean_dec(x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_2);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_89);
lean_ctor_set(x_95, 1, x_2);
lean_ctor_set(x_95, 2, x_51);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_3);
lean_inc(x_1);
x_96 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___redArg(x_1, x_3, x_15, x_95, x_93, x_89, x_43, x_44, x_45, x_46, x_94);
lean_dec(x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
x_99 = lean_whnf(x_97, x_43, x_44, x_45, x_46, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 7)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_104 = lean_expr_consume_type_annotations(x_103);
if (lean_is_scalar(x_102)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_102;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_101);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
lean_dec(x_99);
x_107 = lean_box(0);
x_108 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_13, lean_box(0), x_107, x_43, x_44, x_45, x_46, x_106);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
return x_108;
}
}
else
{
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_99;
}
}
else
{
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_96;
}
}
else
{
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_92;
}
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_18);
lean_dec(x_15);
x_118 = lean_ctor_get(x_39, 1);
lean_inc(x_118);
lean_dec(x_39);
x_119 = lean_box(0);
x_120 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_13, lean_box(0), x_119, x_4, x_5, x_6, x_7, x_118);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_120;
}
}
else
{
uint8_t x_121; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_39);
if (x_121 == 0)
{
return x_39;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_39, 0);
x_123 = lean_ctor_get(x_39, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_39);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_15);
goto block_24;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_31);
lean_dec(x_18);
lean_dec(x_15);
x_125 = lean_box(0);
x_126 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_13, lean_box(0), x_125, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_126;
}
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_13, lean_box(0), x_22, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_16);
lean_dec(x_15);
x_127 = lean_box(0);
x_128 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_13, lean_box(0), x_127, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_128;
}
}
else
{
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
else
{
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
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExcepted___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type expected", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExcepted___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwTypeExcepted___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_Meta_throwTypeExcepted___redArg___closed__1;
x_8 = l_Lean_indentExpr(x_1);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Meta_throwFunctionExpected___redArg___closed__3;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_throwTypeExcepted___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_throwTypeExcepted___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_throwTypeExcepted(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_7, 7);
x_13 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_12, x_1, x_2);
lean_ctor_set(x_7, 7, x_13);
x_14 = lean_st_ref_set(x_3, x_6, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
x_23 = lean_ctor_get(x_7, 2);
x_24 = lean_ctor_get(x_7, 3);
x_25 = lean_ctor_get(x_7, 4);
x_26 = lean_ctor_get(x_7, 5);
x_27 = lean_ctor_get(x_7, 6);
x_28 = lean_ctor_get(x_7, 7);
x_29 = lean_ctor_get(x_7, 8);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_30 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_28, x_1, x_2);
x_31 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_23);
lean_ctor_set(x_31, 3, x_24);
lean_ctor_set(x_31, 4, x_25);
lean_ctor_set(x_31, 5, x_26);
lean_ctor_set(x_31, 6, x_27);
lean_ctor_set(x_31, 7, x_30);
lean_ctor_set(x_31, 8, x_29);
lean_ctor_set(x_6, 0, x_31);
x_32 = lean_st_ref_set(x_3, x_6, x_8);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_37 = lean_ctor_get(x_6, 1);
x_38 = lean_ctor_get(x_6, 2);
x_39 = lean_ctor_get(x_6, 3);
x_40 = lean_ctor_get(x_6, 4);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_6);
x_41 = lean_ctor_get(x_7, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_7, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_7, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_7, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_7, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 5);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 6);
lean_inc(x_47);
x_48 = lean_ctor_get(x_7, 7);
lean_inc(x_48);
x_49 = lean_ctor_get(x_7, 8);
lean_inc(x_49);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 lean_ctor_release(x_7, 8);
 x_50 = x_7;
} else {
 lean_dec_ref(x_7);
 x_50 = lean_box(0);
}
x_51 = l_Lean_PersistentHashMap_insert___at___Lean_assignExp_spec__0___redArg(x_48, x_1, x_2);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 9, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_42);
lean_ctor_set(x_52, 2, x_43);
lean_ctor_set(x_52, 3, x_44);
lean_ctor_set(x_52, 4, x_45);
lean_ctor_set(x_52, 5, x_46);
lean_ctor_set(x_52, 6, x_47);
lean_ctor_set(x_52, 7, x_51);
lean_ctor_set(x_52, 8, x_49);
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_37);
lean_ctor_set(x_53, 2, x_38);
lean_ctor_set(x_53, 3, x_39);
lean_ctor_set(x_53, 4, x_40);
x_54 = lean_st_ref_set(x_3, x_53, x_8);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_2, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Meta_whnfD(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
switch (lean_obj_tag(x_11)) {
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_13);
x_14 = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(x_13, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Meta_mkFreshLevelMVar(x_2, x_3, x_4, x_5, x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_19);
x_21 = l_Lean_Expr_sort___override(x_19);
x_22 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_13, x_21, x_3, x_20);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_19);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_13);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_dec(x_14);
x_28 = l_Lean_Meta_throwTypeExcepted___redArg(x_1, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
case 3:
{
uint8_t x_33; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_10);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_10, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_11, 0);
lean_inc(x_35);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_35);
return x_10;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_dec(x_10);
x_37 = lean_ctor_get(x_11, 0);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
default: 
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_11);
x_39 = lean_ctor_get(x_10, 1);
lean_inc(x_39);
lean_dec(x_10);
x_40 = l_Lean_Meta_throwTypeExcepted___redArg(x_1, x_2, x_3, x_4, x_5, x_39);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_10);
if (x_41 == 0)
{
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_7);
if (x_45 == 0)
{
return x_7;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_7, 0);
x_47 = lean_ctor_get(x_7, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_7);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = 1;
x_12 = lean_usize_sub(x_2, x_11);
x_13 = lean_array_uget(x_1, x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = lean_infer_type(x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Meta_getLevel(x_15, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_mkLevelIMax_x27(x_18, x_4);
x_2 = x_12;
x_4 = x_20;
x_9 = x_19;
goto _start;
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_2 = x_12;
x_4 = x_22;
x_9 = x_23;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_9);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_23; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Lean_Meta_getLevel(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
x_26 = lean_array_get_size(x_1);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_lt(x_27, x_26);
if (x_28 == 0)
{
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = x_23;
goto block_22;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
lean_dec(x_23);
x_29 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_30 = 0;
x_31 = l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(x_1, x_29, x_30, x_24, x_3, x_4, x_5, x_6, x_25);
x_8 = x_31;
goto block_22;
}
}
else
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_23);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
block_22:
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Level_normalize(x_10);
lean_dec(x_10);
x_12 = l_Lean_Expr_sort___override(x_11);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = l_Lean_Level_normalize(x_13);
lean_dec(x_13);
x_16 = l_Lean_Expr_sort___override(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed), 7, 0);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(x_1, x_7, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___lam__0), 8, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_box(1);
x_11 = lean_box(0);
x_12 = lean_unbox(x_10);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___redArg(x_1, x_12, x_11, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_box(1);
x_13 = lean_box(1);
x_14 = lean_unbox(x_11);
x_15 = lean_unbox(x_12);
x_16 = lean_unbox(x_13);
x_17 = l_Lean_Meta_mkForallFVars(x_1, x_9, x_14, x_15, x_16, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0), 7, 0);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(x_1, x_7, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown metavariable '\?", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwUnknownMVar___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_Meta_throwUnknownMVar___redArg___closed__1;
x_8 = l_Lean_MessageData_ofName(x_1);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__3;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_throwUnknownMVar___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_throwUnknownMVar___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_throwUnknownMVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_3, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = l_Lean_MetavarContext_findDecl_x3f(x_11, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_free_object(x_7);
x_13 = l_Lean_Meta_throwUnknownMVar___redArg(x_1, x_2, x_3, x_4, x_5, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
lean_dec(x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_1);
x_19 = l_Lean_MetavarContext_findDecl_x3f(x_18, x_1);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = l_Lean_Meta_throwUnknownMVar___redArg(x_1, x_2, x_3, x_4, x_5, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_1);
x_7 = lean_local_ctx_find(x_6, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = l_Lean_FVarId_throwUnknown___redArg(x_1, x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instBEqExprConfigCacheKey___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instHashableExprConfigCacheKey___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_hasMVar(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = l_Lean_Meta_mkExprConfigCacheKey___redArg(x_1, x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_4, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0;
x_20 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1;
lean_inc(x_10);
x_21 = l_Lean_PersistentHashMap_find_x3f___redArg(x_19, x_20, x_18, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_free_object(x_12);
lean_inc(x_4);
x_22 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = l_Lean_Expr_hasMVar(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_22);
x_26 = lean_st_ref_take(x_4, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 1);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_23);
x_34 = l_Lean_PersistentHashMap_insert___redArg(x_19, x_20, x_33, x_10, x_23);
lean_ctor_set(x_28, 0, x_34);
x_35 = lean_st_ref_set(x_4, x_27, x_29);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_23);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_23);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_40 = lean_ctor_get(x_28, 0);
x_41 = lean_ctor_get(x_28, 1);
x_42 = lean_ctor_get(x_28, 2);
x_43 = lean_ctor_get(x_28, 3);
x_44 = lean_ctor_get(x_28, 4);
x_45 = lean_ctor_get(x_28, 5);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_28);
lean_inc(x_23);
x_46 = l_Lean_PersistentHashMap_insert___redArg(x_19, x_20, x_40, x_10, x_23);
x_47 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
lean_ctor_set(x_47, 2, x_42);
lean_ctor_set(x_47, 3, x_43);
lean_ctor_set(x_47, 4, x_44);
lean_ctor_set(x_47, 5, x_45);
lean_ctor_set(x_27, 1, x_47);
x_48 = lean_st_ref_set(x_4, x_27, x_29);
lean_dec(x_4);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_23);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_52 = lean_ctor_get(x_27, 0);
x_53 = lean_ctor_get(x_27, 2);
x_54 = lean_ctor_get(x_27, 3);
x_55 = lean_ctor_get(x_27, 4);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_27);
x_56 = lean_ctor_get(x_28, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_28, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_28, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_28, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_28, 4);
lean_inc(x_60);
x_61 = lean_ctor_get(x_28, 5);
lean_inc(x_61);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 lean_ctor_release(x_28, 4);
 lean_ctor_release(x_28, 5);
 x_62 = x_28;
} else {
 lean_dec_ref(x_28);
 x_62 = lean_box(0);
}
lean_inc(x_23);
x_63 = l_Lean_PersistentHashMap_insert___redArg(x_19, x_20, x_56, x_10, x_23);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 6, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_57);
lean_ctor_set(x_64, 2, x_58);
lean_ctor_set(x_64, 3, x_59);
lean_ctor_set(x_64, 4, x_60);
lean_ctor_set(x_64, 5, x_61);
x_65 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_65, 0, x_52);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_53);
lean_ctor_set(x_65, 3, x_54);
lean_ctor_set(x_65, 4, x_55);
x_66 = lean_st_ref_set(x_4, x_65, x_29);
lean_dec(x_4);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_23);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_4);
return x_22;
}
}
else
{
lean_dec(x_10);
lean_dec(x_4);
return x_22;
}
}
else
{
lean_object* x_70; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_70 = lean_ctor_get(x_21, 0);
lean_inc(x_70);
lean_dec(x_21);
lean_ctor_set(x_12, 0, x_70);
return x_12;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_12, 1);
lean_inc(x_71);
lean_dec(x_12);
x_72 = lean_ctor_get(x_14, 0);
lean_inc(x_72);
lean_dec(x_14);
x_73 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0;
x_74 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1;
lean_inc(x_10);
x_75 = l_Lean_PersistentHashMap_find_x3f___redArg(x_73, x_74, x_72, x_10);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
lean_inc(x_4);
x_76 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_71);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
x_79 = l_Lean_Expr_hasMVar(x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_76);
x_80 = lean_st_ref_take(x_4, x_78);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_81, 2);
lean_inc(x_85);
x_86 = lean_ctor_get(x_81, 3);
lean_inc(x_86);
x_87 = lean_ctor_get(x_81, 4);
lean_inc(x_87);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 lean_ctor_release(x_81, 2);
 lean_ctor_release(x_81, 3);
 lean_ctor_release(x_81, 4);
 x_88 = x_81;
} else {
 lean_dec_ref(x_81);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_82, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_82, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_82, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_82, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_82, 4);
lean_inc(x_93);
x_94 = lean_ctor_get(x_82, 5);
lean_inc(x_94);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 lean_ctor_release(x_82, 2);
 lean_ctor_release(x_82, 3);
 lean_ctor_release(x_82, 4);
 lean_ctor_release(x_82, 5);
 x_95 = x_82;
} else {
 lean_dec_ref(x_82);
 x_95 = lean_box(0);
}
lean_inc(x_77);
x_96 = l_Lean_PersistentHashMap_insert___redArg(x_73, x_74, x_89, x_10, x_77);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 6, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_90);
lean_ctor_set(x_97, 2, x_91);
lean_ctor_set(x_97, 3, x_92);
lean_ctor_set(x_97, 4, x_93);
lean_ctor_set(x_97, 5, x_94);
if (lean_is_scalar(x_88)) {
 x_98 = lean_alloc_ctor(0, 5, 0);
} else {
 x_98 = x_88;
}
lean_ctor_set(x_98, 0, x_84);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_98, 2, x_85);
lean_ctor_set(x_98, 3, x_86);
lean_ctor_set(x_98, 4, x_87);
x_99 = lean_st_ref_set(x_4, x_98, x_83);
lean_dec(x_4);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_77);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
else
{
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_10);
lean_dec(x_4);
return x_76;
}
}
else
{
lean_dec(x_10);
lean_dec(x_4);
return x_76;
}
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_103 = lean_ctor_get(x_75, 0);
lean_inc(x_103);
lean_dec(x_75);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_71);
return x_104;
}
}
}
else
{
lean_object* x_105; 
lean_dec(x_1);
x_105 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_105;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_42; uint64_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; lean_object* x_98; uint8_t x_99; uint8_t x_100; 
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
x_43 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_44 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_45 = lean_ctor_get(x_2, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 4);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 5);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 6);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_52 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_53 = x_2;
} else {
 lean_dec_ref(x_2);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get_uint8(x_42, 0);
x_55 = lean_ctor_get_uint8(x_42, 1);
x_56 = lean_ctor_get_uint8(x_42, 2);
x_57 = lean_ctor_get_uint8(x_42, 3);
x_58 = lean_ctor_get_uint8(x_42, 4);
x_59 = lean_ctor_get_uint8(x_42, 5);
x_60 = lean_ctor_get_uint8(x_42, 6);
x_61 = lean_ctor_get_uint8(x_42, 7);
x_62 = lean_ctor_get_uint8(x_42, 8);
x_63 = lean_ctor_get_uint8(x_42, 9);
x_64 = lean_ctor_get_uint8(x_42, 10);
x_65 = lean_ctor_get_uint8(x_42, 11);
x_66 = lean_ctor_get_uint8(x_42, 12);
x_67 = lean_ctor_get_uint8(x_42, 13);
x_68 = lean_ctor_get_uint8(x_42, 14);
x_69 = lean_ctor_get_uint8(x_42, 15);
x_70 = lean_ctor_get_uint8(x_42, 16);
x_71 = lean_ctor_get_uint8(x_42, 17);
if (lean_is_exclusive(x_42)) {
 x_72 = x_42;
} else {
 lean_dec_ref(x_42);
 x_72 = lean_box(0);
}
x_98 = lean_box(1);
x_99 = lean_unbox(x_98);
x_100 = l_Lean_Meta_TransparencyMode_lt(x_63, x_99);
if (x_100 == 0)
{
x_73 = x_63;
goto block_97;
}
else
{
uint8_t x_101; 
x_101 = lean_unbox(x_98);
x_73 = x_101;
goto block_97;
}
block_41:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint64_t x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_box(1);
x_31 = lean_box(2);
x_32 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_32, 0, x_10);
lean_ctor_set_uint8(x_32, 1, x_23);
lean_ctor_set_uint8(x_32, 2, x_11);
lean_ctor_set_uint8(x_32, 3, x_21);
lean_ctor_set_uint8(x_32, 4, x_12);
lean_ctor_set_uint8(x_32, 5, x_18);
lean_ctor_set_uint8(x_32, 6, x_24);
lean_ctor_set_uint8(x_32, 7, x_29);
lean_ctor_set_uint8(x_32, 8, x_28);
lean_ctor_set_uint8(x_32, 9, x_13);
lean_ctor_set_uint8(x_32, 10, x_27);
lean_ctor_set_uint8(x_32, 11, x_25);
x_33 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, 12, x_33);
x_34 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, 13, x_34);
x_35 = lean_unbox(x_31);
lean_ctor_set_uint8(x_32, 14, x_35);
x_36 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, 15, x_36);
x_37 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, 16, x_37);
lean_ctor_set_uint8(x_32, 17, x_8);
x_38 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_32);
x_39 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_7);
lean_ctor_set(x_39, 2, x_19);
lean_ctor_set(x_39, 3, x_15);
lean_ctor_set(x_39, 4, x_22);
lean_ctor_set(x_39, 5, x_26);
lean_ctor_set(x_39, 6, x_20);
lean_ctor_set_uint64(x_39, sizeof(void*)*7, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 8, x_16);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 9, x_14);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 10, x_9);
x_40 = lean_apply_5(x_1, x_39, x_3, x_4, x_5, x_17);
return x_40;
}
block_97:
{
lean_object* x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 0, 18);
} else {
 x_74 = x_72;
}
lean_ctor_set_uint8(x_74, 0, x_54);
lean_ctor_set_uint8(x_74, 1, x_55);
lean_ctor_set_uint8(x_74, 2, x_56);
lean_ctor_set_uint8(x_74, 3, x_57);
lean_ctor_set_uint8(x_74, 4, x_58);
lean_ctor_set_uint8(x_74, 5, x_59);
lean_ctor_set_uint8(x_74, 6, x_60);
lean_ctor_set_uint8(x_74, 7, x_61);
lean_ctor_set_uint8(x_74, 8, x_62);
lean_ctor_set_uint8(x_74, 9, x_73);
lean_ctor_set_uint8(x_74, 10, x_64);
lean_ctor_set_uint8(x_74, 11, x_65);
lean_ctor_set_uint8(x_74, 12, x_66);
lean_ctor_set_uint8(x_74, 13, x_67);
lean_ctor_set_uint8(x_74, 14, x_68);
lean_ctor_set_uint8(x_74, 15, x_69);
lean_ctor_set_uint8(x_74, 16, x_70);
lean_ctor_set_uint8(x_74, 17, x_71);
x_75 = 2;
x_76 = lean_uint64_shift_right(x_43, x_75);
x_77 = lean_uint64_shift_left(x_76, x_75);
x_78 = l_Lean_Meta_TransparencyMode_toUInt64(x_73);
x_79 = lean_uint64_lor(x_77, x_78);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
if (lean_is_scalar(x_53)) {
 x_80 = lean_alloc_ctor(0, 7, 11);
} else {
 x_80 = x_53;
}
lean_ctor_set(x_80, 0, x_74);
lean_ctor_set(x_80, 1, x_45);
lean_ctor_set(x_80, 2, x_46);
lean_ctor_set(x_80, 3, x_47);
lean_ctor_set(x_80, 4, x_48);
lean_ctor_set(x_80, 5, x_49);
lean_ctor_set(x_80, 6, x_50);
lean_ctor_set_uint64(x_80, sizeof(void*)*7, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 8, x_44);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 9, x_51);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 10, x_52);
x_81 = l_Lean_Meta_getConfig___redArg(x_80, x_6);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get_uint8(x_82, 13);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_82);
lean_dec(x_80);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_7 = x_45;
x_8 = x_71;
x_9 = x_52;
x_10 = x_54;
x_11 = x_56;
x_12 = x_58;
x_13 = x_73;
x_14 = x_51;
x_15 = x_47;
x_16 = x_44;
x_17 = x_84;
x_18 = x_59;
x_19 = x_46;
x_20 = x_50;
x_21 = x_57;
x_22 = x_48;
x_23 = x_55;
x_24 = x_60;
x_25 = x_65;
x_26 = x_49;
x_27 = x_64;
x_28 = x_62;
x_29 = x_61;
goto block_41;
}
else
{
uint8_t x_85; 
x_85 = lean_ctor_get_uint8(x_82, 12);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_82);
lean_dec(x_80);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
lean_dec(x_81);
x_7 = x_45;
x_8 = x_71;
x_9 = x_52;
x_10 = x_54;
x_11 = x_56;
x_12 = x_58;
x_13 = x_73;
x_14 = x_51;
x_15 = x_47;
x_16 = x_44;
x_17 = x_86;
x_18 = x_59;
x_19 = x_46;
x_20 = x_50;
x_21 = x_57;
x_22 = x_48;
x_23 = x_55;
x_24 = x_60;
x_25 = x_65;
x_26 = x_49;
x_27 = x_64;
x_28 = x_62;
x_29 = x_61;
goto block_41;
}
else
{
uint8_t x_87; 
x_87 = lean_ctor_get_uint8(x_82, 15);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_82);
lean_dec(x_80);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
lean_dec(x_81);
x_7 = x_45;
x_8 = x_71;
x_9 = x_52;
x_10 = x_54;
x_11 = x_56;
x_12 = x_58;
x_13 = x_73;
x_14 = x_51;
x_15 = x_47;
x_16 = x_44;
x_17 = x_88;
x_18 = x_59;
x_19 = x_46;
x_20 = x_50;
x_21 = x_57;
x_22 = x_48;
x_23 = x_55;
x_24 = x_60;
x_25 = x_65;
x_26 = x_49;
x_27 = x_64;
x_28 = x_62;
x_29 = x_61;
goto block_41;
}
else
{
uint8_t x_89; 
x_89 = lean_ctor_get_uint8(x_82, 16);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_82);
lean_dec(x_80);
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
lean_dec(x_81);
x_7 = x_45;
x_8 = x_71;
x_9 = x_52;
x_10 = x_54;
x_11 = x_56;
x_12 = x_58;
x_13 = x_73;
x_14 = x_51;
x_15 = x_47;
x_16 = x_44;
x_17 = x_90;
x_18 = x_59;
x_19 = x_46;
x_20 = x_50;
x_21 = x_57;
x_22 = x_48;
x_23 = x_55;
x_24 = x_60;
x_25 = x_65;
x_26 = x_49;
x_27 = x_64;
x_28 = x_62;
x_29 = x_61;
goto block_41;
}
else
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; uint8_t x_95; 
x_91 = lean_ctor_get(x_81, 1);
lean_inc(x_91);
lean_dec(x_81);
x_92 = lean_ctor_get_uint8(x_82, 14);
lean_dec(x_82);
x_93 = lean_box(2);
x_94 = lean_unbox(x_93);
x_95 = l_Lean_Meta_instDecidableEqProjReductionKind(x_92, x_94);
if (x_95 == 0)
{
lean_dec(x_80);
x_7 = x_45;
x_8 = x_71;
x_9 = x_52;
x_10 = x_54;
x_11 = x_56;
x_12 = x_58;
x_13 = x_73;
x_14 = x_51;
x_15 = x_47;
x_16 = x_44;
x_17 = x_91;
x_18 = x_59;
x_19 = x_46;
x_20 = x_50;
x_21 = x_57;
x_22 = x_48;
x_23 = x_55;
x_24 = x_60;
x_25 = x_65;
x_26 = x_49;
x_27 = x_64;
x_28 = x_62;
x_29 = x_61;
goto block_41;
}
else
{
lean_object* x_96; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
x_96 = lean_apply_5(x_1, x_80, x_3, x_4, x_5, x_91);
return x_96;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_43; uint64_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; uint8_t x_74; lean_object* x_99; uint8_t x_100; uint8_t x_101; 
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
x_44 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_45 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_46 = lean_ctor_get(x_3, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_3, 4);
lean_inc(x_49);
x_50 = lean_ctor_get(x_3, 5);
lean_inc(x_50);
x_51 = lean_ctor_get(x_3, 6);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_53 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 x_54 = x_3;
} else {
 lean_dec_ref(x_3);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get_uint8(x_43, 0);
x_56 = lean_ctor_get_uint8(x_43, 1);
x_57 = lean_ctor_get_uint8(x_43, 2);
x_58 = lean_ctor_get_uint8(x_43, 3);
x_59 = lean_ctor_get_uint8(x_43, 4);
x_60 = lean_ctor_get_uint8(x_43, 5);
x_61 = lean_ctor_get_uint8(x_43, 6);
x_62 = lean_ctor_get_uint8(x_43, 7);
x_63 = lean_ctor_get_uint8(x_43, 8);
x_64 = lean_ctor_get_uint8(x_43, 9);
x_65 = lean_ctor_get_uint8(x_43, 10);
x_66 = lean_ctor_get_uint8(x_43, 11);
x_67 = lean_ctor_get_uint8(x_43, 12);
x_68 = lean_ctor_get_uint8(x_43, 13);
x_69 = lean_ctor_get_uint8(x_43, 14);
x_70 = lean_ctor_get_uint8(x_43, 15);
x_71 = lean_ctor_get_uint8(x_43, 16);
x_72 = lean_ctor_get_uint8(x_43, 17);
if (lean_is_exclusive(x_43)) {
 x_73 = x_43;
} else {
 lean_dec_ref(x_43);
 x_73 = lean_box(0);
}
x_99 = lean_box(1);
x_100 = lean_unbox(x_99);
x_101 = l_Lean_Meta_TransparencyMode_lt(x_64, x_100);
if (x_101 == 0)
{
x_74 = x_64;
goto block_98;
}
else
{
uint8_t x_102; 
x_102 = lean_unbox(x_99);
x_74 = x_102;
goto block_98;
}
block_42:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint64_t x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_box(1);
x_32 = lean_box(2);
x_33 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_33, 0, x_11);
lean_ctor_set_uint8(x_33, 1, x_24);
lean_ctor_set_uint8(x_33, 2, x_12);
lean_ctor_set_uint8(x_33, 3, x_22);
lean_ctor_set_uint8(x_33, 4, x_13);
lean_ctor_set_uint8(x_33, 5, x_19);
lean_ctor_set_uint8(x_33, 6, x_25);
lean_ctor_set_uint8(x_33, 7, x_30);
lean_ctor_set_uint8(x_33, 8, x_29);
lean_ctor_set_uint8(x_33, 9, x_14);
lean_ctor_set_uint8(x_33, 10, x_28);
lean_ctor_set_uint8(x_33, 11, x_26);
x_34 = lean_unbox(x_31);
lean_ctor_set_uint8(x_33, 12, x_34);
x_35 = lean_unbox(x_31);
lean_ctor_set_uint8(x_33, 13, x_35);
x_36 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, 14, x_36);
x_37 = lean_unbox(x_31);
lean_ctor_set_uint8(x_33, 15, x_37);
x_38 = lean_unbox(x_31);
lean_ctor_set_uint8(x_33, 16, x_38);
lean_ctor_set_uint8(x_33, 17, x_9);
x_39 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_33);
x_40 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_8);
lean_ctor_set(x_40, 2, x_20);
lean_ctor_set(x_40, 3, x_16);
lean_ctor_set(x_40, 4, x_23);
lean_ctor_set(x_40, 5, x_27);
lean_ctor_set(x_40, 6, x_21);
lean_ctor_set_uint64(x_40, sizeof(void*)*7, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*7 + 8, x_17);
lean_ctor_set_uint8(x_40, sizeof(void*)*7 + 9, x_15);
lean_ctor_set_uint8(x_40, sizeof(void*)*7 + 10, x_10);
x_41 = lean_apply_5(x_2, x_40, x_4, x_5, x_6, x_18);
return x_41;
}
block_98:
{
lean_object* x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 0, 18);
} else {
 x_75 = x_73;
}
lean_ctor_set_uint8(x_75, 0, x_55);
lean_ctor_set_uint8(x_75, 1, x_56);
lean_ctor_set_uint8(x_75, 2, x_57);
lean_ctor_set_uint8(x_75, 3, x_58);
lean_ctor_set_uint8(x_75, 4, x_59);
lean_ctor_set_uint8(x_75, 5, x_60);
lean_ctor_set_uint8(x_75, 6, x_61);
lean_ctor_set_uint8(x_75, 7, x_62);
lean_ctor_set_uint8(x_75, 8, x_63);
lean_ctor_set_uint8(x_75, 9, x_74);
lean_ctor_set_uint8(x_75, 10, x_65);
lean_ctor_set_uint8(x_75, 11, x_66);
lean_ctor_set_uint8(x_75, 12, x_67);
lean_ctor_set_uint8(x_75, 13, x_68);
lean_ctor_set_uint8(x_75, 14, x_69);
lean_ctor_set_uint8(x_75, 15, x_70);
lean_ctor_set_uint8(x_75, 16, x_71);
lean_ctor_set_uint8(x_75, 17, x_72);
x_76 = 2;
x_77 = lean_uint64_shift_right(x_44, x_76);
x_78 = lean_uint64_shift_left(x_77, x_76);
x_79 = l_Lean_Meta_TransparencyMode_toUInt64(x_74);
x_80 = lean_uint64_lor(x_78, x_79);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
if (lean_is_scalar(x_54)) {
 x_81 = lean_alloc_ctor(0, 7, 11);
} else {
 x_81 = x_54;
}
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_46);
lean_ctor_set(x_81, 2, x_47);
lean_ctor_set(x_81, 3, x_48);
lean_ctor_set(x_81, 4, x_49);
lean_ctor_set(x_81, 5, x_50);
lean_ctor_set(x_81, 6, x_51);
lean_ctor_set_uint64(x_81, sizeof(void*)*7, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 8, x_45);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 9, x_52);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 10, x_53);
x_82 = l_Lean_Meta_getConfig___redArg(x_81, x_7);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get_uint8(x_83, 13);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_83);
lean_dec(x_81);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_8 = x_46;
x_9 = x_72;
x_10 = x_53;
x_11 = x_55;
x_12 = x_57;
x_13 = x_59;
x_14 = x_74;
x_15 = x_52;
x_16 = x_48;
x_17 = x_45;
x_18 = x_85;
x_19 = x_60;
x_20 = x_47;
x_21 = x_51;
x_22 = x_58;
x_23 = x_49;
x_24 = x_56;
x_25 = x_61;
x_26 = x_66;
x_27 = x_50;
x_28 = x_65;
x_29 = x_63;
x_30 = x_62;
goto block_42;
}
else
{
uint8_t x_86; 
x_86 = lean_ctor_get_uint8(x_83, 12);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_83);
lean_dec(x_81);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
lean_dec(x_82);
x_8 = x_46;
x_9 = x_72;
x_10 = x_53;
x_11 = x_55;
x_12 = x_57;
x_13 = x_59;
x_14 = x_74;
x_15 = x_52;
x_16 = x_48;
x_17 = x_45;
x_18 = x_87;
x_19 = x_60;
x_20 = x_47;
x_21 = x_51;
x_22 = x_58;
x_23 = x_49;
x_24 = x_56;
x_25 = x_61;
x_26 = x_66;
x_27 = x_50;
x_28 = x_65;
x_29 = x_63;
x_30 = x_62;
goto block_42;
}
else
{
uint8_t x_88; 
x_88 = lean_ctor_get_uint8(x_83, 15);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_83);
lean_dec(x_81);
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
lean_dec(x_82);
x_8 = x_46;
x_9 = x_72;
x_10 = x_53;
x_11 = x_55;
x_12 = x_57;
x_13 = x_59;
x_14 = x_74;
x_15 = x_52;
x_16 = x_48;
x_17 = x_45;
x_18 = x_89;
x_19 = x_60;
x_20 = x_47;
x_21 = x_51;
x_22 = x_58;
x_23 = x_49;
x_24 = x_56;
x_25 = x_61;
x_26 = x_66;
x_27 = x_50;
x_28 = x_65;
x_29 = x_63;
x_30 = x_62;
goto block_42;
}
else
{
uint8_t x_90; 
x_90 = lean_ctor_get_uint8(x_83, 16);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec(x_83);
lean_dec(x_81);
x_91 = lean_ctor_get(x_82, 1);
lean_inc(x_91);
lean_dec(x_82);
x_8 = x_46;
x_9 = x_72;
x_10 = x_53;
x_11 = x_55;
x_12 = x_57;
x_13 = x_59;
x_14 = x_74;
x_15 = x_52;
x_16 = x_48;
x_17 = x_45;
x_18 = x_91;
x_19 = x_60;
x_20 = x_47;
x_21 = x_51;
x_22 = x_58;
x_23 = x_49;
x_24 = x_56;
x_25 = x_61;
x_26 = x_66;
x_27 = x_50;
x_28 = x_65;
x_29 = x_63;
x_30 = x_62;
goto block_42;
}
else
{
lean_object* x_92; uint8_t x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_82, 1);
lean_inc(x_92);
lean_dec(x_82);
x_93 = lean_ctor_get_uint8(x_83, 14);
lean_dec(x_83);
x_94 = lean_box(2);
x_95 = lean_unbox(x_94);
x_96 = l_Lean_Meta_instDecidableEqProjReductionKind(x_93, x_95);
if (x_96 == 0)
{
lean_dec(x_81);
x_8 = x_46;
x_9 = x_72;
x_10 = x_53;
x_11 = x_55;
x_12 = x_57;
x_13 = x_59;
x_14 = x_74;
x_15 = x_52;
x_16 = x_48;
x_17 = x_45;
x_18 = x_92;
x_19 = x_60;
x_20 = x_47;
x_21 = x_51;
x_22 = x_58;
x_23 = x_49;
x_24 = x_56;
x_25 = x_61;
x_26 = x_66;
x_27 = x_50;
x_28 = x_65;
x_29 = x_63;
x_30 = x_62;
goto block_42;
}
else
{
lean_object* x_97; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
x_97 = lean_apply_5(x_2, x_81, x_4, x_5, x_6, x_92);
return x_97;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; size_t x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
x_5 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0;
x_6 = l_Lean_Expr_hash(x_3);
lean_dec(x_3);
x_7 = lean_uint64_mix_hash(x_6, x_4);
x_8 = lean_uint64_to_usize(x_7);
x_9 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f_spec__0___redArg(x_5, x_1, x_8, x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
x_6 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0;
x_7 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1;
x_8 = l_Lean_Expr_hash(x_4);
lean_dec(x_4);
x_9 = lean_uint64_mix_hash(x_8, x_5);
x_10 = lean_uint64_to_usize(x_9);
x_11 = 1;
x_12 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(x_6, x_7, x_1, x_10, x_11, x_2, x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_inferTypeImp_infer___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected bound variable ", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_inferTypeImp_infer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_inferTypeImp_infer___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp_infer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Meta_inferTypeImp_infer___closed__1;
x_9 = l_Lean_Expr_bvar___override(x_7);
x_10 = l_Lean_MessageData_ofExpr(x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_throwFunctionExpected___redArg___closed__3;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_13, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(x_15, x_2, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
case 2:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(x_17, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
case 3:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l_Lean_Level_succ___override(x_19);
x_21 = l_Lean_Expr_sort___override(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
return x_22;
}
case 4:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_24, x_23, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = l_Lean_Expr_hasMVar(x_1);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = l_Lean_Meta_mkExprConfigCacheKey___redArg(x_1, x_2, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_ref_get(x_3, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 1);
x_36 = lean_ctor_get(x_31, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
lean_inc(x_29);
x_38 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0___redArg(x_37, x_29);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_free_object(x_31);
x_39 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_26, x_23, x_2, x_3, x_4, x_5, x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
x_42 = l_Lean_Expr_hasMVar(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_39);
x_43 = lean_st_ref_take(x_3, x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_44, 1);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_40);
x_51 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_50, x_29, x_40);
lean_ctor_set(x_45, 0, x_51);
x_52 = lean_st_ref_set(x_3, x_44, x_46);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_40);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_40);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_57 = lean_ctor_get(x_45, 0);
x_58 = lean_ctor_get(x_45, 1);
x_59 = lean_ctor_get(x_45, 2);
x_60 = lean_ctor_get(x_45, 3);
x_61 = lean_ctor_get(x_45, 4);
x_62 = lean_ctor_get(x_45, 5);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_45);
lean_inc(x_40);
x_63 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_57, x_29, x_40);
x_64 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
lean_ctor_set(x_64, 2, x_59);
lean_ctor_set(x_64, 3, x_60);
lean_ctor_set(x_64, 4, x_61);
lean_ctor_set(x_64, 5, x_62);
lean_ctor_set(x_44, 1, x_64);
x_65 = lean_st_ref_set(x_3, x_44, x_46);
lean_dec(x_3);
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
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_40);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_69 = lean_ctor_get(x_44, 0);
x_70 = lean_ctor_get(x_44, 2);
x_71 = lean_ctor_get(x_44, 3);
x_72 = lean_ctor_get(x_44, 4);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_44);
x_73 = lean_ctor_get(x_45, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_45, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_45, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_45, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_45, 4);
lean_inc(x_77);
x_78 = lean_ctor_get(x_45, 5);
lean_inc(x_78);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 lean_ctor_release(x_45, 4);
 lean_ctor_release(x_45, 5);
 x_79 = x_45;
} else {
 lean_dec_ref(x_45);
 x_79 = lean_box(0);
}
lean_inc(x_40);
x_80 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_73, x_29, x_40);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 6, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_74);
lean_ctor_set(x_81, 2, x_75);
lean_ctor_set(x_81, 3, x_76);
lean_ctor_set(x_81, 4, x_77);
lean_ctor_set(x_81, 5, x_78);
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_69);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_70);
lean_ctor_set(x_82, 3, x_71);
lean_ctor_set(x_82, 4, x_72);
x_83 = lean_st_ref_set(x_3, x_82, x_46);
lean_dec(x_3);
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
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_40);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_29);
lean_dec(x_3);
return x_39;
}
}
else
{
lean_dec(x_29);
lean_dec(x_3);
return x_39;
}
}
else
{
lean_object* x_87; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_87 = lean_ctor_get(x_38, 0);
lean_inc(x_87);
lean_dec(x_38);
lean_ctor_set(x_31, 0, x_87);
return x_31;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_31, 1);
lean_inc(x_88);
lean_dec(x_31);
x_89 = lean_ctor_get(x_33, 0);
lean_inc(x_89);
lean_dec(x_33);
lean_inc(x_29);
x_90 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0___redArg(x_89, x_29);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_26, x_23, x_2, x_3, x_4, x_5, x_88);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
x_94 = l_Lean_Expr_hasMVar(x_92);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_91);
x_95 = lean_st_ref_take(x_3, x_93);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_96, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_96, 4);
lean_inc(x_102);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 lean_ctor_release(x_96, 2);
 lean_ctor_release(x_96, 3);
 lean_ctor_release(x_96, 4);
 x_103 = x_96;
} else {
 lean_dec_ref(x_96);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_97, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_97, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_97, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_97, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_97, 4);
lean_inc(x_108);
x_109 = lean_ctor_get(x_97, 5);
lean_inc(x_109);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 lean_ctor_release(x_97, 2);
 lean_ctor_release(x_97, 3);
 lean_ctor_release(x_97, 4);
 lean_ctor_release(x_97, 5);
 x_110 = x_97;
} else {
 lean_dec_ref(x_97);
 x_110 = lean_box(0);
}
lean_inc(x_92);
x_111 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_104, x_29, x_92);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 6, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_105);
lean_ctor_set(x_112, 2, x_106);
lean_ctor_set(x_112, 3, x_107);
lean_ctor_set(x_112, 4, x_108);
lean_ctor_set(x_112, 5, x_109);
if (lean_is_scalar(x_103)) {
 x_113 = lean_alloc_ctor(0, 5, 0);
} else {
 x_113 = x_103;
}
lean_ctor_set(x_113, 0, x_99);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_113, 2, x_100);
lean_ctor_set(x_113, 3, x_101);
lean_ctor_set(x_113, 4, x_102);
x_114 = lean_st_ref_set(x_3, x_113, x_98);
lean_dec(x_3);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_92);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
else
{
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_29);
lean_dec(x_3);
return x_91;
}
}
else
{
lean_dec(x_29);
lean_dec(x_3);
return x_91;
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_118 = lean_ctor_get(x_90, 0);
lean_inc(x_118);
lean_dec(x_90);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_88);
return x_119;
}
}
}
else
{
lean_object* x_120; 
lean_dec(x_1);
x_120 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_26, x_23, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_120;
}
}
}
case 5:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_121 = lean_ctor_get(x_1, 0);
lean_inc(x_121);
x_122 = l_Lean_Expr_getAppFn(x_121);
lean_dec(x_121);
x_123 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0;
x_124 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_124);
x_125 = lean_mk_array(x_124, x_123);
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_nat_sub(x_124, x_126);
lean_dec(x_124);
lean_inc(x_1);
x_128 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_125, x_127);
x_129 = l_Lean_Expr_hasMVar(x_1);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_130 = l_Lean_Meta_mkExprConfigCacheKey___redArg(x_1, x_2, x_6);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_st_ref_get(x_3, x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = !lean_is_exclusive(x_133);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_133, 1);
x_138 = lean_ctor_get(x_133, 0);
lean_dec(x_138);
x_139 = lean_ctor_get(x_135, 0);
lean_inc(x_139);
lean_dec(x_135);
lean_inc(x_131);
x_140 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0___redArg(x_139, x_131);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
lean_free_object(x_133);
lean_inc(x_3);
x_141 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_122, x_128, x_2, x_3, x_4, x_5, x_137);
lean_dec(x_128);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
x_144 = l_Lean_Expr_hasMVar(x_142);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
lean_dec(x_141);
x_145 = lean_st_ref_take(x_3, x_143);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_149 = !lean_is_exclusive(x_146);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_146, 1);
lean_dec(x_150);
x_151 = !lean_is_exclusive(x_147);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_152 = lean_ctor_get(x_147, 0);
lean_inc(x_142);
x_153 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_152, x_131, x_142);
lean_ctor_set(x_147, 0, x_153);
x_154 = lean_st_ref_set(x_3, x_146, x_148);
lean_dec(x_3);
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_154, 0);
lean_dec(x_156);
lean_ctor_set(x_154, 0, x_142);
return x_154;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_142);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_159 = lean_ctor_get(x_147, 0);
x_160 = lean_ctor_get(x_147, 1);
x_161 = lean_ctor_get(x_147, 2);
x_162 = lean_ctor_get(x_147, 3);
x_163 = lean_ctor_get(x_147, 4);
x_164 = lean_ctor_get(x_147, 5);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_147);
lean_inc(x_142);
x_165 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_159, x_131, x_142);
x_166 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_160);
lean_ctor_set(x_166, 2, x_161);
lean_ctor_set(x_166, 3, x_162);
lean_ctor_set(x_166, 4, x_163);
lean_ctor_set(x_166, 5, x_164);
lean_ctor_set(x_146, 1, x_166);
x_167 = lean_st_ref_set(x_3, x_146, x_148);
lean_dec(x_3);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_142);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_171 = lean_ctor_get(x_146, 0);
x_172 = lean_ctor_get(x_146, 2);
x_173 = lean_ctor_get(x_146, 3);
x_174 = lean_ctor_get(x_146, 4);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_146);
x_175 = lean_ctor_get(x_147, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_147, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_147, 2);
lean_inc(x_177);
x_178 = lean_ctor_get(x_147, 3);
lean_inc(x_178);
x_179 = lean_ctor_get(x_147, 4);
lean_inc(x_179);
x_180 = lean_ctor_get(x_147, 5);
lean_inc(x_180);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 lean_ctor_release(x_147, 2);
 lean_ctor_release(x_147, 3);
 lean_ctor_release(x_147, 4);
 lean_ctor_release(x_147, 5);
 x_181 = x_147;
} else {
 lean_dec_ref(x_147);
 x_181 = lean_box(0);
}
lean_inc(x_142);
x_182 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_175, x_131, x_142);
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(0, 6, 0);
} else {
 x_183 = x_181;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_176);
lean_ctor_set(x_183, 2, x_177);
lean_ctor_set(x_183, 3, x_178);
lean_ctor_set(x_183, 4, x_179);
lean_ctor_set(x_183, 5, x_180);
x_184 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_184, 0, x_171);
lean_ctor_set(x_184, 1, x_183);
lean_ctor_set(x_184, 2, x_172);
lean_ctor_set(x_184, 3, x_173);
lean_ctor_set(x_184, 4, x_174);
x_185 = lean_st_ref_set(x_3, x_184, x_148);
lean_dec(x_3);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_187 = x_185;
} else {
 lean_dec_ref(x_185);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_142);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
else
{
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_131);
lean_dec(x_3);
return x_141;
}
}
else
{
lean_dec(x_131);
lean_dec(x_3);
return x_141;
}
}
else
{
lean_object* x_189; 
lean_dec(x_131);
lean_dec(x_128);
lean_dec(x_122);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_189 = lean_ctor_get(x_140, 0);
lean_inc(x_189);
lean_dec(x_140);
lean_ctor_set(x_133, 0, x_189);
return x_133;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_133, 1);
lean_inc(x_190);
lean_dec(x_133);
x_191 = lean_ctor_get(x_135, 0);
lean_inc(x_191);
lean_dec(x_135);
lean_inc(x_131);
x_192 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0___redArg(x_191, x_131);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; 
lean_inc(x_3);
x_193 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_122, x_128, x_2, x_3, x_4, x_5, x_190);
lean_dec(x_128);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
x_196 = l_Lean_Expr_hasMVar(x_194);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_193);
x_197 = lean_st_ref_take(x_3, x_195);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_197, 1);
lean_inc(x_200);
lean_dec(x_197);
x_201 = lean_ctor_get(x_198, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_198, 2);
lean_inc(x_202);
x_203 = lean_ctor_get(x_198, 3);
lean_inc(x_203);
x_204 = lean_ctor_get(x_198, 4);
lean_inc(x_204);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 lean_ctor_release(x_198, 4);
 x_205 = x_198;
} else {
 lean_dec_ref(x_198);
 x_205 = lean_box(0);
}
x_206 = lean_ctor_get(x_199, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_199, 1);
lean_inc(x_207);
x_208 = lean_ctor_get(x_199, 2);
lean_inc(x_208);
x_209 = lean_ctor_get(x_199, 3);
lean_inc(x_209);
x_210 = lean_ctor_get(x_199, 4);
lean_inc(x_210);
x_211 = lean_ctor_get(x_199, 5);
lean_inc(x_211);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 lean_ctor_release(x_199, 4);
 lean_ctor_release(x_199, 5);
 x_212 = x_199;
} else {
 lean_dec_ref(x_199);
 x_212 = lean_box(0);
}
lean_inc(x_194);
x_213 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_206, x_131, x_194);
if (lean_is_scalar(x_212)) {
 x_214 = lean_alloc_ctor(0, 6, 0);
} else {
 x_214 = x_212;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_207);
lean_ctor_set(x_214, 2, x_208);
lean_ctor_set(x_214, 3, x_209);
lean_ctor_set(x_214, 4, x_210);
lean_ctor_set(x_214, 5, x_211);
if (lean_is_scalar(x_205)) {
 x_215 = lean_alloc_ctor(0, 5, 0);
} else {
 x_215 = x_205;
}
lean_ctor_set(x_215, 0, x_201);
lean_ctor_set(x_215, 1, x_214);
lean_ctor_set(x_215, 2, x_202);
lean_ctor_set(x_215, 3, x_203);
lean_ctor_set(x_215, 4, x_204);
x_216 = lean_st_ref_set(x_3, x_215, x_200);
lean_dec(x_3);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_218 = x_216;
} else {
 lean_dec_ref(x_216);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_194);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
else
{
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_131);
lean_dec(x_3);
return x_193;
}
}
else
{
lean_dec(x_131);
lean_dec(x_3);
return x_193;
}
}
else
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_131);
lean_dec(x_128);
lean_dec(x_122);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_220 = lean_ctor_get(x_192, 0);
lean_inc(x_220);
lean_dec(x_192);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_190);
return x_221;
}
}
}
else
{
lean_object* x_222; 
lean_dec(x_1);
x_222 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_122, x_128, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_128);
return x_222;
}
}
case 7:
{
uint8_t x_223; 
x_223 = l_Lean_Expr_hasMVar(x_1);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
lean_inc(x_1);
x_224 = l_Lean_Meta_mkExprConfigCacheKey___redArg(x_1, x_2, x_6);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = lean_st_ref_get(x_3, x_226);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
lean_dec(x_228);
x_230 = !lean_is_exclusive(x_227);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_231 = lean_ctor_get(x_227, 1);
x_232 = lean_ctor_get(x_227, 0);
lean_dec(x_232);
x_233 = lean_ctor_get(x_229, 0);
lean_inc(x_233);
lean_dec(x_229);
lean_inc(x_225);
x_234 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0___redArg(x_233, x_225);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; 
lean_free_object(x_227);
lean_inc(x_3);
x_235 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(x_1, x_2, x_3, x_4, x_5, x_231);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
x_238 = l_Lean_Expr_hasMVar(x_236);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
lean_dec(x_235);
x_239 = lean_st_ref_take(x_3, x_237);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_239, 1);
lean_inc(x_242);
lean_dec(x_239);
x_243 = !lean_is_exclusive(x_240);
if (x_243 == 0)
{
lean_object* x_244; uint8_t x_245; 
x_244 = lean_ctor_get(x_240, 1);
lean_dec(x_244);
x_245 = !lean_is_exclusive(x_241);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_246 = lean_ctor_get(x_241, 0);
lean_inc(x_236);
x_247 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_246, x_225, x_236);
lean_ctor_set(x_241, 0, x_247);
x_248 = lean_st_ref_set(x_3, x_240, x_242);
lean_dec(x_3);
x_249 = !lean_is_exclusive(x_248);
if (x_249 == 0)
{
lean_object* x_250; 
x_250 = lean_ctor_get(x_248, 0);
lean_dec(x_250);
lean_ctor_set(x_248, 0, x_236);
return x_248;
}
else
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_248, 1);
lean_inc(x_251);
lean_dec(x_248);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_236);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_253 = lean_ctor_get(x_241, 0);
x_254 = lean_ctor_get(x_241, 1);
x_255 = lean_ctor_get(x_241, 2);
x_256 = lean_ctor_get(x_241, 3);
x_257 = lean_ctor_get(x_241, 4);
x_258 = lean_ctor_get(x_241, 5);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_241);
lean_inc(x_236);
x_259 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_253, x_225, x_236);
x_260 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_254);
lean_ctor_set(x_260, 2, x_255);
lean_ctor_set(x_260, 3, x_256);
lean_ctor_set(x_260, 4, x_257);
lean_ctor_set(x_260, 5, x_258);
lean_ctor_set(x_240, 1, x_260);
x_261 = lean_st_ref_set(x_3, x_240, x_242);
lean_dec(x_3);
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_263 = x_261;
} else {
 lean_dec_ref(x_261);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_236);
lean_ctor_set(x_264, 1, x_262);
return x_264;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_265 = lean_ctor_get(x_240, 0);
x_266 = lean_ctor_get(x_240, 2);
x_267 = lean_ctor_get(x_240, 3);
x_268 = lean_ctor_get(x_240, 4);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_240);
x_269 = lean_ctor_get(x_241, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_241, 1);
lean_inc(x_270);
x_271 = lean_ctor_get(x_241, 2);
lean_inc(x_271);
x_272 = lean_ctor_get(x_241, 3);
lean_inc(x_272);
x_273 = lean_ctor_get(x_241, 4);
lean_inc(x_273);
x_274 = lean_ctor_get(x_241, 5);
lean_inc(x_274);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 lean_ctor_release(x_241, 2);
 lean_ctor_release(x_241, 3);
 lean_ctor_release(x_241, 4);
 lean_ctor_release(x_241, 5);
 x_275 = x_241;
} else {
 lean_dec_ref(x_241);
 x_275 = lean_box(0);
}
lean_inc(x_236);
x_276 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_269, x_225, x_236);
if (lean_is_scalar(x_275)) {
 x_277 = lean_alloc_ctor(0, 6, 0);
} else {
 x_277 = x_275;
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_270);
lean_ctor_set(x_277, 2, x_271);
lean_ctor_set(x_277, 3, x_272);
lean_ctor_set(x_277, 4, x_273);
lean_ctor_set(x_277, 5, x_274);
x_278 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_278, 0, x_265);
lean_ctor_set(x_278, 1, x_277);
lean_ctor_set(x_278, 2, x_266);
lean_ctor_set(x_278, 3, x_267);
lean_ctor_set(x_278, 4, x_268);
x_279 = lean_st_ref_set(x_3, x_278, x_242);
lean_dec(x_3);
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_281 = x_279;
} else {
 lean_dec_ref(x_279);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_236);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
else
{
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_225);
lean_dec(x_3);
return x_235;
}
}
else
{
lean_dec(x_225);
lean_dec(x_3);
return x_235;
}
}
else
{
lean_object* x_283; 
lean_dec(x_225);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_283 = lean_ctor_get(x_234, 0);
lean_inc(x_283);
lean_dec(x_234);
lean_ctor_set(x_227, 0, x_283);
return x_227;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_227, 1);
lean_inc(x_284);
lean_dec(x_227);
x_285 = lean_ctor_get(x_229, 0);
lean_inc(x_285);
lean_dec(x_229);
lean_inc(x_225);
x_286 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0___redArg(x_285, x_225);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; 
lean_inc(x_3);
x_287 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(x_1, x_2, x_3, x_4, x_5, x_284);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
x_290 = l_Lean_Expr_hasMVar(x_288);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_287);
x_291 = lean_st_ref_take(x_3, x_289);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
x_294 = lean_ctor_get(x_291, 1);
lean_inc(x_294);
lean_dec(x_291);
x_295 = lean_ctor_get(x_292, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_292, 2);
lean_inc(x_296);
x_297 = lean_ctor_get(x_292, 3);
lean_inc(x_297);
x_298 = lean_ctor_get(x_292, 4);
lean_inc(x_298);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 lean_ctor_release(x_292, 2);
 lean_ctor_release(x_292, 3);
 lean_ctor_release(x_292, 4);
 x_299 = x_292;
} else {
 lean_dec_ref(x_292);
 x_299 = lean_box(0);
}
x_300 = lean_ctor_get(x_293, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_293, 1);
lean_inc(x_301);
x_302 = lean_ctor_get(x_293, 2);
lean_inc(x_302);
x_303 = lean_ctor_get(x_293, 3);
lean_inc(x_303);
x_304 = lean_ctor_get(x_293, 4);
lean_inc(x_304);
x_305 = lean_ctor_get(x_293, 5);
lean_inc(x_305);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 lean_ctor_release(x_293, 2);
 lean_ctor_release(x_293, 3);
 lean_ctor_release(x_293, 4);
 lean_ctor_release(x_293, 5);
 x_306 = x_293;
} else {
 lean_dec_ref(x_293);
 x_306 = lean_box(0);
}
lean_inc(x_288);
x_307 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_300, x_225, x_288);
if (lean_is_scalar(x_306)) {
 x_308 = lean_alloc_ctor(0, 6, 0);
} else {
 x_308 = x_306;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_301);
lean_ctor_set(x_308, 2, x_302);
lean_ctor_set(x_308, 3, x_303);
lean_ctor_set(x_308, 4, x_304);
lean_ctor_set(x_308, 5, x_305);
if (lean_is_scalar(x_299)) {
 x_309 = lean_alloc_ctor(0, 5, 0);
} else {
 x_309 = x_299;
}
lean_ctor_set(x_309, 0, x_295);
lean_ctor_set(x_309, 1, x_308);
lean_ctor_set(x_309, 2, x_296);
lean_ctor_set(x_309, 3, x_297);
lean_ctor_set(x_309, 4, x_298);
x_310 = lean_st_ref_set(x_3, x_309, x_294);
lean_dec(x_3);
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_312 = x_310;
} else {
 lean_dec_ref(x_310);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_288);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
else
{
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_225);
lean_dec(x_3);
return x_287;
}
}
else
{
lean_dec(x_225);
lean_dec(x_3);
return x_287;
}
}
else
{
lean_object* x_314; lean_object* x_315; 
lean_dec(x_225);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_314 = lean_ctor_get(x_286, 0);
lean_inc(x_314);
lean_dec(x_286);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_284);
return x_315;
}
}
}
else
{
lean_object* x_316; 
x_316 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(x_1, x_2, x_3, x_4, x_5, x_6);
return x_316;
}
}
case 9:
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_317 = lean_ctor_get(x_1, 0);
lean_inc(x_317);
lean_dec(x_1);
x_318 = l_Lean_Literal_type(x_317);
lean_dec(x_317);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_6);
return x_319;
}
case 10:
{
lean_object* x_320; 
x_320 = lean_ctor_get(x_1, 1);
lean_inc(x_320);
lean_dec(x_1);
x_1 = x_320;
goto _start;
}
case 11:
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; 
x_322 = lean_ctor_get(x_1, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_1, 1);
lean_inc(x_323);
x_324 = lean_ctor_get(x_1, 2);
lean_inc(x_324);
x_325 = l_Lean_Expr_hasMVar(x_1);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; 
x_326 = l_Lean_Meta_mkExprConfigCacheKey___redArg(x_1, x_2, x_6);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec(x_326);
x_329 = lean_st_ref_get(x_3, x_328);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_330, 1);
lean_inc(x_331);
lean_dec(x_330);
x_332 = !lean_is_exclusive(x_329);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_333 = lean_ctor_get(x_329, 1);
x_334 = lean_ctor_get(x_329, 0);
lean_dec(x_334);
x_335 = lean_ctor_get(x_331, 0);
lean_inc(x_335);
lean_dec(x_331);
lean_inc(x_327);
x_336 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0___redArg(x_335, x_327);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; 
lean_free_object(x_329);
lean_inc(x_3);
x_337 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(x_322, x_323, x_324, x_2, x_3, x_4, x_5, x_333);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
x_340 = l_Lean_Expr_hasMVar(x_338);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; 
lean_dec(x_337);
x_341 = lean_st_ref_take(x_3, x_339);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_342, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_341, 1);
lean_inc(x_344);
lean_dec(x_341);
x_345 = !lean_is_exclusive(x_342);
if (x_345 == 0)
{
lean_object* x_346; uint8_t x_347; 
x_346 = lean_ctor_get(x_342, 1);
lean_dec(x_346);
x_347 = !lean_is_exclusive(x_343);
if (x_347 == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; 
x_348 = lean_ctor_get(x_343, 0);
lean_inc(x_338);
x_349 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_348, x_327, x_338);
lean_ctor_set(x_343, 0, x_349);
x_350 = lean_st_ref_set(x_3, x_342, x_344);
lean_dec(x_3);
x_351 = !lean_is_exclusive(x_350);
if (x_351 == 0)
{
lean_object* x_352; 
x_352 = lean_ctor_get(x_350, 0);
lean_dec(x_352);
lean_ctor_set(x_350, 0, x_338);
return x_350;
}
else
{
lean_object* x_353; lean_object* x_354; 
x_353 = lean_ctor_get(x_350, 1);
lean_inc(x_353);
lean_dec(x_350);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_338);
lean_ctor_set(x_354, 1, x_353);
return x_354;
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_355 = lean_ctor_get(x_343, 0);
x_356 = lean_ctor_get(x_343, 1);
x_357 = lean_ctor_get(x_343, 2);
x_358 = lean_ctor_get(x_343, 3);
x_359 = lean_ctor_get(x_343, 4);
x_360 = lean_ctor_get(x_343, 5);
lean_inc(x_360);
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_343);
lean_inc(x_338);
x_361 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_355, x_327, x_338);
x_362 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_356);
lean_ctor_set(x_362, 2, x_357);
lean_ctor_set(x_362, 3, x_358);
lean_ctor_set(x_362, 4, x_359);
lean_ctor_set(x_362, 5, x_360);
lean_ctor_set(x_342, 1, x_362);
x_363 = lean_st_ref_set(x_3, x_342, x_344);
lean_dec(x_3);
x_364 = lean_ctor_get(x_363, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_365 = x_363;
} else {
 lean_dec_ref(x_363);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_338);
lean_ctor_set(x_366, 1, x_364);
return x_366;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_367 = lean_ctor_get(x_342, 0);
x_368 = lean_ctor_get(x_342, 2);
x_369 = lean_ctor_get(x_342, 3);
x_370 = lean_ctor_get(x_342, 4);
lean_inc(x_370);
lean_inc(x_369);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_342);
x_371 = lean_ctor_get(x_343, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_343, 1);
lean_inc(x_372);
x_373 = lean_ctor_get(x_343, 2);
lean_inc(x_373);
x_374 = lean_ctor_get(x_343, 3);
lean_inc(x_374);
x_375 = lean_ctor_get(x_343, 4);
lean_inc(x_375);
x_376 = lean_ctor_get(x_343, 5);
lean_inc(x_376);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 lean_ctor_release(x_343, 2);
 lean_ctor_release(x_343, 3);
 lean_ctor_release(x_343, 4);
 lean_ctor_release(x_343, 5);
 x_377 = x_343;
} else {
 lean_dec_ref(x_343);
 x_377 = lean_box(0);
}
lean_inc(x_338);
x_378 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_371, x_327, x_338);
if (lean_is_scalar(x_377)) {
 x_379 = lean_alloc_ctor(0, 6, 0);
} else {
 x_379 = x_377;
}
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_372);
lean_ctor_set(x_379, 2, x_373);
lean_ctor_set(x_379, 3, x_374);
lean_ctor_set(x_379, 4, x_375);
lean_ctor_set(x_379, 5, x_376);
x_380 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_380, 0, x_367);
lean_ctor_set(x_380, 1, x_379);
lean_ctor_set(x_380, 2, x_368);
lean_ctor_set(x_380, 3, x_369);
lean_ctor_set(x_380, 4, x_370);
x_381 = lean_st_ref_set(x_3, x_380, x_344);
lean_dec(x_3);
x_382 = lean_ctor_get(x_381, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_383 = x_381;
} else {
 lean_dec_ref(x_381);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_338);
lean_ctor_set(x_384, 1, x_382);
return x_384;
}
}
else
{
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_327);
lean_dec(x_3);
return x_337;
}
}
else
{
lean_dec(x_327);
lean_dec(x_3);
return x_337;
}
}
else
{
lean_object* x_385; 
lean_dec(x_327);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_385 = lean_ctor_get(x_336, 0);
lean_inc(x_385);
lean_dec(x_336);
lean_ctor_set(x_329, 0, x_385);
return x_329;
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_329, 1);
lean_inc(x_386);
lean_dec(x_329);
x_387 = lean_ctor_get(x_331, 0);
lean_inc(x_387);
lean_dec(x_331);
lean_inc(x_327);
x_388 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0___redArg(x_387, x_327);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; 
lean_inc(x_3);
x_389 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(x_322, x_323, x_324, x_2, x_3, x_4, x_5, x_386);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; uint8_t x_392; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
x_392 = l_Lean_Expr_hasMVar(x_390);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
lean_dec(x_389);
x_393 = lean_st_ref_take(x_3, x_391);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_394, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_393, 1);
lean_inc(x_396);
lean_dec(x_393);
x_397 = lean_ctor_get(x_394, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_394, 2);
lean_inc(x_398);
x_399 = lean_ctor_get(x_394, 3);
lean_inc(x_399);
x_400 = lean_ctor_get(x_394, 4);
lean_inc(x_400);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 lean_ctor_release(x_394, 2);
 lean_ctor_release(x_394, 3);
 lean_ctor_release(x_394, 4);
 x_401 = x_394;
} else {
 lean_dec_ref(x_394);
 x_401 = lean_box(0);
}
x_402 = lean_ctor_get(x_395, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_395, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_395, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_395, 3);
lean_inc(x_405);
x_406 = lean_ctor_get(x_395, 4);
lean_inc(x_406);
x_407 = lean_ctor_get(x_395, 5);
lean_inc(x_407);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 lean_ctor_release(x_395, 2);
 lean_ctor_release(x_395, 3);
 lean_ctor_release(x_395, 4);
 lean_ctor_release(x_395, 5);
 x_408 = x_395;
} else {
 lean_dec_ref(x_395);
 x_408 = lean_box(0);
}
lean_inc(x_390);
x_409 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_402, x_327, x_390);
if (lean_is_scalar(x_408)) {
 x_410 = lean_alloc_ctor(0, 6, 0);
} else {
 x_410 = x_408;
}
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_403);
lean_ctor_set(x_410, 2, x_404);
lean_ctor_set(x_410, 3, x_405);
lean_ctor_set(x_410, 4, x_406);
lean_ctor_set(x_410, 5, x_407);
if (lean_is_scalar(x_401)) {
 x_411 = lean_alloc_ctor(0, 5, 0);
} else {
 x_411 = x_401;
}
lean_ctor_set(x_411, 0, x_397);
lean_ctor_set(x_411, 1, x_410);
lean_ctor_set(x_411, 2, x_398);
lean_ctor_set(x_411, 3, x_399);
lean_ctor_set(x_411, 4, x_400);
x_412 = lean_st_ref_set(x_3, x_411, x_396);
lean_dec(x_3);
x_413 = lean_ctor_get(x_412, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 x_414 = x_412;
} else {
 lean_dec_ref(x_412);
 x_414 = lean_box(0);
}
if (lean_is_scalar(x_414)) {
 x_415 = lean_alloc_ctor(0, 2, 0);
} else {
 x_415 = x_414;
}
lean_ctor_set(x_415, 0, x_390);
lean_ctor_set(x_415, 1, x_413);
return x_415;
}
else
{
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_327);
lean_dec(x_3);
return x_389;
}
}
else
{
lean_dec(x_327);
lean_dec(x_3);
return x_389;
}
}
else
{
lean_object* x_416; lean_object* x_417; 
lean_dec(x_327);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_416 = lean_ctor_get(x_388, 0);
lean_inc(x_416);
lean_dec(x_388);
x_417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_386);
return x_417;
}
}
}
else
{
lean_object* x_418; 
lean_dec(x_1);
x_418 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(x_322, x_323, x_324, x_2, x_3, x_4, x_5, x_6);
return x_418;
}
}
default: 
{
uint8_t x_419; 
x_419 = l_Lean_Expr_hasMVar(x_1);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; 
lean_inc(x_1);
x_420 = l_Lean_Meta_mkExprConfigCacheKey___redArg(x_1, x_2, x_6);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_st_ref_get(x_3, x_422);
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_424, 1);
lean_inc(x_425);
lean_dec(x_424);
x_426 = !lean_is_exclusive(x_423);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_427 = lean_ctor_get(x_423, 1);
x_428 = lean_ctor_get(x_423, 0);
lean_dec(x_428);
x_429 = lean_ctor_get(x_425, 0);
lean_inc(x_429);
lean_dec(x_425);
lean_inc(x_421);
x_430 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0___redArg(x_429, x_421);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; 
lean_free_object(x_423);
lean_inc(x_3);
x_431 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(x_1, x_2, x_3, x_4, x_5, x_427);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; uint8_t x_434; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
x_434 = l_Lean_Expr_hasMVar(x_432);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; 
lean_dec(x_431);
x_435 = lean_st_ref_take(x_3, x_433);
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_436, 1);
lean_inc(x_437);
x_438 = lean_ctor_get(x_435, 1);
lean_inc(x_438);
lean_dec(x_435);
x_439 = !lean_is_exclusive(x_436);
if (x_439 == 0)
{
lean_object* x_440; uint8_t x_441; 
x_440 = lean_ctor_get(x_436, 1);
lean_dec(x_440);
x_441 = !lean_is_exclusive(x_437);
if (x_441 == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; 
x_442 = lean_ctor_get(x_437, 0);
lean_inc(x_432);
x_443 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_442, x_421, x_432);
lean_ctor_set(x_437, 0, x_443);
x_444 = lean_st_ref_set(x_3, x_436, x_438);
lean_dec(x_3);
x_445 = !lean_is_exclusive(x_444);
if (x_445 == 0)
{
lean_object* x_446; 
x_446 = lean_ctor_get(x_444, 0);
lean_dec(x_446);
lean_ctor_set(x_444, 0, x_432);
return x_444;
}
else
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_ctor_get(x_444, 1);
lean_inc(x_447);
lean_dec(x_444);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_432);
lean_ctor_set(x_448, 1, x_447);
return x_448;
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_449 = lean_ctor_get(x_437, 0);
x_450 = lean_ctor_get(x_437, 1);
x_451 = lean_ctor_get(x_437, 2);
x_452 = lean_ctor_get(x_437, 3);
x_453 = lean_ctor_get(x_437, 4);
x_454 = lean_ctor_get(x_437, 5);
lean_inc(x_454);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_451);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_437);
lean_inc(x_432);
x_455 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_449, x_421, x_432);
x_456 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_450);
lean_ctor_set(x_456, 2, x_451);
lean_ctor_set(x_456, 3, x_452);
lean_ctor_set(x_456, 4, x_453);
lean_ctor_set(x_456, 5, x_454);
lean_ctor_set(x_436, 1, x_456);
x_457 = lean_st_ref_set(x_3, x_436, x_438);
lean_dec(x_3);
x_458 = lean_ctor_get(x_457, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 lean_ctor_release(x_457, 1);
 x_459 = x_457;
} else {
 lean_dec_ref(x_457);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(0, 2, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_432);
lean_ctor_set(x_460, 1, x_458);
return x_460;
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_461 = lean_ctor_get(x_436, 0);
x_462 = lean_ctor_get(x_436, 2);
x_463 = lean_ctor_get(x_436, 3);
x_464 = lean_ctor_get(x_436, 4);
lean_inc(x_464);
lean_inc(x_463);
lean_inc(x_462);
lean_inc(x_461);
lean_dec(x_436);
x_465 = lean_ctor_get(x_437, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_437, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_437, 2);
lean_inc(x_467);
x_468 = lean_ctor_get(x_437, 3);
lean_inc(x_468);
x_469 = lean_ctor_get(x_437, 4);
lean_inc(x_469);
x_470 = lean_ctor_get(x_437, 5);
lean_inc(x_470);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 lean_ctor_release(x_437, 2);
 lean_ctor_release(x_437, 3);
 lean_ctor_release(x_437, 4);
 lean_ctor_release(x_437, 5);
 x_471 = x_437;
} else {
 lean_dec_ref(x_437);
 x_471 = lean_box(0);
}
lean_inc(x_432);
x_472 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_465, x_421, x_432);
if (lean_is_scalar(x_471)) {
 x_473 = lean_alloc_ctor(0, 6, 0);
} else {
 x_473 = x_471;
}
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_466);
lean_ctor_set(x_473, 2, x_467);
lean_ctor_set(x_473, 3, x_468);
lean_ctor_set(x_473, 4, x_469);
lean_ctor_set(x_473, 5, x_470);
x_474 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_474, 0, x_461);
lean_ctor_set(x_474, 1, x_473);
lean_ctor_set(x_474, 2, x_462);
lean_ctor_set(x_474, 3, x_463);
lean_ctor_set(x_474, 4, x_464);
x_475 = lean_st_ref_set(x_3, x_474, x_438);
lean_dec(x_3);
x_476 = lean_ctor_get(x_475, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 x_477 = x_475;
} else {
 lean_dec_ref(x_475);
 x_477 = lean_box(0);
}
if (lean_is_scalar(x_477)) {
 x_478 = lean_alloc_ctor(0, 2, 0);
} else {
 x_478 = x_477;
}
lean_ctor_set(x_478, 0, x_432);
lean_ctor_set(x_478, 1, x_476);
return x_478;
}
}
else
{
lean_dec(x_433);
lean_dec(x_432);
lean_dec(x_421);
lean_dec(x_3);
return x_431;
}
}
else
{
lean_dec(x_421);
lean_dec(x_3);
return x_431;
}
}
else
{
lean_object* x_479; 
lean_dec(x_421);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_479 = lean_ctor_get(x_430, 0);
lean_inc(x_479);
lean_dec(x_430);
lean_ctor_set(x_423, 0, x_479);
return x_423;
}
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_480 = lean_ctor_get(x_423, 1);
lean_inc(x_480);
lean_dec(x_423);
x_481 = lean_ctor_get(x_425, 0);
lean_inc(x_481);
lean_dec(x_425);
lean_inc(x_421);
x_482 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_inferTypeImp_infer_spec__0___redArg(x_481, x_421);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; 
lean_inc(x_3);
x_483 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(x_1, x_2, x_3, x_4, x_5, x_480);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; uint8_t x_486; 
x_484 = lean_ctor_get(x_483, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_483, 1);
lean_inc(x_485);
x_486 = l_Lean_Expr_hasMVar(x_484);
if (x_486 == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
lean_dec(x_483);
x_487 = lean_st_ref_take(x_3, x_485);
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_488, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_487, 1);
lean_inc(x_490);
lean_dec(x_487);
x_491 = lean_ctor_get(x_488, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_488, 2);
lean_inc(x_492);
x_493 = lean_ctor_get(x_488, 3);
lean_inc(x_493);
x_494 = lean_ctor_get(x_488, 4);
lean_inc(x_494);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 lean_ctor_release(x_488, 2);
 lean_ctor_release(x_488, 3);
 lean_ctor_release(x_488, 4);
 x_495 = x_488;
} else {
 lean_dec_ref(x_488);
 x_495 = lean_box(0);
}
x_496 = lean_ctor_get(x_489, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_489, 1);
lean_inc(x_497);
x_498 = lean_ctor_get(x_489, 2);
lean_inc(x_498);
x_499 = lean_ctor_get(x_489, 3);
lean_inc(x_499);
x_500 = lean_ctor_get(x_489, 4);
lean_inc(x_500);
x_501 = lean_ctor_get(x_489, 5);
lean_inc(x_501);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 lean_ctor_release(x_489, 1);
 lean_ctor_release(x_489, 2);
 lean_ctor_release(x_489, 3);
 lean_ctor_release(x_489, 4);
 lean_ctor_release(x_489, 5);
 x_502 = x_489;
} else {
 lean_dec_ref(x_489);
 x_502 = lean_box(0);
}
lean_inc(x_484);
x_503 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_inferTypeImp_infer_spec__1___redArg(x_496, x_421, x_484);
if (lean_is_scalar(x_502)) {
 x_504 = lean_alloc_ctor(0, 6, 0);
} else {
 x_504 = x_502;
}
lean_ctor_set(x_504, 0, x_503);
lean_ctor_set(x_504, 1, x_497);
lean_ctor_set(x_504, 2, x_498);
lean_ctor_set(x_504, 3, x_499);
lean_ctor_set(x_504, 4, x_500);
lean_ctor_set(x_504, 5, x_501);
if (lean_is_scalar(x_495)) {
 x_505 = lean_alloc_ctor(0, 5, 0);
} else {
 x_505 = x_495;
}
lean_ctor_set(x_505, 0, x_491);
lean_ctor_set(x_505, 1, x_504);
lean_ctor_set(x_505, 2, x_492);
lean_ctor_set(x_505, 3, x_493);
lean_ctor_set(x_505, 4, x_494);
x_506 = lean_st_ref_set(x_3, x_505, x_490);
lean_dec(x_3);
x_507 = lean_ctor_get(x_506, 1);
lean_inc(x_507);
if (lean_is_exclusive(x_506)) {
 lean_ctor_release(x_506, 0);
 lean_ctor_release(x_506, 1);
 x_508 = x_506;
} else {
 lean_dec_ref(x_506);
 x_508 = lean_box(0);
}
if (lean_is_scalar(x_508)) {
 x_509 = lean_alloc_ctor(0, 2, 0);
} else {
 x_509 = x_508;
}
lean_ctor_set(x_509, 0, x_484);
lean_ctor_set(x_509, 1, x_507);
return x_509;
}
else
{
lean_dec(x_485);
lean_dec(x_484);
lean_dec(x_421);
lean_dec(x_3);
return x_483;
}
}
else
{
lean_dec(x_421);
lean_dec(x_3);
return x_483;
}
}
else
{
lean_object* x_510; lean_object* x_511; 
lean_dec(x_421);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_510 = lean_ctor_get(x_482, 0);
lean_inc(x_510);
lean_dec(x_482);
x_511 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_511, 0, x_510);
lean_ctor_set(x_511, 1, x_480);
return x_511;
}
}
}
else
{
lean_object* x_512; 
x_512 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(x_1, x_2, x_3, x_4, x_5, x_6);
return x_512;
}
}
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information", 157, 157);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__5;
x_2 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__2;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__6;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg(x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 2);
x_11 = lean_ctor_get(x_4, 3);
x_12 = lean_ctor_get(x_4, 4);
x_13 = lean_ctor_get(x_4, 5);
x_14 = lean_ctor_get(x_4, 6);
x_15 = lean_ctor_get(x_4, 7);
x_16 = lean_ctor_get(x_4, 8);
x_17 = lean_ctor_get(x_4, 9);
x_18 = lean_ctor_get(x_4, 10);
x_19 = lean_ctor_get(x_4, 11);
x_20 = lean_ctor_get(x_4, 12);
x_21 = lean_nat_dec_eq(x_11, x_12);
if (x_21 == 0)
{
lean_object* x_22; uint64_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; uint8_t x_90; lean_object* x_115; uint8_t x_116; uint8_t x_117; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_24 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 4);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 5);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 6);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_33 = x_2;
} else {
 lean_dec_ref(x_2);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get_uint8(x_22, 0);
x_35 = lean_ctor_get_uint8(x_22, 1);
x_36 = lean_ctor_get_uint8(x_22, 2);
x_37 = lean_ctor_get_uint8(x_22, 3);
x_38 = lean_ctor_get_uint8(x_22, 4);
x_39 = lean_ctor_get_uint8(x_22, 5);
x_40 = lean_ctor_get_uint8(x_22, 6);
x_41 = lean_ctor_get_uint8(x_22, 7);
x_42 = lean_ctor_get_uint8(x_22, 8);
x_43 = lean_ctor_get_uint8(x_22, 9);
x_44 = lean_ctor_get_uint8(x_22, 10);
x_45 = lean_ctor_get_uint8(x_22, 11);
x_46 = lean_ctor_get_uint8(x_22, 12);
x_47 = lean_ctor_get_uint8(x_22, 13);
x_48 = lean_ctor_get_uint8(x_22, 14);
x_49 = lean_ctor_get_uint8(x_22, 15);
x_50 = lean_ctor_get_uint8(x_22, 16);
x_51 = lean_ctor_get_uint8(x_22, 17);
if (lean_is_exclusive(x_22)) {
 x_52 = x_22;
} else {
 lean_dec_ref(x_22);
 x_52 = lean_box(0);
}
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_11, x_53);
lean_dec(x_11);
lean_ctor_set(x_4, 3, x_54);
x_115 = lean_box(1);
x_116 = lean_unbox(x_115);
x_117 = l_Lean_Meta_TransparencyMode_lt(x_43, x_116);
if (x_117 == 0)
{
x_90 = x_43;
goto block_114;
}
else
{
uint8_t x_118; 
x_118 = lean_unbox(x_115);
x_90 = x_118;
goto block_114;
}
block_89:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; 
x_78 = lean_box(1);
x_79 = lean_box(2);
if (lean_is_scalar(x_52)) {
 x_80 = lean_alloc_ctor(0, 0, 18);
} else {
 x_80 = x_52;
}
lean_ctor_set_uint8(x_80, 0, x_55);
lean_ctor_set_uint8(x_80, 1, x_73);
lean_ctor_set_uint8(x_80, 2, x_72);
lean_ctor_set_uint8(x_80, 3, x_74);
lean_ctor_set_uint8(x_80, 4, x_56);
lean_ctor_set_uint8(x_80, 5, x_62);
lean_ctor_set_uint8(x_80, 6, x_64);
lean_ctor_set_uint8(x_80, 7, x_75);
lean_ctor_set_uint8(x_80, 8, x_65);
lean_ctor_set_uint8(x_80, 9, x_71);
lean_ctor_set_uint8(x_80, 10, x_77);
lean_ctor_set_uint8(x_80, 11, x_67);
x_81 = lean_unbox(x_78);
lean_ctor_set_uint8(x_80, 12, x_81);
x_82 = lean_unbox(x_78);
lean_ctor_set_uint8(x_80, 13, x_82);
x_83 = lean_unbox(x_79);
lean_ctor_set_uint8(x_80, 14, x_83);
x_84 = lean_unbox(x_78);
lean_ctor_set_uint8(x_80, 15, x_84);
x_85 = lean_unbox(x_78);
lean_ctor_set_uint8(x_80, 16, x_85);
lean_ctor_set_uint8(x_80, 17, x_57);
x_86 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_80);
if (lean_is_scalar(x_33)) {
 x_87 = lean_alloc_ctor(0, 7, 11);
} else {
 x_87 = x_33;
}
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_70);
lean_ctor_set(x_87, 2, x_59);
lean_ctor_set(x_87, 3, x_61);
lean_ctor_set(x_87, 4, x_58);
lean_ctor_set(x_87, 5, x_76);
lean_ctor_set(x_87, 6, x_60);
lean_ctor_set_uint64(x_87, sizeof(void*)*7, x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*7 + 8, x_66);
lean_ctor_set_uint8(x_87, sizeof(void*)*7 + 9, x_69);
lean_ctor_set_uint8(x_87, sizeof(void*)*7 + 10, x_68);
x_88 = l_Lean_Meta_inferTypeImp_infer(x_1, x_87, x_3, x_4, x_5, x_63);
return x_88;
}
block_114:
{
lean_object* x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_91 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_91, 0, x_34);
lean_ctor_set_uint8(x_91, 1, x_35);
lean_ctor_set_uint8(x_91, 2, x_36);
lean_ctor_set_uint8(x_91, 3, x_37);
lean_ctor_set_uint8(x_91, 4, x_38);
lean_ctor_set_uint8(x_91, 5, x_39);
lean_ctor_set_uint8(x_91, 6, x_40);
lean_ctor_set_uint8(x_91, 7, x_41);
lean_ctor_set_uint8(x_91, 8, x_42);
lean_ctor_set_uint8(x_91, 9, x_90);
lean_ctor_set_uint8(x_91, 10, x_44);
lean_ctor_set_uint8(x_91, 11, x_45);
lean_ctor_set_uint8(x_91, 12, x_46);
lean_ctor_set_uint8(x_91, 13, x_47);
lean_ctor_set_uint8(x_91, 14, x_48);
lean_ctor_set_uint8(x_91, 15, x_49);
lean_ctor_set_uint8(x_91, 16, x_50);
lean_ctor_set_uint8(x_91, 17, x_51);
x_92 = 2;
x_93 = lean_uint64_shift_right(x_23, x_92);
x_94 = lean_uint64_shift_left(x_93, x_92);
x_95 = l_Lean_Meta_TransparencyMode_toUInt64(x_90);
x_96 = lean_uint64_lor(x_94, x_95);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_97 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_97, 0, x_91);
lean_ctor_set(x_97, 1, x_25);
lean_ctor_set(x_97, 2, x_26);
lean_ctor_set(x_97, 3, x_27);
lean_ctor_set(x_97, 4, x_28);
lean_ctor_set(x_97, 5, x_29);
lean_ctor_set(x_97, 6, x_30);
lean_ctor_set_uint64(x_97, sizeof(void*)*7, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*7 + 8, x_24);
lean_ctor_set_uint8(x_97, sizeof(void*)*7 + 9, x_31);
lean_ctor_set_uint8(x_97, sizeof(void*)*7 + 10, x_32);
x_98 = l_Lean_Meta_getConfig___redArg(x_97, x_6);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get_uint8(x_99, 13);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_99);
lean_dec(x_97);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_55 = x_34;
x_56 = x_38;
x_57 = x_51;
x_58 = x_28;
x_59 = x_26;
x_60 = x_30;
x_61 = x_27;
x_62 = x_39;
x_63 = x_101;
x_64 = x_40;
x_65 = x_42;
x_66 = x_24;
x_67 = x_45;
x_68 = x_32;
x_69 = x_31;
x_70 = x_25;
x_71 = x_90;
x_72 = x_36;
x_73 = x_35;
x_74 = x_37;
x_75 = x_41;
x_76 = x_29;
x_77 = x_44;
goto block_89;
}
else
{
uint8_t x_102; 
x_102 = lean_ctor_get_uint8(x_99, 12);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_99);
lean_dec(x_97);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_dec(x_98);
x_55 = x_34;
x_56 = x_38;
x_57 = x_51;
x_58 = x_28;
x_59 = x_26;
x_60 = x_30;
x_61 = x_27;
x_62 = x_39;
x_63 = x_103;
x_64 = x_40;
x_65 = x_42;
x_66 = x_24;
x_67 = x_45;
x_68 = x_32;
x_69 = x_31;
x_70 = x_25;
x_71 = x_90;
x_72 = x_36;
x_73 = x_35;
x_74 = x_37;
x_75 = x_41;
x_76 = x_29;
x_77 = x_44;
goto block_89;
}
else
{
uint8_t x_104; 
x_104 = lean_ctor_get_uint8(x_99, 15);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_99);
lean_dec(x_97);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_55 = x_34;
x_56 = x_38;
x_57 = x_51;
x_58 = x_28;
x_59 = x_26;
x_60 = x_30;
x_61 = x_27;
x_62 = x_39;
x_63 = x_105;
x_64 = x_40;
x_65 = x_42;
x_66 = x_24;
x_67 = x_45;
x_68 = x_32;
x_69 = x_31;
x_70 = x_25;
x_71 = x_90;
x_72 = x_36;
x_73 = x_35;
x_74 = x_37;
x_75 = x_41;
x_76 = x_29;
x_77 = x_44;
goto block_89;
}
else
{
uint8_t x_106; 
x_106 = lean_ctor_get_uint8(x_99, 16);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_99);
lean_dec(x_97);
x_107 = lean_ctor_get(x_98, 1);
lean_inc(x_107);
lean_dec(x_98);
x_55 = x_34;
x_56 = x_38;
x_57 = x_51;
x_58 = x_28;
x_59 = x_26;
x_60 = x_30;
x_61 = x_27;
x_62 = x_39;
x_63 = x_107;
x_64 = x_40;
x_65 = x_42;
x_66 = x_24;
x_67 = x_45;
x_68 = x_32;
x_69 = x_31;
x_70 = x_25;
x_71 = x_90;
x_72 = x_36;
x_73 = x_35;
x_74 = x_37;
x_75 = x_41;
x_76 = x_29;
x_77 = x_44;
goto block_89;
}
else
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; 
x_108 = lean_ctor_get(x_98, 1);
lean_inc(x_108);
lean_dec(x_98);
x_109 = lean_ctor_get_uint8(x_99, 14);
lean_dec(x_99);
x_110 = lean_box(2);
x_111 = lean_unbox(x_110);
x_112 = l_Lean_Meta_instDecidableEqProjReductionKind(x_109, x_111);
if (x_112 == 0)
{
lean_dec(x_97);
x_55 = x_34;
x_56 = x_38;
x_57 = x_51;
x_58 = x_28;
x_59 = x_26;
x_60 = x_30;
x_61 = x_27;
x_62 = x_39;
x_63 = x_108;
x_64 = x_40;
x_65 = x_42;
x_66 = x_24;
x_67 = x_45;
x_68 = x_32;
x_69 = x_31;
x_70 = x_25;
x_71 = x_90;
x_72 = x_36;
x_73 = x_35;
x_74 = x_37;
x_75 = x_41;
x_76 = x_29;
x_77 = x_44;
goto block_89;
}
else
{
lean_object* x_113; 
lean_dec(x_52);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
x_113 = l_Lean_Meta_inferTypeImp_infer(x_1, x_97, x_3, x_4, x_5, x_108);
return x_113;
}
}
}
}
}
}
}
else
{
lean_object* x_119; 
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg(x_13, x_6);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; uint8_t x_135; 
x_120 = lean_ctor_get(x_4, 0);
x_121 = lean_ctor_get(x_4, 1);
x_122 = lean_ctor_get(x_4, 2);
x_123 = lean_ctor_get(x_4, 3);
x_124 = lean_ctor_get(x_4, 4);
x_125 = lean_ctor_get(x_4, 5);
x_126 = lean_ctor_get(x_4, 6);
x_127 = lean_ctor_get(x_4, 7);
x_128 = lean_ctor_get(x_4, 8);
x_129 = lean_ctor_get(x_4, 9);
x_130 = lean_ctor_get(x_4, 10);
x_131 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_132 = lean_ctor_get(x_4, 11);
x_133 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_134 = lean_ctor_get(x_4, 12);
lean_inc(x_134);
lean_inc(x_132);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_4);
x_135 = lean_nat_dec_eq(x_123, x_124);
if (x_135 == 0)
{
lean_object* x_136; uint64_t x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; uint8_t x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; uint8_t x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; uint8_t x_179; uint8_t x_180; uint8_t x_181; uint8_t x_182; uint8_t x_183; uint8_t x_184; lean_object* x_185; uint8_t x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; lean_object* x_191; uint8_t x_192; uint8_t x_205; lean_object* x_230; uint8_t x_231; uint8_t x_232; 
x_136 = lean_ctor_get(x_2, 0);
lean_inc(x_136);
x_137 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_138 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_139 = lean_ctor_get(x_2, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_2, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_2, 3);
lean_inc(x_141);
x_142 = lean_ctor_get(x_2, 4);
lean_inc(x_142);
x_143 = lean_ctor_get(x_2, 5);
lean_inc(x_143);
x_144 = lean_ctor_get(x_2, 6);
lean_inc(x_144);
x_145 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_146 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_147 = x_2;
} else {
 lean_dec_ref(x_2);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get_uint8(x_136, 0);
x_149 = lean_ctor_get_uint8(x_136, 1);
x_150 = lean_ctor_get_uint8(x_136, 2);
x_151 = lean_ctor_get_uint8(x_136, 3);
x_152 = lean_ctor_get_uint8(x_136, 4);
x_153 = lean_ctor_get_uint8(x_136, 5);
x_154 = lean_ctor_get_uint8(x_136, 6);
x_155 = lean_ctor_get_uint8(x_136, 7);
x_156 = lean_ctor_get_uint8(x_136, 8);
x_157 = lean_ctor_get_uint8(x_136, 9);
x_158 = lean_ctor_get_uint8(x_136, 10);
x_159 = lean_ctor_get_uint8(x_136, 11);
x_160 = lean_ctor_get_uint8(x_136, 12);
x_161 = lean_ctor_get_uint8(x_136, 13);
x_162 = lean_ctor_get_uint8(x_136, 14);
x_163 = lean_ctor_get_uint8(x_136, 15);
x_164 = lean_ctor_get_uint8(x_136, 16);
x_165 = lean_ctor_get_uint8(x_136, 17);
if (lean_is_exclusive(x_136)) {
 x_166 = x_136;
} else {
 lean_dec_ref(x_136);
 x_166 = lean_box(0);
}
x_167 = lean_unsigned_to_nat(1u);
x_168 = lean_nat_add(x_123, x_167);
lean_dec(x_123);
x_169 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_169, 0, x_120);
lean_ctor_set(x_169, 1, x_121);
lean_ctor_set(x_169, 2, x_122);
lean_ctor_set(x_169, 3, x_168);
lean_ctor_set(x_169, 4, x_124);
lean_ctor_set(x_169, 5, x_125);
lean_ctor_set(x_169, 6, x_126);
lean_ctor_set(x_169, 7, x_127);
lean_ctor_set(x_169, 8, x_128);
lean_ctor_set(x_169, 9, x_129);
lean_ctor_set(x_169, 10, x_130);
lean_ctor_set(x_169, 11, x_132);
lean_ctor_set(x_169, 12, x_134);
lean_ctor_set_uint8(x_169, sizeof(void*)*13, x_131);
lean_ctor_set_uint8(x_169, sizeof(void*)*13 + 1, x_133);
x_230 = lean_box(1);
x_231 = lean_unbox(x_230);
x_232 = l_Lean_Meta_TransparencyMode_lt(x_157, x_231);
if (x_232 == 0)
{
x_205 = x_157;
goto block_229;
}
else
{
uint8_t x_233; 
x_233 = lean_unbox(x_230);
x_205 = x_233;
goto block_229;
}
block_204:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; uint8_t x_200; uint64_t x_201; lean_object* x_202; lean_object* x_203; 
x_193 = lean_box(1);
x_194 = lean_box(2);
if (lean_is_scalar(x_166)) {
 x_195 = lean_alloc_ctor(0, 0, 18);
} else {
 x_195 = x_166;
}
lean_ctor_set_uint8(x_195, 0, x_170);
lean_ctor_set_uint8(x_195, 1, x_188);
lean_ctor_set_uint8(x_195, 2, x_187);
lean_ctor_set_uint8(x_195, 3, x_189);
lean_ctor_set_uint8(x_195, 4, x_171);
lean_ctor_set_uint8(x_195, 5, x_177);
lean_ctor_set_uint8(x_195, 6, x_179);
lean_ctor_set_uint8(x_195, 7, x_190);
lean_ctor_set_uint8(x_195, 8, x_180);
lean_ctor_set_uint8(x_195, 9, x_186);
lean_ctor_set_uint8(x_195, 10, x_192);
lean_ctor_set_uint8(x_195, 11, x_182);
x_196 = lean_unbox(x_193);
lean_ctor_set_uint8(x_195, 12, x_196);
x_197 = lean_unbox(x_193);
lean_ctor_set_uint8(x_195, 13, x_197);
x_198 = lean_unbox(x_194);
lean_ctor_set_uint8(x_195, 14, x_198);
x_199 = lean_unbox(x_193);
lean_ctor_set_uint8(x_195, 15, x_199);
x_200 = lean_unbox(x_193);
lean_ctor_set_uint8(x_195, 16, x_200);
lean_ctor_set_uint8(x_195, 17, x_172);
x_201 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_195);
if (lean_is_scalar(x_147)) {
 x_202 = lean_alloc_ctor(0, 7, 11);
} else {
 x_202 = x_147;
}
lean_ctor_set(x_202, 0, x_195);
lean_ctor_set(x_202, 1, x_185);
lean_ctor_set(x_202, 2, x_174);
lean_ctor_set(x_202, 3, x_176);
lean_ctor_set(x_202, 4, x_173);
lean_ctor_set(x_202, 5, x_191);
lean_ctor_set(x_202, 6, x_175);
lean_ctor_set_uint64(x_202, sizeof(void*)*7, x_201);
lean_ctor_set_uint8(x_202, sizeof(void*)*7 + 8, x_181);
lean_ctor_set_uint8(x_202, sizeof(void*)*7 + 9, x_184);
lean_ctor_set_uint8(x_202, sizeof(void*)*7 + 10, x_183);
x_203 = l_Lean_Meta_inferTypeImp_infer(x_1, x_202, x_3, x_169, x_5, x_178);
return x_203;
}
block_229:
{
lean_object* x_206; uint64_t x_207; uint64_t x_208; uint64_t x_209; uint64_t x_210; uint64_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_206 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_206, 0, x_148);
lean_ctor_set_uint8(x_206, 1, x_149);
lean_ctor_set_uint8(x_206, 2, x_150);
lean_ctor_set_uint8(x_206, 3, x_151);
lean_ctor_set_uint8(x_206, 4, x_152);
lean_ctor_set_uint8(x_206, 5, x_153);
lean_ctor_set_uint8(x_206, 6, x_154);
lean_ctor_set_uint8(x_206, 7, x_155);
lean_ctor_set_uint8(x_206, 8, x_156);
lean_ctor_set_uint8(x_206, 9, x_205);
lean_ctor_set_uint8(x_206, 10, x_158);
lean_ctor_set_uint8(x_206, 11, x_159);
lean_ctor_set_uint8(x_206, 12, x_160);
lean_ctor_set_uint8(x_206, 13, x_161);
lean_ctor_set_uint8(x_206, 14, x_162);
lean_ctor_set_uint8(x_206, 15, x_163);
lean_ctor_set_uint8(x_206, 16, x_164);
lean_ctor_set_uint8(x_206, 17, x_165);
x_207 = 2;
x_208 = lean_uint64_shift_right(x_137, x_207);
x_209 = lean_uint64_shift_left(x_208, x_207);
x_210 = l_Lean_Meta_TransparencyMode_toUInt64(x_205);
x_211 = lean_uint64_lor(x_209, x_210);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
x_212 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_212, 0, x_206);
lean_ctor_set(x_212, 1, x_139);
lean_ctor_set(x_212, 2, x_140);
lean_ctor_set(x_212, 3, x_141);
lean_ctor_set(x_212, 4, x_142);
lean_ctor_set(x_212, 5, x_143);
lean_ctor_set(x_212, 6, x_144);
lean_ctor_set_uint64(x_212, sizeof(void*)*7, x_211);
lean_ctor_set_uint8(x_212, sizeof(void*)*7 + 8, x_138);
lean_ctor_set_uint8(x_212, sizeof(void*)*7 + 9, x_145);
lean_ctor_set_uint8(x_212, sizeof(void*)*7 + 10, x_146);
x_213 = l_Lean_Meta_getConfig___redArg(x_212, x_6);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get_uint8(x_214, 13);
if (x_215 == 0)
{
lean_object* x_216; 
lean_dec(x_214);
lean_dec(x_212);
x_216 = lean_ctor_get(x_213, 1);
lean_inc(x_216);
lean_dec(x_213);
x_170 = x_148;
x_171 = x_152;
x_172 = x_165;
x_173 = x_142;
x_174 = x_140;
x_175 = x_144;
x_176 = x_141;
x_177 = x_153;
x_178 = x_216;
x_179 = x_154;
x_180 = x_156;
x_181 = x_138;
x_182 = x_159;
x_183 = x_146;
x_184 = x_145;
x_185 = x_139;
x_186 = x_205;
x_187 = x_150;
x_188 = x_149;
x_189 = x_151;
x_190 = x_155;
x_191 = x_143;
x_192 = x_158;
goto block_204;
}
else
{
uint8_t x_217; 
x_217 = lean_ctor_get_uint8(x_214, 12);
if (x_217 == 0)
{
lean_object* x_218; 
lean_dec(x_214);
lean_dec(x_212);
x_218 = lean_ctor_get(x_213, 1);
lean_inc(x_218);
lean_dec(x_213);
x_170 = x_148;
x_171 = x_152;
x_172 = x_165;
x_173 = x_142;
x_174 = x_140;
x_175 = x_144;
x_176 = x_141;
x_177 = x_153;
x_178 = x_218;
x_179 = x_154;
x_180 = x_156;
x_181 = x_138;
x_182 = x_159;
x_183 = x_146;
x_184 = x_145;
x_185 = x_139;
x_186 = x_205;
x_187 = x_150;
x_188 = x_149;
x_189 = x_151;
x_190 = x_155;
x_191 = x_143;
x_192 = x_158;
goto block_204;
}
else
{
uint8_t x_219; 
x_219 = lean_ctor_get_uint8(x_214, 15);
if (x_219 == 0)
{
lean_object* x_220; 
lean_dec(x_214);
lean_dec(x_212);
x_220 = lean_ctor_get(x_213, 1);
lean_inc(x_220);
lean_dec(x_213);
x_170 = x_148;
x_171 = x_152;
x_172 = x_165;
x_173 = x_142;
x_174 = x_140;
x_175 = x_144;
x_176 = x_141;
x_177 = x_153;
x_178 = x_220;
x_179 = x_154;
x_180 = x_156;
x_181 = x_138;
x_182 = x_159;
x_183 = x_146;
x_184 = x_145;
x_185 = x_139;
x_186 = x_205;
x_187 = x_150;
x_188 = x_149;
x_189 = x_151;
x_190 = x_155;
x_191 = x_143;
x_192 = x_158;
goto block_204;
}
else
{
uint8_t x_221; 
x_221 = lean_ctor_get_uint8(x_214, 16);
if (x_221 == 0)
{
lean_object* x_222; 
lean_dec(x_214);
lean_dec(x_212);
x_222 = lean_ctor_get(x_213, 1);
lean_inc(x_222);
lean_dec(x_213);
x_170 = x_148;
x_171 = x_152;
x_172 = x_165;
x_173 = x_142;
x_174 = x_140;
x_175 = x_144;
x_176 = x_141;
x_177 = x_153;
x_178 = x_222;
x_179 = x_154;
x_180 = x_156;
x_181 = x_138;
x_182 = x_159;
x_183 = x_146;
x_184 = x_145;
x_185 = x_139;
x_186 = x_205;
x_187 = x_150;
x_188 = x_149;
x_189 = x_151;
x_190 = x_155;
x_191 = x_143;
x_192 = x_158;
goto block_204;
}
else
{
lean_object* x_223; uint8_t x_224; lean_object* x_225; uint8_t x_226; uint8_t x_227; 
x_223 = lean_ctor_get(x_213, 1);
lean_inc(x_223);
lean_dec(x_213);
x_224 = lean_ctor_get_uint8(x_214, 14);
lean_dec(x_214);
x_225 = lean_box(2);
x_226 = lean_unbox(x_225);
x_227 = l_Lean_Meta_instDecidableEqProjReductionKind(x_224, x_226);
if (x_227 == 0)
{
lean_dec(x_212);
x_170 = x_148;
x_171 = x_152;
x_172 = x_165;
x_173 = x_142;
x_174 = x_140;
x_175 = x_144;
x_176 = x_141;
x_177 = x_153;
x_178 = x_223;
x_179 = x_154;
x_180 = x_156;
x_181 = x_138;
x_182 = x_159;
x_183 = x_146;
x_184 = x_145;
x_185 = x_139;
x_186 = x_205;
x_187 = x_150;
x_188 = x_149;
x_189 = x_151;
x_190 = x_155;
x_191 = x_143;
x_192 = x_158;
goto block_204;
}
else
{
lean_object* x_228; 
lean_dec(x_166);
lean_dec(x_147);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
x_228 = l_Lean_Meta_inferTypeImp_infer(x_1, x_212, x_3, x_169, x_5, x_223);
return x_228;
}
}
}
}
}
}
}
else
{
lean_object* x_234; 
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_234 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg(x_125, x_6);
return x_234;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
case 2:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(x_4);
if (x_6 == 0)
{
return x_6;
}
else
{
x_1 = x_5;
goto _start;
}
}
case 3:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
x_1 = x_8;
goto _start;
}
default: 
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_2, x_10);
lean_dec(x_2);
if (x_11 == 0)
{
lean_dec(x_9);
x_5 = x_4;
goto block_8;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_instantiateLevelMVars___at___Lean_Meta_normalizeLevel_spec__0___redArg(x_9, x_3, x_4);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(x_14);
lean_dec(x_14);
x_16 = l_Bool_toLBool(x_15);
x_17 = lean_box(x_16);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(x_18);
lean_dec(x_18);
x_21 = l_Bool_toLBool(x_20);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
}
case 7:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_1, 2);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_2, x_25);
if (x_26 == 1)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_2, x_29);
lean_dec(x_2);
x_1 = x_24;
x_2 = x_30;
goto _start;
}
}
case 8:
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_1, 3);
lean_inc(x_32);
lean_dec(x_1);
x_1 = x_32;
goto _start;
}
case 10:
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_dec(x_1);
x_1 = x_34;
goto _start;
}
default: 
{
lean_dec(x_2);
lean_dec(x_1);
x_5 = x_4;
goto block_8;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___redArg(x_1, x_2, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(x_8, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___redArg(x_10, x_2, x_4, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
case 2:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(x_17, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___redArg(x_19, x_2, x_4, x_20);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
case 4:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_26, x_27, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___redArg(x_29, x_2, x_4, x_30);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
case 5:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_2, x_37);
lean_dec(x_2);
x_1 = x_36;
x_2 = x_38;
goto _start;
}
case 6:
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_1, 2);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_eq(x_2, x_41);
if (x_42 == 1)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_7);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_2, x_45);
lean_dec(x_2);
x_1 = x_40;
x_2 = x_46;
goto _start;
}
}
case 8:
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_1, 3);
lean_inc(x_48);
lean_dec(x_1);
x_1 = x_48;
goto _start;
}
case 10:
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
lean_dec(x_1);
x_1 = x_50;
goto _start;
}
default: 
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_box(2);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_7);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(x_9, x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___redArg(x_11, x_13, x_3, x_12);
return x_14;
}
else
{
uint8_t x_15; 
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
case 2:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(x_19, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___redArg(x_21, x_23, x_3, x_22);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
case 4:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_29, x_30, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___redArg(x_32, x_34, x_3, x_33);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
case 5:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_unsigned_to_nat(1u);
x_42 = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(x_40, x_41, x_2, x_3, x_4, x_5, x_6);
return x_42;
}
case 7:
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_1, 2);
lean_inc(x_43);
lean_dec(x_1);
x_1 = x_43;
goto _start;
}
case 8:
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_1, 3);
lean_inc(x_45);
lean_dec(x_1);
x_1 = x_45;
goto _start;
}
case 10:
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
lean_dec(x_1);
x_1 = x_47;
goto _start;
}
case 11:
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_box(2);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_6);
return x_50;
}
default: 
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_6);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isPropQuick(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_isPropQuick(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
switch (x_9) {
case 0:
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
case 1:
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = lean_box(1);
lean_ctor_set(x_7, 0, x_18);
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
default: 
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_3);
x_26 = l_Lean_Meta_whnfD(x_24, x_2, x_3, x_4, x_5, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 3)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_instantiateLevelMVars___at___Lean_Meta_normalizeLevel_spec__0___redArg(x_29, x_3, x_28);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(x_32);
lean_dec(x_32);
x_34 = lean_box(x_33);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_30);
x_37 = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(x_35);
lean_dec(x_35);
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_27);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_26, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_26, 0, x_42);
return x_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 1);
lean_inc(x_43);
lean_dec(x_26);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_26);
if (x_46 == 0)
{
return x_26;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_26, 0);
x_48 = lean_ctor_get(x_26, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_26);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_23);
if (x_50 == 0)
{
return x_23;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_23, 0);
x_52 = lean_ctor_get(x_23, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_23);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_7);
if (x_54 == 0)
{
return x_7;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_7, 0);
x_56 = lean_ctor_get(x_7, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_7);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_2, x_9);
if (x_10 == 1)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_2);
x_11 = l_Lean_Meta_isPropQuick(x_1, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_2, x_12);
lean_dec(x_2);
x_1 = x_8;
x_2 = x_13;
goto _start;
}
}
case 8:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_2, x_16);
if (x_17 == 0)
{
x_1 = x_15;
goto _start;
}
else
{
lean_dec(x_2);
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
case 10:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_2, x_21);
if (x_22 == 0)
{
x_1 = x_20;
goto _start;
}
else
{
lean_dec(x_2);
x_1 = x_20;
x_2 = x_21;
goto _start;
}
}
default: 
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_2, x_25);
lean_dec(x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_box(2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_7);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = l_Lean_Meta_isPropQuick(x_1, x_3, x_4, x_5, x_6, x_7);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_3);
x_9 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(x_8, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(x_10, x_2, x_3, x_4, x_5, x_6, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
case 2:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(x_17, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(x_19, x_2, x_3, x_4, x_5, x_6, x_20);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
case 4:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_26, x_27, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(x_29, x_2, x_3, x_4, x_5, x_6, x_30);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
case 5:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_2, x_37);
lean_dec(x_2);
x_1 = x_36;
x_2 = x_38;
goto _start;
}
case 6:
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_1, 2);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_eq(x_2, x_41);
if (x_42 == 1)
{
lean_object* x_43; 
lean_dec(x_2);
x_43 = l_Lean_Meta_isProofQuick(x_40, x_3, x_4, x_5, x_6, x_7);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_2, x_44);
lean_dec(x_2);
x_1 = x_40;
x_2 = x_45;
goto _start;
}
}
case 8:
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_1, 3);
lean_inc(x_47);
lean_dec(x_1);
x_1 = x_47;
goto _start;
}
case 10:
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_1, 1);
lean_inc(x_49);
lean_dec(x_1);
x_1 = x_49;
goto _start;
}
default: 
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_box(2);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_7);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
lean_inc(x_2);
x_10 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(x_9, x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(x_11, x_13, x_2, x_3, x_4, x_5, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_2);
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
case 2:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(x_21, x_23, x_2, x_3, x_4, x_5, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
case 4:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_29, x_30, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(x_32, x_34, x_2, x_3, x_4, x_5, x_33);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
case 5:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_unsigned_to_nat(1u);
x_42 = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(x_40, x_41, x_2, x_3, x_4, x_5, x_6);
return x_42;
}
case 6:
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_1, 2);
lean_inc(x_43);
lean_dec(x_1);
x_1 = x_43;
goto _start;
}
case 8:
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_1, 3);
lean_inc(x_45);
lean_dec(x_1);
x_1 = x_45;
goto _start;
}
case 10:
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
lean_dec(x_1);
x_1 = x_47;
goto _start;
}
case 11:
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_box(2);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_6);
return x_50;
}
default: 
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_6);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isProofQuick(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_isProofQuick(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
switch (x_9) {
case 0:
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
case 1:
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = lean_box(1);
lean_ctor_set(x_7, 0, x_18);
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
default: 
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_isProp(x_24, x_2, x_3, x_4, x_5, x_25);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
return x_7;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
lean_dec(x_2);
if (x_9 == 0)
{
x_4 = x_3;
goto block_7;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
case 7:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 1)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_2, x_17);
lean_dec(x_2);
x_1 = x_12;
x_2 = x_18;
goto _start;
}
}
case 8:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_1, 3);
x_1 = x_20;
goto _start;
}
case 10:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_1, 1);
x_1 = x_22;
goto _start;
}
default: 
{
lean_dec(x_2);
x_4 = x_3;
goto block_7;
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(x_8, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(x_10, x_2, x_11);
lean_dec(x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
case 2:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(x_17, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(x_19, x_2, x_20);
lean_dec(x_19);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
case 4:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_26, x_27, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(x_29, x_2, x_30);
lean_dec(x_29);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
case 5:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_2, x_37);
lean_dec(x_2);
x_1 = x_36;
x_2 = x_38;
goto _start;
}
case 6:
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_1, 2);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_eq(x_2, x_41);
if (x_42 == 1)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_7);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_2, x_45);
lean_dec(x_2);
x_1 = x_40;
x_2 = x_46;
goto _start;
}
}
case 8:
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_1, 3);
lean_inc(x_48);
lean_dec(x_1);
x_1 = x_48;
goto _start;
}
case 10:
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
lean_dec(x_1);
x_1 = x_50;
goto _start;
}
default: 
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_box(2);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_7);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(x_7, x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(x_9, x_11, x_10);
lean_dec(x_9);
return x_12;
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
case 2:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(x_17, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(x_19, x_21, x_20);
lean_dec(x_19);
return x_22;
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
case 3:
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
case 4:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_29, x_30, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(x_32, x_34, x_33);
lean_dec(x_32);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
case 5:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_unsigned_to_nat(1u);
x_42 = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(x_40, x_41, x_2, x_3, x_4, x_5, x_6);
return x_42;
}
case 6:
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_6);
return x_44;
}
case 7:
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_6);
return x_46;
}
case 8:
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_1, 3);
lean_inc(x_47);
lean_dec(x_1);
x_1 = x_47;
goto _start;
}
case 9:
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_6);
return x_50;
}
case 10:
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
lean_dec(x_1);
x_1 = x_51;
goto _start;
}
default: 
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_box(2);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_6);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isTypeQuick(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_isTypeQuick(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
switch (x_9) {
case 0:
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
case 1:
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = lean_box(1);
lean_ctor_set(x_7, 0, x_18);
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
default: 
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_whnfD(x_24, x_2, x_3, x_4, x_5, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 3)
{
uint8_t x_28; 
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_box(1);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_box(1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_27);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_26, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_26, 0, x_36);
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 1);
lean_inc(x_37);
lean_dec(x_26);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
return x_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_26, 0);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_26);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
}
else
{
uint8_t x_48; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_7);
if (x_48 == 0)
{
return x_7;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_7, 0);
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_7);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
case 7:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 2);
x_1 = x_4;
goto _start;
}
default: 
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_typeFormerTypeLevelQuick(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_push(x_1, x_3);
x_10 = l_Lean_Meta_typeFormerTypeLevel_go(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_typeFormerTypeLevel_go___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_8 = x_13;
x_9 = x_7;
goto block_12;
}
case 7:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_typeFormerTypeLevel_go___lam__0), 8, 2);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_16);
x_19 = lean_expr_instantiate_rev(x_15, x_2);
lean_dec(x_2);
lean_dec(x_15);
x_20 = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(x_14, x_17, x_19, x_18, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
default: 
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l_Lean_Meta_whnfD(x_21, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
switch (lean_obj_tag(x_23)) {
case 3:
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_8 = x_25;
x_9 = x_24;
goto block_12;
}
case 7:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = l_Lean_Meta_typeFormerTypeLevel_go___closed__0;
x_1 = x_23;
x_2 = x_27;
x_7 = x_26;
goto _start;
}
default: 
{
uint8_t x_29; 
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_22, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_22, 0, x_31);
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_dec(x_22);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 1);
lean_dec(x_9);
lean_ctor_set(x_6, 1, x_2);
x_10 = lean_st_ref_set(x_1, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 2);
x_19 = lean_ctor_get(x_6, 3);
x_20 = lean_ctor_get(x_6, 4);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set(x_21, 4, x_20);
x_22 = lean_st_ref_set(x_1, x_21, x_7);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_typeFormerTypeLevelQuick(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_st_ref_get(x_3, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_typeFormerTypeLevel_go___closed__0;
lean_inc(x_3);
x_13 = l_Lean_Meta_typeFormerTypeLevel_go(x_1, x_12, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = l_Lean_Meta_typeFormerTypeLevel___lam__0(x_3, x_11, x_16, x_15);
lean_dec(x_16);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_14);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_box(0);
x_25 = l_Lean_Meta_typeFormerTypeLevel___lam__0(x_3, x_11, x_24, x_23);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 0, x_22);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_6);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_typeFormerTypeLevel___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_typeFormerTypeLevel(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_7, 0);
lean_dec(x_16);
x_17 = lean_box(1);
lean_ctor_set(x_7, 0, x_17);
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_box(1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Meta_isPropFormerType_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_level_eq(x_9, x_10);
return x_11;
}
}
}
}
static lean_object* _init_l_Lean_Meta_isPropFormerType___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_typeFormerTypeLevel(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Meta_isPropFormerType___closed__0;
x_11 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Meta_isPropFormerType_spec__0(x_9, x_10);
lean_dec(x_9);
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = l_Lean_Meta_isPropFormerType___closed__0;
x_16 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Meta_isPropFormerType_spec__0(x_13, x_15);
lean_dec(x_13);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Meta_isPropFormerType_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_isTypeFormerType(x_8, x_2, x_3, x_4, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
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
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_expr_eqv(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___Lean_Meta_arrowDomainsN_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_arrowDomainsN_spec__0_spec__0(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_arrowDomainsN_spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_3, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = lean_infer_type(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_16, x_2, x_13);
x_2 = x_18;
x_3 = x_19;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_arrowDomainsN_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_hasFVar(x_2);
if (x_3 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_Expr_fvar___override(x_9);
x_11 = l_Array_contains___at___Lean_Meta_arrowDomainsN_spec__0(x_1, x_10);
lean_dec(x_10);
return x_11;
}
case 5:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_arrowDomainsN_spec__3(x_1, x_12);
if (x_14 == 0)
{
x_2 = x_13;
goto _start;
}
else
{
lean_dec(x_13);
return x_3;
}
}
case 6:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
lean_dec(x_2);
x_4 = x_16;
x_5 = x_17;
goto block_8;
}
case 7:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
lean_dec(x_2);
x_4 = x_18;
x_5 = x_19;
goto block_8;
}
case 8:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 3);
lean_inc(x_22);
lean_dec(x_2);
x_23 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_arrowDomainsN_spec__3(x_1, x_20);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_arrowDomainsN_spec__3(x_1, x_21);
if (x_24 == 0)
{
x_2 = x_22;
goto _start;
}
else
{
lean_dec(x_22);
return x_3;
}
}
else
{
lean_dec(x_22);
lean_dec(x_21);
return x_3;
}
}
case 10:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_dec(x_2);
x_2 = x_26;
goto _start;
}
case 11:
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_dec(x_2);
x_2 = x_28;
goto _start;
}
default: 
{
lean_object* x_30; uint8_t x_31; 
lean_dec(x_2);
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
return x_31;
}
}
}
block_8:
{
uint8_t x_6; 
x_6 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_arrowDomainsN_spec__3(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_dec(x_5);
return x_3;
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected dependent type ", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" in ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_6, x_5);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_7);
x_21 = lean_array_uget(x_4, x_6);
lean_inc(x_21);
x_22 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_arrowDomainsN_spec__3(x_1, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_inc(x_2);
x_13 = x_2;
x_14 = x_12;
goto block_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_23 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__1;
x_24 = l_Lean_MessageData_ofExpr(x_21);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__3;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MessageData_ofExpr(x_3);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Meta_throwFunctionExpected___redArg___closed__3;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_31, x_8, x_9, x_10, x_11, x_12);
return x_32;
}
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_6, x_15);
x_6 = x_16;
x_7 = x_13;
x_12 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_6, x_5);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_7);
x_21 = lean_array_uget(x_4, x_6);
lean_inc(x_21);
x_22 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_arrowDomainsN_spec__3(x_1, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_inc(x_2);
x_13 = x_2;
x_14 = x_12;
goto block_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_23 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__1;
x_24 = l_Lean_MessageData_ofExpr(x_21);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__3;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MessageData_ofExpr(x_3);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Meta_throwFunctionExpected___redArg___closed__3;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_31, x_8, x_9, x_10, x_11, x_12);
return x_32;
}
}
block_18:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 1;
x_16 = lean_usize_add(x_6, x_15);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_16, x_13, x_8, x_9, x_10, x_11, x_14);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___lam__0), 8, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___redArg(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_arrowDomainsN___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" does not have ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_arrowDomainsN___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" parameters", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_arrowDomainsN___lam__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_eq(x_10, x_2);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_3);
x_12 = l_Lean_Meta_arrowDomainsN___lam__0___closed__1;
x_13 = l_Lean_MessageData_ofExpr(x_1);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_arrowDomainsN___lam__0___closed__3;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Nat_reprFast(x_2);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_MessageData_ofFormat(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Meta_arrowDomainsN___lam__0___closed__5;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_22, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
lean_dec(x_2);
x_28 = lean_array_size(x_3);
x_29 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_30 = l_Array_mapMUnsafe_map___at___Lean_Meta_arrowDomainsN_spec__2(x_28, x_29, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = lean_array_size(x_31);
x_35 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4(x_3, x_33, x_1, x_31, x_34, x_29, x_33, x_5, x_6, x_7, x_8, x_32);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_31);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_31);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
return x_35;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_35);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
lean_inc(x_1);
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = lean_unbox(x_10);
x_13 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_2, x_9, x_8, x_11, x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_arrowDomainsN_spec__0_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___Lean_Meta_arrowDomainsN_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Meta_arrowDomainsN_spec__2(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_arrowDomainsN_spec__3(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_arrowDomainsN___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_arrowDomainsN(x_1, x_9, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* initialize_Lean_Data_LBool(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_LBool(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__0 = _init_l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__0();
lean_mark_persistent(l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__0);
l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__1 = _init_l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__1();
lean_mark_persistent(l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__1);
l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__2 = _init_l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__2();
lean_mark_persistent(l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__2);
l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__3 = _init_l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__3();
lean_mark_persistent(l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__3);
l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__4 = _init_l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__4();
lean_mark_persistent(l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__4);
l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__5 = _init_l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__5();
lean_mark_persistent(l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__5);
l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__6 = _init_l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__6();
lean_mark_persistent(l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__6);
l_Lean_Expr_instantiateBetaRevRange_visit___closed__0 = _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__0();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange_visit___closed__0);
l_Lean_Expr_instantiateBetaRevRange_visit___closed__1 = _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__1();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange_visit___closed__1);
l_Lean_Expr_instantiateBetaRevRange_visit___closed__2 = _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__2();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange_visit___closed__2);
l_Lean_Expr_instantiateBetaRevRange_visit___closed__3 = _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__3();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange_visit___closed__3);
l_Lean_Expr_instantiateBetaRevRange_visit___closed__4 = _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__4();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange_visit___closed__4);
l_Lean_Expr_instantiateBetaRevRange_visit___closed__5 = _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__5();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange_visit___closed__5);
l_Lean_Expr_instantiateBetaRevRange_visit___closed__6 = _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__6();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange_visit___closed__6);
l_Lean_Expr_instantiateBetaRevRange_visit___closed__7 = _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__7();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange_visit___closed__7);
l_Lean_Expr_instantiateBetaRevRange___closed__0 = _init_l_Lean_Expr_instantiateBetaRevRange___closed__0();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange___closed__0);
l_Lean_Expr_instantiateBetaRevRange___closed__1 = _init_l_Lean_Expr_instantiateBetaRevRange___closed__1();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange___closed__1);
l_Lean_Expr_instantiateBetaRevRange___closed__2 = _init_l_Lean_Expr_instantiateBetaRevRange___closed__2();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange___closed__2);
l_Lean_Expr_instantiateBetaRevRange___closed__3 = _init_l_Lean_Expr_instantiateBetaRevRange___closed__3();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange___closed__3);
l_Lean_Expr_instantiateBetaRevRange___closed__4 = _init_l_Lean_Expr_instantiateBetaRevRange___closed__4();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange___closed__4);
l_Lean_Expr_instantiateBetaRevRange___closed__5 = _init_l_Lean_Expr_instantiateBetaRevRange___closed__5();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange___closed__5);
l_Lean_Expr_instantiateBetaRevRange___closed__6 = _init_l_Lean_Expr_instantiateBetaRevRange___closed__6();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange___closed__6);
l_Lean_Expr_instantiateBetaRevRange___closed__7 = _init_l_Lean_Expr_instantiateBetaRevRange___closed__7();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange___closed__7);
l_Lean_Meta_throwFunctionExpected___redArg___closed__0 = _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_throwFunctionExpected___redArg___closed__0);
l_Lean_Meta_throwFunctionExpected___redArg___closed__1 = _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_throwFunctionExpected___redArg___closed__1);
l_Lean_Meta_throwFunctionExpected___redArg___closed__2 = _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_throwFunctionExpected___redArg___closed__2);
l_Lean_Meta_throwFunctionExpected___redArg___closed__3 = _init_l_Lean_Meta_throwFunctionExpected___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_throwFunctionExpected___redArg___closed__3);
l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0 = _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0);
l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1 = _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1);
l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__0 = _init_l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__0();
lean_mark_persistent(l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__0);
l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__1 = _init_l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__1();
lean_mark_persistent(l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__1);
l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__2 = _init_l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__2();
lean_mark_persistent(l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__2);
l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__3 = _init_l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__3();
lean_mark_persistent(l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___closed__3);
l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0 = _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0);
l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1 = _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1);
l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2 = _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2);
l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3 = _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3);
l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0 = _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0();
lean_mark_persistent(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0);
l_Lean_Meta_throwTypeExcepted___redArg___closed__0 = _init_l_Lean_Meta_throwTypeExcepted___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_throwTypeExcepted___redArg___closed__0);
l_Lean_Meta_throwTypeExcepted___redArg___closed__1 = _init_l_Lean_Meta_throwTypeExcepted___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_throwTypeExcepted___redArg___closed__1);
l_Lean_Meta_throwUnknownMVar___redArg___closed__0 = _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_throwUnknownMVar___redArg___closed__0);
l_Lean_Meta_throwUnknownMVar___redArg___closed__1 = _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0 = _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0();
lean_mark_persistent(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0);
l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1 = _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1();
lean_mark_persistent(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
l_Lean_Meta_inferTypeImp_infer___closed__0 = _init_l_Lean_Meta_inferTypeImp_infer___closed__0();
lean_mark_persistent(l_Lean_Meta_inferTypeImp_infer___closed__0);
l_Lean_Meta_inferTypeImp_infer___closed__1 = _init_l_Lean_Meta_inferTypeImp_infer___closed__1();
lean_mark_persistent(l_Lean_Meta_inferTypeImp_infer___closed__1);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__0 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__0);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__1);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__2);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__3);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__4);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__5);
l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__6);
l_Lean_Meta_typeFormerTypeLevel_go___closed__0 = _init_l_Lean_Meta_typeFormerTypeLevel_go___closed__0();
lean_mark_persistent(l_Lean_Meta_typeFormerTypeLevel_go___closed__0);
l_Lean_Meta_isPropFormerType___closed__0 = _init_l_Lean_Meta_isPropFormerType___closed__0();
lean_mark_persistent(l_Lean_Meta_isPropFormerType___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__1);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__2);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__3);
l_Lean_Meta_arrowDomainsN___lam__0___closed__0 = _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_arrowDomainsN___lam__0___closed__0);
l_Lean_Meta_arrowDomainsN___lam__0___closed__1 = _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_arrowDomainsN___lam__0___closed__1);
l_Lean_Meta_arrowDomainsN___lam__0___closed__2 = _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_arrowDomainsN___lam__0___closed__2);
l_Lean_Meta_arrowDomainsN___lam__0___closed__3 = _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_arrowDomainsN___lam__0___closed__3);
l_Lean_Meta_arrowDomainsN___lam__0___closed__4 = _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_arrowDomainsN___lam__0___closed__4);
l_Lean_Meta_arrowDomainsN___lam__0___closed__5 = _init_l_Lean_Meta_arrowDomainsN___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_arrowDomainsN___lam__0___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
