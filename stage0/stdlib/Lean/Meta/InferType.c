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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwFunctionExpected___rarg___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwFunctionExpected___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___closed__1;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_Meta_arrowDomainsN___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Expr_instantiateBetaRevRange_visit___spec__4(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Core_instantiateTypeLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_Meta_arrowDomainsN___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownMVar___spec__1(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___rarg___closed__1;
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__4;
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__10;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_arrowDomainsN___spec__3(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Meta_isPropFormerType___spec__1(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_instantiateBetaRevRange_visit___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownMVar___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwTypeExcepted___rarg___closed__2;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__12;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_isPropFormerType___closed__1;
lean_object* l_Lean_Literal_type(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__3;
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_arrowDomainsN___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___rarg___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_arrowDomainsN___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Meta_withInferTypeConfig___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Meta_isPropFormerType___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwTypeExcepted___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownMVar___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwIncorrectNumberOfLevels___spec__1(lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__5;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_throwTypeExcepted___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1(lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Expr_instantiateBetaRevRange_visit___spec__4___at_Lean_Expr_instantiateBetaRevRange_visit___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_outOfBounds___rarg(lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__11;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_Meta_instDecidableEqProjReductionKind(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static size_t l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___closed__2;
static lean_object* l_Lean_Meta_typeFormerTypeLevel_go___closed__1;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_panic___at_Lean_Expr_appFn_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwFunctionExpected___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8___closed__1;
lean_object* lean_expr_consume_type_annotations(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwFunctionExpected___rarg___closed__1;
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_arrowDomainsN___lambda__2___closed__4;
lean_object* l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__2;
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__8;
lean_object* lean_usize_to_nat(size_t);
static lean_object* l_Lean_Meta_arrowDomainsN___lambda__2___closed__1;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwUnknownMVar___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp_infer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at_Lean_Meta_arrowDomainsN___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___rarg(lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__7;
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Meta_arrowDomainsN___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object*);
lean_object* l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ExprStructEq_instHashable;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_arrowDomainsN___lambda__2___closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
extern lean_object* l_Id_instMonad;
extern lean_object* l_Lean_ExprStructEq_instBEq;
LEAN_EXPORT lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_inferTypeImp_infer___closed__1;
static lean_object* l_Lean_Meta_arrowDomainsN___lambda__2___closed__5;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__13;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__6;
lean_object* l_Lean_Meta_mkExprConfigCacheKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_inferTypeImp_infer___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwFunctionExpected___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwTypeExcepted___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Expr_instantiateBetaRevRange_visit___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__2;
static lean_object* l_Lean_Meta_throwUnknownMVar___rarg___closed__2;
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__3;
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_instantiateBetaRevRange_visit___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__2;
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwUnknownMVar___rarg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_arrowDomainsN___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwIncorrectNumberOfLevels___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwIncorrectNumberOfLevels___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__3;
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Lean_FVarId_throwUnknown___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwUnknownMVar___rarg___closed__1;
static lean_object* l_Lean_Meta_throwFunctionExpected___rarg___closed__3;
static lean_object* l_Lean_Meta_arrowDomainsN___lambda__2___closed__3;
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__6;
static lean_object* l_Lean_Meta_arrowDomainsN___lambda__2___closed__6;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__1;
lean_object* l_Lean_Level_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__1;
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__7;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Expr_instantiateBetaRevRange_visit___spec__7___boxed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwTypeExcepted___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lambda__1___closed__1;
lean_object* l_instHashableNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__5;
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_expr_equal(x_6, x_8);
if (x_10 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_eq(x_7, x_9);
if (x_12 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Expr_instantiateBetaRevRange_visit___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_2, x_20);
lean_ctor_set(x_3, 2, x_21);
x_22 = lean_array_uset(x_2, x_20, x_3);
x_2 = x_22;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_27 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_24);
x_28 = lean_apply_1(x_1, x_24);
x_29 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_2, x_40);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_array_uset(x_2, x_40, x_42);
x_2 = x_43;
x_3 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Expr_instantiateBetaRevRange_visit___spec__4___at_Lean_Expr_instantiateBetaRevRange_visit___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = 32;
x_8 = 16;
x_9 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_10 = 1;
x_11 = lean_usize_sub(x_9, x_10);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_14 = l_Lean_Expr_hash(x_12);
lean_dec(x_12);
x_15 = lean_uint64_of_nat(x_13);
lean_dec(x_13);
x_16 = lean_uint64_mix_hash(x_14, x_15);
x_17 = lean_uint64_shift_right(x_16, x_7);
x_18 = lean_uint64_xor(x_16, x_17);
x_19 = lean_uint64_shift_right(x_18, x_8);
x_20 = lean_uint64_xor(x_18, x_19);
x_21 = lean_uint64_to_usize(x_20);
x_22 = lean_usize_land(x_21, x_11);
x_23 = lean_array_uget(x_1, x_22);
lean_ctor_set(x_2, 2, x_23);
x_24 = lean_array_uset(x_1, x_22, x_2);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_29 = lean_array_get_size(x_1);
x_30 = 32;
x_31 = 16;
x_32 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_33 = 1;
x_34 = lean_usize_sub(x_32, x_33);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
x_37 = l_Lean_Expr_hash(x_35);
lean_dec(x_35);
x_38 = lean_uint64_of_nat(x_36);
lean_dec(x_36);
x_39 = lean_uint64_mix_hash(x_37, x_38);
x_40 = lean_uint64_shift_right(x_39, x_30);
x_41 = lean_uint64_xor(x_39, x_40);
x_42 = lean_uint64_shift_right(x_41, x_31);
x_43 = lean_uint64_xor(x_41, x_42);
x_44 = lean_uint64_to_usize(x_43);
x_45 = lean_usize_land(x_44, x_34);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Expr_instantiateBetaRevRange_visit___spec__4___at_Lean_Expr_instantiateBetaRevRange_visit___spec__5(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_expr_equal(x_9, x_11);
lean_dec(x_11);
lean_dec(x_9);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_10);
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_14);
return x_3;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_eq(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_16);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_ctor_get(x_3, 2);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_expr_equal(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_21);
x_25 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_1, x_2, x_19);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_25);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_eq(x_21, x_23);
lean_dec(x_23);
lean_dec(x_21);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_1, x_2, x_19);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_18);
lean_ctor_set(x_29, 2, x_28);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_18);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_19);
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Expr_instantiateBetaRevRange_visit___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_expr_equal(x_7, x_9);
if (x_11 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_eq(x_8, x_10);
if (x_13 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_15; 
lean_inc(x_5);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_5);
return x_15;
}
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Id_instMonad;
x_2 = l_StateT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8___closed__1;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8___closed__2;
x_4 = lean_panic_fn(x_3, x_1);
x_5 = lean_apply_1(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_instantiateBetaRevRange_visit___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
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
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_7, x_6, x_12);
lean_inc(x_4);
x_14 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_11, x_4, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_6, x_17);
x_19 = lean_array_uset(x_13, x_6, x_15);
x_6 = x_18;
x_7 = x_19;
x_8 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_array_push(x_8, x_11);
x_7 = x_10;
x_8 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_4);
lean_inc(x_7);
x_14 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_7, x_4, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_size(x_8);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at_Lean_Expr_instantiateBetaRevRange_visit___spec__9(x_1, x_2, x_3, x_4, x_17, x_18, x_8, x_16);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_Expr_isBVar(x_7);
lean_dec(x_7);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_mkAppRev(x_15, x_21);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
uint8_t x_24; lean_object* x_25; 
x_24 = 0;
x_25 = l_Lean_Expr_betaRev(x_15, x_21, x_24, x_24);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = l_Lean_Expr_isBVar(x_7);
lean_dec(x_7);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_mkAppRev(x_15, x_26);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
else
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_31 = 0;
x_32 = l_Lean_Expr_betaRev(x_15, x_26, x_31, x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__1;
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ExprStructEq_instBEq;
x_2 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__2;
x_3 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instHashableNat___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ExprStructEq_instHashable;
x_2 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__4;
x_3 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.InferType", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Expr.instantiateBetaRevRange.visit", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
x_2 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__7;
x_3 = lean_unsigned_to_nat(63u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__8;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
x_2 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__7;
x_3 = lean_unsigned_to_nat(64u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__8;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
x_2 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__7;
x_3 = lean_unsigned_to_nat(65u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__8;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
x_2 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__7;
x_3 = lean_unsigned_to_nat(62u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__8;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
x_2 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__7;
x_3 = lean_unsigned_to_nat(66u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__8;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; uint64_t x_100; uint64_t x_101; uint64_t x_102; size_t x_103; size_t x_104; size_t x_105; size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; 
lean_inc(x_5);
lean_inc(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
x_91 = lean_ctor_get(x_6, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_6, 1);
lean_inc(x_92);
x_93 = lean_array_get_size(x_92);
x_94 = l_Lean_Expr_hash(x_4);
x_95 = lean_uint64_of_nat(x_5);
x_96 = lean_uint64_mix_hash(x_94, x_95);
x_97 = 32;
x_98 = lean_uint64_shift_right(x_96, x_97);
x_99 = lean_uint64_xor(x_96, x_98);
x_100 = 16;
x_101 = lean_uint64_shift_right(x_99, x_100);
x_102 = lean_uint64_xor(x_99, x_101);
x_103 = lean_uint64_to_usize(x_102);
x_104 = lean_usize_of_nat(x_93);
lean_dec(x_93);
x_105 = 1;
x_106 = lean_usize_sub(x_104, x_105);
x_107 = lean_usize_land(x_103, x_106);
x_108 = lean_array_uget(x_92, x_107);
x_109 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Expr_instantiateBetaRevRange_visit___spec__7(x_9, x_108);
if (lean_obj_tag(x_109) == 0)
{
switch (lean_obj_tag(x_4)) {
case 0:
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_6);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_111 = lean_ctor_get(x_6, 1);
lean_dec(x_111);
x_112 = lean_ctor_get(x_6, 0);
lean_dec(x_112);
x_113 = lean_ctor_get(x_4, 0);
lean_inc(x_113);
lean_dec(x_4);
x_114 = lean_nat_sub(x_2, x_1);
x_115 = lean_nat_add(x_5, x_114);
x_116 = lean_nat_dec_lt(x_113, x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
lean_dec(x_5);
x_117 = lean_nat_sub(x_113, x_114);
lean_dec(x_114);
lean_dec(x_113);
x_118 = l_Lean_Expr_bvar___override(x_117);
x_119 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_108);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_120 = lean_unsigned_to_nat(1u);
x_121 = lean_nat_add(x_91, x_120);
lean_dec(x_91);
lean_inc(x_118);
x_122 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_122, 0, x_9);
lean_ctor_set(x_122, 1, x_118);
lean_ctor_set(x_122, 2, x_108);
x_123 = lean_array_uset(x_92, x_107, x_122);
x_124 = lean_unsigned_to_nat(4u);
x_125 = lean_nat_mul(x_121, x_124);
x_126 = lean_unsigned_to_nat(3u);
x_127 = lean_nat_div(x_125, x_126);
lean_dec(x_125);
x_128 = lean_array_get_size(x_123);
x_129 = lean_nat_dec_le(x_127, x_128);
lean_dec(x_128);
lean_dec(x_127);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_123);
lean_ctor_set(x_6, 1, x_130);
lean_ctor_set(x_6, 0, x_121);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_118);
lean_ctor_set(x_131, 1, x_6);
return x_131;
}
else
{
lean_object* x_132; 
lean_ctor_set(x_6, 1, x_123);
lean_ctor_set(x_6, 0, x_121);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_118);
lean_ctor_set(x_132, 1, x_6);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_box(0);
x_134 = lean_array_uset(x_92, x_107, x_133);
lean_inc(x_118);
x_135 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_118, x_108);
x_136 = lean_array_uset(x_134, x_107, x_135);
lean_ctor_set(x_6, 1, x_136);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_118);
lean_ctor_set(x_137, 1, x_6);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_dec(x_114);
x_138 = lean_nat_sub(x_113, x_5);
lean_dec(x_113);
x_139 = lean_nat_sub(x_2, x_138);
lean_dec(x_138);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_nat_sub(x_139, x_140);
lean_dec(x_139);
x_142 = lean_array_get_size(x_3);
x_143 = lean_nat_dec_lt(x_141, x_142);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_141);
x_144 = l_Lean_instInhabitedExpr;
x_145 = l_outOfBounds___rarg(x_144);
x_146 = lean_unsigned_to_nat(0u);
x_147 = lean_expr_lift_loose_bvars(x_145, x_146, x_5);
lean_dec(x_5);
lean_dec(x_145);
x_148 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_108);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_149 = lean_nat_add(x_91, x_140);
lean_dec(x_91);
lean_inc(x_147);
x_150 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_150, 0, x_9);
lean_ctor_set(x_150, 1, x_147);
lean_ctor_set(x_150, 2, x_108);
x_151 = lean_array_uset(x_92, x_107, x_150);
x_152 = lean_unsigned_to_nat(4u);
x_153 = lean_nat_mul(x_149, x_152);
x_154 = lean_unsigned_to_nat(3u);
x_155 = lean_nat_div(x_153, x_154);
lean_dec(x_153);
x_156 = lean_array_get_size(x_151);
x_157 = lean_nat_dec_le(x_155, x_156);
lean_dec(x_156);
lean_dec(x_155);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_151);
lean_ctor_set(x_6, 1, x_158);
lean_ctor_set(x_6, 0, x_149);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_147);
lean_ctor_set(x_159, 1, x_6);
return x_159;
}
else
{
lean_object* x_160; 
lean_ctor_set(x_6, 1, x_151);
lean_ctor_set(x_6, 0, x_149);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_147);
lean_ctor_set(x_160, 1, x_6);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_box(0);
x_162 = lean_array_uset(x_92, x_107, x_161);
lean_inc(x_147);
x_163 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_147, x_108);
x_164 = lean_array_uset(x_162, x_107, x_163);
lean_ctor_set(x_6, 1, x_164);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_147);
lean_ctor_set(x_165, 1, x_6);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_166 = lean_array_fget(x_3, x_141);
lean_dec(x_141);
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_expr_lift_loose_bvars(x_166, x_167, x_5);
lean_dec(x_5);
lean_dec(x_166);
x_169 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_108);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_170 = lean_nat_add(x_91, x_140);
lean_dec(x_91);
lean_inc(x_168);
x_171 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_171, 0, x_9);
lean_ctor_set(x_171, 1, x_168);
lean_ctor_set(x_171, 2, x_108);
x_172 = lean_array_uset(x_92, x_107, x_171);
x_173 = lean_unsigned_to_nat(4u);
x_174 = lean_nat_mul(x_170, x_173);
x_175 = lean_unsigned_to_nat(3u);
x_176 = lean_nat_div(x_174, x_175);
lean_dec(x_174);
x_177 = lean_array_get_size(x_172);
x_178 = lean_nat_dec_le(x_176, x_177);
lean_dec(x_177);
lean_dec(x_176);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_172);
lean_ctor_set(x_6, 1, x_179);
lean_ctor_set(x_6, 0, x_170);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_168);
lean_ctor_set(x_180, 1, x_6);
return x_180;
}
else
{
lean_object* x_181; 
lean_ctor_set(x_6, 1, x_172);
lean_ctor_set(x_6, 0, x_170);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_168);
lean_ctor_set(x_181, 1, x_6);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_182 = lean_box(0);
x_183 = lean_array_uset(x_92, x_107, x_182);
lean_inc(x_168);
x_184 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_168, x_108);
x_185 = lean_array_uset(x_183, x_107, x_184);
lean_ctor_set(x_6, 1, x_185);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_168);
lean_ctor_set(x_186, 1, x_6);
return x_186;
}
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
lean_dec(x_6);
x_187 = lean_ctor_get(x_4, 0);
lean_inc(x_187);
lean_dec(x_4);
x_188 = lean_nat_sub(x_2, x_1);
x_189 = lean_nat_add(x_5, x_188);
x_190 = lean_nat_dec_lt(x_187, x_189);
lean_dec(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; 
lean_dec(x_5);
x_191 = lean_nat_sub(x_187, x_188);
lean_dec(x_188);
lean_dec(x_187);
x_192 = l_Lean_Expr_bvar___override(x_191);
x_193 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_108);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_194 = lean_unsigned_to_nat(1u);
x_195 = lean_nat_add(x_91, x_194);
lean_dec(x_91);
lean_inc(x_192);
x_196 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_196, 0, x_9);
lean_ctor_set(x_196, 1, x_192);
lean_ctor_set(x_196, 2, x_108);
x_197 = lean_array_uset(x_92, x_107, x_196);
x_198 = lean_unsigned_to_nat(4u);
x_199 = lean_nat_mul(x_195, x_198);
x_200 = lean_unsigned_to_nat(3u);
x_201 = lean_nat_div(x_199, x_200);
lean_dec(x_199);
x_202 = lean_array_get_size(x_197);
x_203 = lean_nat_dec_le(x_201, x_202);
lean_dec(x_202);
lean_dec(x_201);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_197);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_195);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_192);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_195);
lean_ctor_set(x_207, 1, x_197);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_192);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_209 = lean_box(0);
x_210 = lean_array_uset(x_92, x_107, x_209);
lean_inc(x_192);
x_211 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_192, x_108);
x_212 = lean_array_uset(x_210, x_107, x_211);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_91);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_192);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
lean_dec(x_188);
x_215 = lean_nat_sub(x_187, x_5);
lean_dec(x_187);
x_216 = lean_nat_sub(x_2, x_215);
lean_dec(x_215);
x_217 = lean_unsigned_to_nat(1u);
x_218 = lean_nat_sub(x_216, x_217);
lean_dec(x_216);
x_219 = lean_array_get_size(x_3);
x_220 = lean_nat_dec_lt(x_218, x_219);
lean_dec(x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
lean_dec(x_218);
x_221 = l_Lean_instInhabitedExpr;
x_222 = l_outOfBounds___rarg(x_221);
x_223 = lean_unsigned_to_nat(0u);
x_224 = lean_expr_lift_loose_bvars(x_222, x_223, x_5);
lean_dec(x_5);
lean_dec(x_222);
x_225 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_108);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_226 = lean_nat_add(x_91, x_217);
lean_dec(x_91);
lean_inc(x_224);
x_227 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_227, 0, x_9);
lean_ctor_set(x_227, 1, x_224);
lean_ctor_set(x_227, 2, x_108);
x_228 = lean_array_uset(x_92, x_107, x_227);
x_229 = lean_unsigned_to_nat(4u);
x_230 = lean_nat_mul(x_226, x_229);
x_231 = lean_unsigned_to_nat(3u);
x_232 = lean_nat_div(x_230, x_231);
lean_dec(x_230);
x_233 = lean_array_get_size(x_228);
x_234 = lean_nat_dec_le(x_232, x_233);
lean_dec(x_233);
lean_dec(x_232);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_228);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_226);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_224);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_226);
lean_ctor_set(x_238, 1, x_228);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_224);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_240 = lean_box(0);
x_241 = lean_array_uset(x_92, x_107, x_240);
lean_inc(x_224);
x_242 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_224, x_108);
x_243 = lean_array_uset(x_241, x_107, x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_91);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_224);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_246 = lean_array_fget(x_3, x_218);
lean_dec(x_218);
x_247 = lean_unsigned_to_nat(0u);
x_248 = lean_expr_lift_loose_bvars(x_246, x_247, x_5);
lean_dec(x_5);
lean_dec(x_246);
x_249 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_108);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_250 = lean_nat_add(x_91, x_217);
lean_dec(x_91);
lean_inc(x_248);
x_251 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_251, 0, x_9);
lean_ctor_set(x_251, 1, x_248);
lean_ctor_set(x_251, 2, x_108);
x_252 = lean_array_uset(x_92, x_107, x_251);
x_253 = lean_unsigned_to_nat(4u);
x_254 = lean_nat_mul(x_250, x_253);
x_255 = lean_unsigned_to_nat(3u);
x_256 = lean_nat_div(x_254, x_255);
lean_dec(x_254);
x_257 = lean_array_get_size(x_252);
x_258 = lean_nat_dec_le(x_256, x_257);
lean_dec(x_257);
lean_dec(x_256);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_252);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_250);
lean_ctor_set(x_260, 1, x_259);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_248);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_250);
lean_ctor_set(x_262, 1, x_252);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_248);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_264 = lean_box(0);
x_265 = lean_array_uset(x_92, x_107, x_264);
lean_inc(x_248);
x_266 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_248, x_108);
x_267 = lean_array_uset(x_265, x_107, x_266);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_91);
lean_ctor_set(x_268, 1, x_267);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_248);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
}
}
case 1:
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_5);
lean_dec(x_4);
x_270 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__9;
x_271 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8(x_270, x_6);
x_272 = !lean_is_exclusive(x_271);
if (x_272 == 0)
{
lean_object* x_273; uint8_t x_274; 
x_273 = lean_ctor_get(x_271, 1);
x_274 = !lean_is_exclusive(x_273);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; size_t x_279; size_t x_280; size_t x_281; lean_object* x_282; uint8_t x_283; 
x_275 = lean_ctor_get(x_271, 0);
x_276 = lean_ctor_get(x_273, 0);
x_277 = lean_ctor_get(x_273, 1);
x_278 = lean_array_get_size(x_277);
x_279 = lean_usize_of_nat(x_278);
lean_dec(x_278);
x_280 = lean_usize_sub(x_279, x_105);
x_281 = lean_usize_land(x_103, x_280);
x_282 = lean_array_uget(x_277, x_281);
x_283 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_282);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_284 = lean_unsigned_to_nat(1u);
x_285 = lean_nat_add(x_276, x_284);
lean_dec(x_276);
lean_inc(x_275);
x_286 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_286, 0, x_9);
lean_ctor_set(x_286, 1, x_275);
lean_ctor_set(x_286, 2, x_282);
x_287 = lean_array_uset(x_277, x_281, x_286);
x_288 = lean_unsigned_to_nat(4u);
x_289 = lean_nat_mul(x_285, x_288);
x_290 = lean_unsigned_to_nat(3u);
x_291 = lean_nat_div(x_289, x_290);
lean_dec(x_289);
x_292 = lean_array_get_size(x_287);
x_293 = lean_nat_dec_le(x_291, x_292);
lean_dec(x_292);
lean_dec(x_291);
if (x_293 == 0)
{
lean_object* x_294; 
x_294 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_287);
lean_ctor_set(x_273, 1, x_294);
lean_ctor_set(x_273, 0, x_285);
return x_271;
}
else
{
lean_ctor_set(x_273, 1, x_287);
lean_ctor_set(x_273, 0, x_285);
return x_271;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_295 = lean_box(0);
x_296 = lean_array_uset(x_277, x_281, x_295);
lean_inc(x_275);
x_297 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_275, x_282);
x_298 = lean_array_uset(x_296, x_281, x_297);
lean_ctor_set(x_273, 1, x_298);
return x_271;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; size_t x_303; size_t x_304; size_t x_305; lean_object* x_306; uint8_t x_307; 
x_299 = lean_ctor_get(x_271, 0);
x_300 = lean_ctor_get(x_273, 0);
x_301 = lean_ctor_get(x_273, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_273);
x_302 = lean_array_get_size(x_301);
x_303 = lean_usize_of_nat(x_302);
lean_dec(x_302);
x_304 = lean_usize_sub(x_303, x_105);
x_305 = lean_usize_land(x_103, x_304);
x_306 = lean_array_uget(x_301, x_305);
x_307 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_306);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_308 = lean_unsigned_to_nat(1u);
x_309 = lean_nat_add(x_300, x_308);
lean_dec(x_300);
lean_inc(x_299);
x_310 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_310, 0, x_9);
lean_ctor_set(x_310, 1, x_299);
lean_ctor_set(x_310, 2, x_306);
x_311 = lean_array_uset(x_301, x_305, x_310);
x_312 = lean_unsigned_to_nat(4u);
x_313 = lean_nat_mul(x_309, x_312);
x_314 = lean_unsigned_to_nat(3u);
x_315 = lean_nat_div(x_313, x_314);
lean_dec(x_313);
x_316 = lean_array_get_size(x_311);
x_317 = lean_nat_dec_le(x_315, x_316);
lean_dec(x_316);
lean_dec(x_315);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; 
x_318 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_311);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_309);
lean_ctor_set(x_319, 1, x_318);
lean_ctor_set(x_271, 1, x_319);
return x_271;
}
else
{
lean_object* x_320; 
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_309);
lean_ctor_set(x_320, 1, x_311);
lean_ctor_set(x_271, 1, x_320);
return x_271;
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_321 = lean_box(0);
x_322 = lean_array_uset(x_301, x_305, x_321);
lean_inc(x_299);
x_323 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_299, x_306);
x_324 = lean_array_uset(x_322, x_305, x_323);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_300);
lean_ctor_set(x_325, 1, x_324);
lean_ctor_set(x_271, 1, x_325);
return x_271;
}
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; size_t x_332; size_t x_333; size_t x_334; lean_object* x_335; uint8_t x_336; 
x_326 = lean_ctor_get(x_271, 1);
x_327 = lean_ctor_get(x_271, 0);
lean_inc(x_326);
lean_inc(x_327);
lean_dec(x_271);
x_328 = lean_ctor_get(x_326, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_326, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_330 = x_326;
} else {
 lean_dec_ref(x_326);
 x_330 = lean_box(0);
}
x_331 = lean_array_get_size(x_329);
x_332 = lean_usize_of_nat(x_331);
lean_dec(x_331);
x_333 = lean_usize_sub(x_332, x_105);
x_334 = lean_usize_land(x_103, x_333);
x_335 = lean_array_uget(x_329, x_334);
x_336 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_335);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_337 = lean_unsigned_to_nat(1u);
x_338 = lean_nat_add(x_328, x_337);
lean_dec(x_328);
lean_inc(x_327);
x_339 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_339, 0, x_9);
lean_ctor_set(x_339, 1, x_327);
lean_ctor_set(x_339, 2, x_335);
x_340 = lean_array_uset(x_329, x_334, x_339);
x_341 = lean_unsigned_to_nat(4u);
x_342 = lean_nat_mul(x_338, x_341);
x_343 = lean_unsigned_to_nat(3u);
x_344 = lean_nat_div(x_342, x_343);
lean_dec(x_342);
x_345 = lean_array_get_size(x_340);
x_346 = lean_nat_dec_le(x_344, x_345);
lean_dec(x_345);
lean_dec(x_344);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_340);
if (lean_is_scalar(x_330)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_330;
}
lean_ctor_set(x_348, 0, x_338);
lean_ctor_set(x_348, 1, x_347);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_327);
lean_ctor_set(x_349, 1, x_348);
return x_349;
}
else
{
lean_object* x_350; lean_object* x_351; 
if (lean_is_scalar(x_330)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_330;
}
lean_ctor_set(x_350, 0, x_338);
lean_ctor_set(x_350, 1, x_340);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_327);
lean_ctor_set(x_351, 1, x_350);
return x_351;
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_352 = lean_box(0);
x_353 = lean_array_uset(x_329, x_334, x_352);
lean_inc(x_327);
x_354 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_327, x_335);
x_355 = lean_array_uset(x_353, x_334, x_354);
if (lean_is_scalar(x_330)) {
 x_356 = lean_alloc_ctor(0, 2, 0);
} else {
 x_356 = x_330;
}
lean_ctor_set(x_356, 0, x_328);
lean_ctor_set(x_356, 1, x_355);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_327);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
}
}
case 2:
{
lean_object* x_358; lean_object* x_359; uint8_t x_360; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_5);
lean_dec(x_4);
x_358 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__10;
x_359 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8(x_358, x_6);
x_360 = !lean_is_exclusive(x_359);
if (x_360 == 0)
{
lean_object* x_361; uint8_t x_362; 
x_361 = lean_ctor_get(x_359, 1);
x_362 = !lean_is_exclusive(x_361);
if (x_362 == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; size_t x_367; size_t x_368; size_t x_369; lean_object* x_370; uint8_t x_371; 
x_363 = lean_ctor_get(x_359, 0);
x_364 = lean_ctor_get(x_361, 0);
x_365 = lean_ctor_get(x_361, 1);
x_366 = lean_array_get_size(x_365);
x_367 = lean_usize_of_nat(x_366);
lean_dec(x_366);
x_368 = lean_usize_sub(x_367, x_105);
x_369 = lean_usize_land(x_103, x_368);
x_370 = lean_array_uget(x_365, x_369);
x_371 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_370);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; 
x_372 = lean_unsigned_to_nat(1u);
x_373 = lean_nat_add(x_364, x_372);
lean_dec(x_364);
lean_inc(x_363);
x_374 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_374, 0, x_9);
lean_ctor_set(x_374, 1, x_363);
lean_ctor_set(x_374, 2, x_370);
x_375 = lean_array_uset(x_365, x_369, x_374);
x_376 = lean_unsigned_to_nat(4u);
x_377 = lean_nat_mul(x_373, x_376);
x_378 = lean_unsigned_to_nat(3u);
x_379 = lean_nat_div(x_377, x_378);
lean_dec(x_377);
x_380 = lean_array_get_size(x_375);
x_381 = lean_nat_dec_le(x_379, x_380);
lean_dec(x_380);
lean_dec(x_379);
if (x_381 == 0)
{
lean_object* x_382; 
x_382 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_375);
lean_ctor_set(x_361, 1, x_382);
lean_ctor_set(x_361, 0, x_373);
return x_359;
}
else
{
lean_ctor_set(x_361, 1, x_375);
lean_ctor_set(x_361, 0, x_373);
return x_359;
}
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_383 = lean_box(0);
x_384 = lean_array_uset(x_365, x_369, x_383);
lean_inc(x_363);
x_385 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_363, x_370);
x_386 = lean_array_uset(x_384, x_369, x_385);
lean_ctor_set(x_361, 1, x_386);
return x_359;
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; size_t x_391; size_t x_392; size_t x_393; lean_object* x_394; uint8_t x_395; 
x_387 = lean_ctor_get(x_359, 0);
x_388 = lean_ctor_get(x_361, 0);
x_389 = lean_ctor_get(x_361, 1);
lean_inc(x_389);
lean_inc(x_388);
lean_dec(x_361);
x_390 = lean_array_get_size(x_389);
x_391 = lean_usize_of_nat(x_390);
lean_dec(x_390);
x_392 = lean_usize_sub(x_391, x_105);
x_393 = lean_usize_land(x_103, x_392);
x_394 = lean_array_uget(x_389, x_393);
x_395 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_394);
if (x_395 == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; 
x_396 = lean_unsigned_to_nat(1u);
x_397 = lean_nat_add(x_388, x_396);
lean_dec(x_388);
lean_inc(x_387);
x_398 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_398, 0, x_9);
lean_ctor_set(x_398, 1, x_387);
lean_ctor_set(x_398, 2, x_394);
x_399 = lean_array_uset(x_389, x_393, x_398);
x_400 = lean_unsigned_to_nat(4u);
x_401 = lean_nat_mul(x_397, x_400);
x_402 = lean_unsigned_to_nat(3u);
x_403 = lean_nat_div(x_401, x_402);
lean_dec(x_401);
x_404 = lean_array_get_size(x_399);
x_405 = lean_nat_dec_le(x_403, x_404);
lean_dec(x_404);
lean_dec(x_403);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; 
x_406 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_399);
x_407 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_407, 0, x_397);
lean_ctor_set(x_407, 1, x_406);
lean_ctor_set(x_359, 1, x_407);
return x_359;
}
else
{
lean_object* x_408; 
x_408 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_408, 0, x_397);
lean_ctor_set(x_408, 1, x_399);
lean_ctor_set(x_359, 1, x_408);
return x_359;
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_409 = lean_box(0);
x_410 = lean_array_uset(x_389, x_393, x_409);
lean_inc(x_387);
x_411 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_387, x_394);
x_412 = lean_array_uset(x_410, x_393, x_411);
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_388);
lean_ctor_set(x_413, 1, x_412);
lean_ctor_set(x_359, 1, x_413);
return x_359;
}
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; size_t x_420; size_t x_421; size_t x_422; lean_object* x_423; uint8_t x_424; 
x_414 = lean_ctor_get(x_359, 1);
x_415 = lean_ctor_get(x_359, 0);
lean_inc(x_414);
lean_inc(x_415);
lean_dec(x_359);
x_416 = lean_ctor_get(x_414, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_414, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_418 = x_414;
} else {
 lean_dec_ref(x_414);
 x_418 = lean_box(0);
}
x_419 = lean_array_get_size(x_417);
x_420 = lean_usize_of_nat(x_419);
lean_dec(x_419);
x_421 = lean_usize_sub(x_420, x_105);
x_422 = lean_usize_land(x_103, x_421);
x_423 = lean_array_uget(x_417, x_422);
x_424 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_423);
if (x_424 == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; 
x_425 = lean_unsigned_to_nat(1u);
x_426 = lean_nat_add(x_416, x_425);
lean_dec(x_416);
lean_inc(x_415);
x_427 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_427, 0, x_9);
lean_ctor_set(x_427, 1, x_415);
lean_ctor_set(x_427, 2, x_423);
x_428 = lean_array_uset(x_417, x_422, x_427);
x_429 = lean_unsigned_to_nat(4u);
x_430 = lean_nat_mul(x_426, x_429);
x_431 = lean_unsigned_to_nat(3u);
x_432 = lean_nat_div(x_430, x_431);
lean_dec(x_430);
x_433 = lean_array_get_size(x_428);
x_434 = lean_nat_dec_le(x_432, x_433);
lean_dec(x_433);
lean_dec(x_432);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_428);
if (lean_is_scalar(x_418)) {
 x_436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_436 = x_418;
}
lean_ctor_set(x_436, 0, x_426);
lean_ctor_set(x_436, 1, x_435);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_415);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_439; 
if (lean_is_scalar(x_418)) {
 x_438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_438 = x_418;
}
lean_ctor_set(x_438, 0, x_426);
lean_ctor_set(x_438, 1, x_428);
x_439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_439, 0, x_415);
lean_ctor_set(x_439, 1, x_438);
return x_439;
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_440 = lean_box(0);
x_441 = lean_array_uset(x_417, x_422, x_440);
lean_inc(x_415);
x_442 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_415, x_423);
x_443 = lean_array_uset(x_441, x_422, x_442);
if (lean_is_scalar(x_418)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_418;
}
lean_ctor_set(x_444, 0, x_416);
lean_ctor_set(x_444, 1, x_443);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_415);
lean_ctor_set(x_445, 1, x_444);
return x_445;
}
}
}
case 3:
{
lean_object* x_446; lean_object* x_447; uint8_t x_448; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_5);
lean_dec(x_4);
x_446 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__11;
x_447 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8(x_446, x_6);
x_448 = !lean_is_exclusive(x_447);
if (x_448 == 0)
{
lean_object* x_449; uint8_t x_450; 
x_449 = lean_ctor_get(x_447, 1);
x_450 = !lean_is_exclusive(x_449);
if (x_450 == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; size_t x_455; size_t x_456; size_t x_457; lean_object* x_458; uint8_t x_459; 
x_451 = lean_ctor_get(x_447, 0);
x_452 = lean_ctor_get(x_449, 0);
x_453 = lean_ctor_get(x_449, 1);
x_454 = lean_array_get_size(x_453);
x_455 = lean_usize_of_nat(x_454);
lean_dec(x_454);
x_456 = lean_usize_sub(x_455, x_105);
x_457 = lean_usize_land(x_103, x_456);
x_458 = lean_array_uget(x_453, x_457);
x_459 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_458);
if (x_459 == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; 
x_460 = lean_unsigned_to_nat(1u);
x_461 = lean_nat_add(x_452, x_460);
lean_dec(x_452);
lean_inc(x_451);
x_462 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_462, 0, x_9);
lean_ctor_set(x_462, 1, x_451);
lean_ctor_set(x_462, 2, x_458);
x_463 = lean_array_uset(x_453, x_457, x_462);
x_464 = lean_unsigned_to_nat(4u);
x_465 = lean_nat_mul(x_461, x_464);
x_466 = lean_unsigned_to_nat(3u);
x_467 = lean_nat_div(x_465, x_466);
lean_dec(x_465);
x_468 = lean_array_get_size(x_463);
x_469 = lean_nat_dec_le(x_467, x_468);
lean_dec(x_468);
lean_dec(x_467);
if (x_469 == 0)
{
lean_object* x_470; 
x_470 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_463);
lean_ctor_set(x_449, 1, x_470);
lean_ctor_set(x_449, 0, x_461);
return x_447;
}
else
{
lean_ctor_set(x_449, 1, x_463);
lean_ctor_set(x_449, 0, x_461);
return x_447;
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_471 = lean_box(0);
x_472 = lean_array_uset(x_453, x_457, x_471);
lean_inc(x_451);
x_473 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_451, x_458);
x_474 = lean_array_uset(x_472, x_457, x_473);
lean_ctor_set(x_449, 1, x_474);
return x_447;
}
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; size_t x_479; size_t x_480; size_t x_481; lean_object* x_482; uint8_t x_483; 
x_475 = lean_ctor_get(x_447, 0);
x_476 = lean_ctor_get(x_449, 0);
x_477 = lean_ctor_get(x_449, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_449);
x_478 = lean_array_get_size(x_477);
x_479 = lean_usize_of_nat(x_478);
lean_dec(x_478);
x_480 = lean_usize_sub(x_479, x_105);
x_481 = lean_usize_land(x_103, x_480);
x_482 = lean_array_uget(x_477, x_481);
x_483 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_482);
if (x_483 == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; uint8_t x_493; 
x_484 = lean_unsigned_to_nat(1u);
x_485 = lean_nat_add(x_476, x_484);
lean_dec(x_476);
lean_inc(x_475);
x_486 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_486, 0, x_9);
lean_ctor_set(x_486, 1, x_475);
lean_ctor_set(x_486, 2, x_482);
x_487 = lean_array_uset(x_477, x_481, x_486);
x_488 = lean_unsigned_to_nat(4u);
x_489 = lean_nat_mul(x_485, x_488);
x_490 = lean_unsigned_to_nat(3u);
x_491 = lean_nat_div(x_489, x_490);
lean_dec(x_489);
x_492 = lean_array_get_size(x_487);
x_493 = lean_nat_dec_le(x_491, x_492);
lean_dec(x_492);
lean_dec(x_491);
if (x_493 == 0)
{
lean_object* x_494; lean_object* x_495; 
x_494 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_487);
x_495 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_495, 0, x_485);
lean_ctor_set(x_495, 1, x_494);
lean_ctor_set(x_447, 1, x_495);
return x_447;
}
else
{
lean_object* x_496; 
x_496 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_496, 0, x_485);
lean_ctor_set(x_496, 1, x_487);
lean_ctor_set(x_447, 1, x_496);
return x_447;
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_497 = lean_box(0);
x_498 = lean_array_uset(x_477, x_481, x_497);
lean_inc(x_475);
x_499 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_475, x_482);
x_500 = lean_array_uset(x_498, x_481, x_499);
x_501 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_501, 0, x_476);
lean_ctor_set(x_501, 1, x_500);
lean_ctor_set(x_447, 1, x_501);
return x_447;
}
}
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; size_t x_508; size_t x_509; size_t x_510; lean_object* x_511; uint8_t x_512; 
x_502 = lean_ctor_get(x_447, 1);
x_503 = lean_ctor_get(x_447, 0);
lean_inc(x_502);
lean_inc(x_503);
lean_dec(x_447);
x_504 = lean_ctor_get(x_502, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_502, 1);
lean_inc(x_505);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 x_506 = x_502;
} else {
 lean_dec_ref(x_502);
 x_506 = lean_box(0);
}
x_507 = lean_array_get_size(x_505);
x_508 = lean_usize_of_nat(x_507);
lean_dec(x_507);
x_509 = lean_usize_sub(x_508, x_105);
x_510 = lean_usize_land(x_103, x_509);
x_511 = lean_array_uget(x_505, x_510);
x_512 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_511);
if (x_512 == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; 
x_513 = lean_unsigned_to_nat(1u);
x_514 = lean_nat_add(x_504, x_513);
lean_dec(x_504);
lean_inc(x_503);
x_515 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_515, 0, x_9);
lean_ctor_set(x_515, 1, x_503);
lean_ctor_set(x_515, 2, x_511);
x_516 = lean_array_uset(x_505, x_510, x_515);
x_517 = lean_unsigned_to_nat(4u);
x_518 = lean_nat_mul(x_514, x_517);
x_519 = lean_unsigned_to_nat(3u);
x_520 = lean_nat_div(x_518, x_519);
lean_dec(x_518);
x_521 = lean_array_get_size(x_516);
x_522 = lean_nat_dec_le(x_520, x_521);
lean_dec(x_521);
lean_dec(x_520);
if (x_522 == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_523 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_516);
if (lean_is_scalar(x_506)) {
 x_524 = lean_alloc_ctor(0, 2, 0);
} else {
 x_524 = x_506;
}
lean_ctor_set(x_524, 0, x_514);
lean_ctor_set(x_524, 1, x_523);
x_525 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_525, 0, x_503);
lean_ctor_set(x_525, 1, x_524);
return x_525;
}
else
{
lean_object* x_526; lean_object* x_527; 
if (lean_is_scalar(x_506)) {
 x_526 = lean_alloc_ctor(0, 2, 0);
} else {
 x_526 = x_506;
}
lean_ctor_set(x_526, 0, x_514);
lean_ctor_set(x_526, 1, x_516);
x_527 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_527, 0, x_503);
lean_ctor_set(x_527, 1, x_526);
return x_527;
}
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_528 = lean_box(0);
x_529 = lean_array_uset(x_505, x_510, x_528);
lean_inc(x_503);
x_530 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_503, x_511);
x_531 = lean_array_uset(x_529, x_510, x_530);
if (lean_is_scalar(x_506)) {
 x_532 = lean_alloc_ctor(0, 2, 0);
} else {
 x_532 = x_506;
}
lean_ctor_set(x_532, 0, x_504);
lean_ctor_set(x_532, 1, x_531);
x_533 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_533, 0, x_503);
lean_ctor_set(x_533, 1, x_532);
return x_533;
}
}
}
case 4:
{
lean_object* x_534; lean_object* x_535; uint8_t x_536; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_5);
lean_dec(x_4);
x_534 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__12;
x_535 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8(x_534, x_6);
x_536 = !lean_is_exclusive(x_535);
if (x_536 == 0)
{
lean_object* x_537; uint8_t x_538; 
x_537 = lean_ctor_get(x_535, 1);
x_538 = !lean_is_exclusive(x_537);
if (x_538 == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; size_t x_543; size_t x_544; size_t x_545; lean_object* x_546; uint8_t x_547; 
x_539 = lean_ctor_get(x_535, 0);
x_540 = lean_ctor_get(x_537, 0);
x_541 = lean_ctor_get(x_537, 1);
x_542 = lean_array_get_size(x_541);
x_543 = lean_usize_of_nat(x_542);
lean_dec(x_542);
x_544 = lean_usize_sub(x_543, x_105);
x_545 = lean_usize_land(x_103, x_544);
x_546 = lean_array_uget(x_541, x_545);
x_547 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_546);
if (x_547 == 0)
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; uint8_t x_557; 
x_548 = lean_unsigned_to_nat(1u);
x_549 = lean_nat_add(x_540, x_548);
lean_dec(x_540);
lean_inc(x_539);
x_550 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_550, 0, x_9);
lean_ctor_set(x_550, 1, x_539);
lean_ctor_set(x_550, 2, x_546);
x_551 = lean_array_uset(x_541, x_545, x_550);
x_552 = lean_unsigned_to_nat(4u);
x_553 = lean_nat_mul(x_549, x_552);
x_554 = lean_unsigned_to_nat(3u);
x_555 = lean_nat_div(x_553, x_554);
lean_dec(x_553);
x_556 = lean_array_get_size(x_551);
x_557 = lean_nat_dec_le(x_555, x_556);
lean_dec(x_556);
lean_dec(x_555);
if (x_557 == 0)
{
lean_object* x_558; 
x_558 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_551);
lean_ctor_set(x_537, 1, x_558);
lean_ctor_set(x_537, 0, x_549);
return x_535;
}
else
{
lean_ctor_set(x_537, 1, x_551);
lean_ctor_set(x_537, 0, x_549);
return x_535;
}
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_559 = lean_box(0);
x_560 = lean_array_uset(x_541, x_545, x_559);
lean_inc(x_539);
x_561 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_539, x_546);
x_562 = lean_array_uset(x_560, x_545, x_561);
lean_ctor_set(x_537, 1, x_562);
return x_535;
}
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; size_t x_567; size_t x_568; size_t x_569; lean_object* x_570; uint8_t x_571; 
x_563 = lean_ctor_get(x_535, 0);
x_564 = lean_ctor_get(x_537, 0);
x_565 = lean_ctor_get(x_537, 1);
lean_inc(x_565);
lean_inc(x_564);
lean_dec(x_537);
x_566 = lean_array_get_size(x_565);
x_567 = lean_usize_of_nat(x_566);
lean_dec(x_566);
x_568 = lean_usize_sub(x_567, x_105);
x_569 = lean_usize_land(x_103, x_568);
x_570 = lean_array_uget(x_565, x_569);
x_571 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_570);
if (x_571 == 0)
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; uint8_t x_581; 
x_572 = lean_unsigned_to_nat(1u);
x_573 = lean_nat_add(x_564, x_572);
lean_dec(x_564);
lean_inc(x_563);
x_574 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_574, 0, x_9);
lean_ctor_set(x_574, 1, x_563);
lean_ctor_set(x_574, 2, x_570);
x_575 = lean_array_uset(x_565, x_569, x_574);
x_576 = lean_unsigned_to_nat(4u);
x_577 = lean_nat_mul(x_573, x_576);
x_578 = lean_unsigned_to_nat(3u);
x_579 = lean_nat_div(x_577, x_578);
lean_dec(x_577);
x_580 = lean_array_get_size(x_575);
x_581 = lean_nat_dec_le(x_579, x_580);
lean_dec(x_580);
lean_dec(x_579);
if (x_581 == 0)
{
lean_object* x_582; lean_object* x_583; 
x_582 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_575);
x_583 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_583, 0, x_573);
lean_ctor_set(x_583, 1, x_582);
lean_ctor_set(x_535, 1, x_583);
return x_535;
}
else
{
lean_object* x_584; 
x_584 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_584, 0, x_573);
lean_ctor_set(x_584, 1, x_575);
lean_ctor_set(x_535, 1, x_584);
return x_535;
}
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_585 = lean_box(0);
x_586 = lean_array_uset(x_565, x_569, x_585);
lean_inc(x_563);
x_587 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_563, x_570);
x_588 = lean_array_uset(x_586, x_569, x_587);
x_589 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_589, 0, x_564);
lean_ctor_set(x_589, 1, x_588);
lean_ctor_set(x_535, 1, x_589);
return x_535;
}
}
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; size_t x_596; size_t x_597; size_t x_598; lean_object* x_599; uint8_t x_600; 
x_590 = lean_ctor_get(x_535, 1);
x_591 = lean_ctor_get(x_535, 0);
lean_inc(x_590);
lean_inc(x_591);
lean_dec(x_535);
x_592 = lean_ctor_get(x_590, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_590, 1);
lean_inc(x_593);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 lean_ctor_release(x_590, 1);
 x_594 = x_590;
} else {
 lean_dec_ref(x_590);
 x_594 = lean_box(0);
}
x_595 = lean_array_get_size(x_593);
x_596 = lean_usize_of_nat(x_595);
lean_dec(x_595);
x_597 = lean_usize_sub(x_596, x_105);
x_598 = lean_usize_land(x_103, x_597);
x_599 = lean_array_uget(x_593, x_598);
x_600 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_599);
if (x_600 == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; 
x_601 = lean_unsigned_to_nat(1u);
x_602 = lean_nat_add(x_592, x_601);
lean_dec(x_592);
lean_inc(x_591);
x_603 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_603, 0, x_9);
lean_ctor_set(x_603, 1, x_591);
lean_ctor_set(x_603, 2, x_599);
x_604 = lean_array_uset(x_593, x_598, x_603);
x_605 = lean_unsigned_to_nat(4u);
x_606 = lean_nat_mul(x_602, x_605);
x_607 = lean_unsigned_to_nat(3u);
x_608 = lean_nat_div(x_606, x_607);
lean_dec(x_606);
x_609 = lean_array_get_size(x_604);
x_610 = lean_nat_dec_le(x_608, x_609);
lean_dec(x_609);
lean_dec(x_608);
if (x_610 == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_611 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_604);
if (lean_is_scalar(x_594)) {
 x_612 = lean_alloc_ctor(0, 2, 0);
} else {
 x_612 = x_594;
}
lean_ctor_set(x_612, 0, x_602);
lean_ctor_set(x_612, 1, x_611);
x_613 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_613, 0, x_591);
lean_ctor_set(x_613, 1, x_612);
return x_613;
}
else
{
lean_object* x_614; lean_object* x_615; 
if (lean_is_scalar(x_594)) {
 x_614 = lean_alloc_ctor(0, 2, 0);
} else {
 x_614 = x_594;
}
lean_ctor_set(x_614, 0, x_602);
lean_ctor_set(x_614, 1, x_604);
x_615 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_615, 0, x_591);
lean_ctor_set(x_615, 1, x_614);
return x_615;
}
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_616 = lean_box(0);
x_617 = lean_array_uset(x_593, x_598, x_616);
lean_inc(x_591);
x_618 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_591, x_599);
x_619 = lean_array_uset(x_617, x_598, x_618);
if (lean_is_scalar(x_594)) {
 x_620 = lean_alloc_ctor(0, 2, 0);
} else {
 x_620 = x_594;
}
lean_ctor_set(x_620, 0, x_592);
lean_ctor_set(x_620, 1, x_619);
x_621 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_621, 0, x_591);
lean_ctor_set(x_621, 1, x_620);
return x_621;
}
}
}
case 5:
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; uint8_t x_628; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
x_622 = lean_unsigned_to_nat(0u);
x_623 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_4, x_622);
x_624 = lean_mk_empty_array_with_capacity(x_623);
lean_dec(x_623);
x_625 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__3;
x_626 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__5;
x_627 = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10(x_1, x_2, x_3, x_5, x_625, x_626, x_4, x_624, x_6);
x_628 = !lean_is_exclusive(x_627);
if (x_628 == 0)
{
lean_object* x_629; uint8_t x_630; 
x_629 = lean_ctor_get(x_627, 1);
x_630 = !lean_is_exclusive(x_629);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; size_t x_635; size_t x_636; size_t x_637; lean_object* x_638; uint8_t x_639; 
x_631 = lean_ctor_get(x_627, 0);
x_632 = lean_ctor_get(x_629, 0);
x_633 = lean_ctor_get(x_629, 1);
x_634 = lean_array_get_size(x_633);
x_635 = lean_usize_of_nat(x_634);
lean_dec(x_634);
x_636 = lean_usize_sub(x_635, x_105);
x_637 = lean_usize_land(x_103, x_636);
x_638 = lean_array_uget(x_633, x_637);
x_639 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_638);
if (x_639 == 0)
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_649; 
x_640 = lean_unsigned_to_nat(1u);
x_641 = lean_nat_add(x_632, x_640);
lean_dec(x_632);
lean_inc(x_631);
x_642 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_642, 0, x_9);
lean_ctor_set(x_642, 1, x_631);
lean_ctor_set(x_642, 2, x_638);
x_643 = lean_array_uset(x_633, x_637, x_642);
x_644 = lean_unsigned_to_nat(4u);
x_645 = lean_nat_mul(x_641, x_644);
x_646 = lean_unsigned_to_nat(3u);
x_647 = lean_nat_div(x_645, x_646);
lean_dec(x_645);
x_648 = lean_array_get_size(x_643);
x_649 = lean_nat_dec_le(x_647, x_648);
lean_dec(x_648);
lean_dec(x_647);
if (x_649 == 0)
{
lean_object* x_650; 
x_650 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_643);
lean_ctor_set(x_629, 1, x_650);
lean_ctor_set(x_629, 0, x_641);
return x_627;
}
else
{
lean_ctor_set(x_629, 1, x_643);
lean_ctor_set(x_629, 0, x_641);
return x_627;
}
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_651 = lean_box(0);
x_652 = lean_array_uset(x_633, x_637, x_651);
lean_inc(x_631);
x_653 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_631, x_638);
x_654 = lean_array_uset(x_652, x_637, x_653);
lean_ctor_set(x_629, 1, x_654);
return x_627;
}
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; size_t x_659; size_t x_660; size_t x_661; lean_object* x_662; uint8_t x_663; 
x_655 = lean_ctor_get(x_627, 0);
x_656 = lean_ctor_get(x_629, 0);
x_657 = lean_ctor_get(x_629, 1);
lean_inc(x_657);
lean_inc(x_656);
lean_dec(x_629);
x_658 = lean_array_get_size(x_657);
x_659 = lean_usize_of_nat(x_658);
lean_dec(x_658);
x_660 = lean_usize_sub(x_659, x_105);
x_661 = lean_usize_land(x_103, x_660);
x_662 = lean_array_uget(x_657, x_661);
x_663 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_662);
if (x_663 == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; uint8_t x_673; 
x_664 = lean_unsigned_to_nat(1u);
x_665 = lean_nat_add(x_656, x_664);
lean_dec(x_656);
lean_inc(x_655);
x_666 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_666, 0, x_9);
lean_ctor_set(x_666, 1, x_655);
lean_ctor_set(x_666, 2, x_662);
x_667 = lean_array_uset(x_657, x_661, x_666);
x_668 = lean_unsigned_to_nat(4u);
x_669 = lean_nat_mul(x_665, x_668);
x_670 = lean_unsigned_to_nat(3u);
x_671 = lean_nat_div(x_669, x_670);
lean_dec(x_669);
x_672 = lean_array_get_size(x_667);
x_673 = lean_nat_dec_le(x_671, x_672);
lean_dec(x_672);
lean_dec(x_671);
if (x_673 == 0)
{
lean_object* x_674; lean_object* x_675; 
x_674 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_667);
x_675 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_675, 0, x_665);
lean_ctor_set(x_675, 1, x_674);
lean_ctor_set(x_627, 1, x_675);
return x_627;
}
else
{
lean_object* x_676; 
x_676 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_676, 0, x_665);
lean_ctor_set(x_676, 1, x_667);
lean_ctor_set(x_627, 1, x_676);
return x_627;
}
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; 
x_677 = lean_box(0);
x_678 = lean_array_uset(x_657, x_661, x_677);
lean_inc(x_655);
x_679 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_655, x_662);
x_680 = lean_array_uset(x_678, x_661, x_679);
x_681 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_681, 0, x_656);
lean_ctor_set(x_681, 1, x_680);
lean_ctor_set(x_627, 1, x_681);
return x_627;
}
}
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; size_t x_688; size_t x_689; size_t x_690; lean_object* x_691; uint8_t x_692; 
x_682 = lean_ctor_get(x_627, 1);
x_683 = lean_ctor_get(x_627, 0);
lean_inc(x_682);
lean_inc(x_683);
lean_dec(x_627);
x_684 = lean_ctor_get(x_682, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_682, 1);
lean_inc(x_685);
if (lean_is_exclusive(x_682)) {
 lean_ctor_release(x_682, 0);
 lean_ctor_release(x_682, 1);
 x_686 = x_682;
} else {
 lean_dec_ref(x_682);
 x_686 = lean_box(0);
}
x_687 = lean_array_get_size(x_685);
x_688 = lean_usize_of_nat(x_687);
lean_dec(x_687);
x_689 = lean_usize_sub(x_688, x_105);
x_690 = lean_usize_land(x_103, x_689);
x_691 = lean_array_uget(x_685, x_690);
x_692 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_691);
if (x_692 == 0)
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; 
x_693 = lean_unsigned_to_nat(1u);
x_694 = lean_nat_add(x_684, x_693);
lean_dec(x_684);
lean_inc(x_683);
x_695 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_695, 0, x_9);
lean_ctor_set(x_695, 1, x_683);
lean_ctor_set(x_695, 2, x_691);
x_696 = lean_array_uset(x_685, x_690, x_695);
x_697 = lean_unsigned_to_nat(4u);
x_698 = lean_nat_mul(x_694, x_697);
x_699 = lean_unsigned_to_nat(3u);
x_700 = lean_nat_div(x_698, x_699);
lean_dec(x_698);
x_701 = lean_array_get_size(x_696);
x_702 = lean_nat_dec_le(x_700, x_701);
lean_dec(x_701);
lean_dec(x_700);
if (x_702 == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; 
x_703 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_696);
if (lean_is_scalar(x_686)) {
 x_704 = lean_alloc_ctor(0, 2, 0);
} else {
 x_704 = x_686;
}
lean_ctor_set(x_704, 0, x_694);
lean_ctor_set(x_704, 1, x_703);
x_705 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_705, 0, x_683);
lean_ctor_set(x_705, 1, x_704);
return x_705;
}
else
{
lean_object* x_706; lean_object* x_707; 
if (lean_is_scalar(x_686)) {
 x_706 = lean_alloc_ctor(0, 2, 0);
} else {
 x_706 = x_686;
}
lean_ctor_set(x_706, 0, x_694);
lean_ctor_set(x_706, 1, x_696);
x_707 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_707, 0, x_683);
lean_ctor_set(x_707, 1, x_706);
return x_707;
}
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_708 = lean_box(0);
x_709 = lean_array_uset(x_685, x_690, x_708);
lean_inc(x_683);
x_710 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_683, x_691);
x_711 = lean_array_uset(x_709, x_690, x_710);
if (lean_is_scalar(x_686)) {
 x_712 = lean_alloc_ctor(0, 2, 0);
} else {
 x_712 = x_686;
}
lean_ctor_set(x_712, 0, x_684);
lean_ctor_set(x_712, 1, x_711);
x_713 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_713, 0, x_683);
lean_ctor_set(x_713, 1, x_712);
return x_713;
}
}
}
case 6:
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; uint8_t x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; size_t x_727; size_t x_728; uint8_t x_729; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
x_714 = lean_ctor_get(x_4, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_4, 1);
lean_inc(x_715);
x_716 = lean_ctor_get(x_4, 2);
lean_inc(x_716);
x_717 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
lean_inc(x_5);
lean_inc(x_715);
x_718 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_715, x_5, x_6);
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_718, 1);
lean_inc(x_720);
lean_dec(x_718);
x_721 = lean_unsigned_to_nat(1u);
x_722 = lean_nat_add(x_5, x_721);
lean_inc(x_716);
x_723 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_716, x_722, x_720);
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_723, 1);
lean_inc(x_725);
lean_dec(x_723);
lean_inc(x_716);
lean_inc(x_715);
lean_inc(x_714);
x_726 = l_Lean_Expr_lam___override(x_714, x_715, x_716, x_717);
x_727 = lean_ptr_addr(x_715);
lean_dec(x_715);
x_728 = lean_ptr_addr(x_719);
x_729 = lean_usize_dec_eq(x_727, x_728);
if (x_729 == 0)
{
lean_object* x_730; 
lean_dec(x_726);
lean_dec(x_716);
x_730 = l_Lean_Expr_lam___override(x_714, x_719, x_724, x_717);
x_10 = x_730;
x_11 = x_725;
goto block_90;
}
else
{
size_t x_731; size_t x_732; uint8_t x_733; 
x_731 = lean_ptr_addr(x_716);
lean_dec(x_716);
x_732 = lean_ptr_addr(x_724);
x_733 = lean_usize_dec_eq(x_731, x_732);
if (x_733 == 0)
{
lean_object* x_734; 
lean_dec(x_726);
x_734 = l_Lean_Expr_lam___override(x_714, x_719, x_724, x_717);
x_10 = x_734;
x_11 = x_725;
goto block_90;
}
else
{
uint8_t x_735; 
x_735 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_717, x_717);
if (x_735 == 0)
{
lean_object* x_736; 
lean_dec(x_726);
x_736 = l_Lean_Expr_lam___override(x_714, x_719, x_724, x_717);
x_10 = x_736;
x_11 = x_725;
goto block_90;
}
else
{
lean_dec(x_724);
lean_dec(x_719);
lean_dec(x_714);
x_10 = x_726;
x_11 = x_725;
goto block_90;
}
}
}
}
case 7:
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; uint8_t x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; size_t x_750; size_t x_751; uint8_t x_752; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
x_737 = lean_ctor_get(x_4, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_4, 1);
lean_inc(x_738);
x_739 = lean_ctor_get(x_4, 2);
lean_inc(x_739);
x_740 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
lean_inc(x_5);
lean_inc(x_738);
x_741 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_738, x_5, x_6);
x_742 = lean_ctor_get(x_741, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_741, 1);
lean_inc(x_743);
lean_dec(x_741);
x_744 = lean_unsigned_to_nat(1u);
x_745 = lean_nat_add(x_5, x_744);
lean_inc(x_739);
x_746 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_739, x_745, x_743);
x_747 = lean_ctor_get(x_746, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_746, 1);
lean_inc(x_748);
lean_dec(x_746);
lean_inc(x_739);
lean_inc(x_738);
lean_inc(x_737);
x_749 = l_Lean_Expr_forallE___override(x_737, x_738, x_739, x_740);
x_750 = lean_ptr_addr(x_738);
lean_dec(x_738);
x_751 = lean_ptr_addr(x_742);
x_752 = lean_usize_dec_eq(x_750, x_751);
if (x_752 == 0)
{
lean_object* x_753; 
lean_dec(x_749);
lean_dec(x_739);
x_753 = l_Lean_Expr_forallE___override(x_737, x_742, x_747, x_740);
x_10 = x_753;
x_11 = x_748;
goto block_90;
}
else
{
size_t x_754; size_t x_755; uint8_t x_756; 
x_754 = lean_ptr_addr(x_739);
lean_dec(x_739);
x_755 = lean_ptr_addr(x_747);
x_756 = lean_usize_dec_eq(x_754, x_755);
if (x_756 == 0)
{
lean_object* x_757; 
lean_dec(x_749);
x_757 = l_Lean_Expr_forallE___override(x_737, x_742, x_747, x_740);
x_10 = x_757;
x_11 = x_748;
goto block_90;
}
else
{
uint8_t x_758; 
x_758 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_740, x_740);
if (x_758 == 0)
{
lean_object* x_759; 
lean_dec(x_749);
x_759 = l_Lean_Expr_forallE___override(x_737, x_742, x_747, x_740);
x_10 = x_759;
x_11 = x_748;
goto block_90;
}
else
{
lean_dec(x_747);
lean_dec(x_742);
lean_dec(x_737);
x_10 = x_749;
x_11 = x_748;
goto block_90;
}
}
}
}
case 8:
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; uint8_t x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; size_t x_776; size_t x_777; uint8_t x_778; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
x_760 = lean_ctor_get(x_4, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_4, 1);
lean_inc(x_761);
x_762 = lean_ctor_get(x_4, 2);
lean_inc(x_762);
x_763 = lean_ctor_get(x_4, 3);
lean_inc(x_763);
x_764 = lean_ctor_get_uint8(x_4, sizeof(void*)*4 + 8);
lean_inc(x_5);
lean_inc(x_761);
x_765 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_761, x_5, x_6);
x_766 = lean_ctor_get(x_765, 0);
lean_inc(x_766);
x_767 = lean_ctor_get(x_765, 1);
lean_inc(x_767);
lean_dec(x_765);
lean_inc(x_5);
lean_inc(x_762);
x_768 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_762, x_5, x_767);
x_769 = lean_ctor_get(x_768, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_768, 1);
lean_inc(x_770);
lean_dec(x_768);
x_771 = lean_unsigned_to_nat(1u);
x_772 = lean_nat_add(x_5, x_771);
lean_inc(x_763);
x_773 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_763, x_772, x_770);
x_774 = lean_ctor_get(x_773, 0);
lean_inc(x_774);
x_775 = lean_ctor_get(x_773, 1);
lean_inc(x_775);
lean_dec(x_773);
x_776 = lean_ptr_addr(x_761);
lean_dec(x_761);
x_777 = lean_ptr_addr(x_766);
x_778 = lean_usize_dec_eq(x_776, x_777);
if (x_778 == 0)
{
lean_object* x_779; 
lean_dec(x_763);
lean_dec(x_762);
x_779 = l_Lean_Expr_letE___override(x_760, x_766, x_769, x_774, x_764);
x_10 = x_779;
x_11 = x_775;
goto block_90;
}
else
{
size_t x_780; size_t x_781; uint8_t x_782; 
x_780 = lean_ptr_addr(x_762);
lean_dec(x_762);
x_781 = lean_ptr_addr(x_769);
x_782 = lean_usize_dec_eq(x_780, x_781);
if (x_782 == 0)
{
lean_object* x_783; 
lean_dec(x_763);
x_783 = l_Lean_Expr_letE___override(x_760, x_766, x_769, x_774, x_764);
x_10 = x_783;
x_11 = x_775;
goto block_90;
}
else
{
size_t x_784; size_t x_785; uint8_t x_786; 
x_784 = lean_ptr_addr(x_763);
lean_dec(x_763);
x_785 = lean_ptr_addr(x_774);
x_786 = lean_usize_dec_eq(x_784, x_785);
if (x_786 == 0)
{
lean_object* x_787; 
x_787 = l_Lean_Expr_letE___override(x_760, x_766, x_769, x_774, x_764);
x_10 = x_787;
x_11 = x_775;
goto block_90;
}
else
{
lean_dec(x_774);
lean_dec(x_769);
lean_dec(x_766);
lean_dec(x_760);
lean_inc(x_4);
x_10 = x_4;
x_11 = x_775;
goto block_90;
}
}
}
}
case 9:
{
lean_object* x_788; lean_object* x_789; uint8_t x_790; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_5);
lean_dec(x_4);
x_788 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__13;
x_789 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8(x_788, x_6);
x_790 = !lean_is_exclusive(x_789);
if (x_790 == 0)
{
lean_object* x_791; uint8_t x_792; 
x_791 = lean_ctor_get(x_789, 1);
x_792 = !lean_is_exclusive(x_791);
if (x_792 == 0)
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; size_t x_797; size_t x_798; size_t x_799; lean_object* x_800; uint8_t x_801; 
x_793 = lean_ctor_get(x_789, 0);
x_794 = lean_ctor_get(x_791, 0);
x_795 = lean_ctor_get(x_791, 1);
x_796 = lean_array_get_size(x_795);
x_797 = lean_usize_of_nat(x_796);
lean_dec(x_796);
x_798 = lean_usize_sub(x_797, x_105);
x_799 = lean_usize_land(x_103, x_798);
x_800 = lean_array_uget(x_795, x_799);
x_801 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_800);
if (x_801 == 0)
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; uint8_t x_811; 
x_802 = lean_unsigned_to_nat(1u);
x_803 = lean_nat_add(x_794, x_802);
lean_dec(x_794);
lean_inc(x_793);
x_804 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_804, 0, x_9);
lean_ctor_set(x_804, 1, x_793);
lean_ctor_set(x_804, 2, x_800);
x_805 = lean_array_uset(x_795, x_799, x_804);
x_806 = lean_unsigned_to_nat(4u);
x_807 = lean_nat_mul(x_803, x_806);
x_808 = lean_unsigned_to_nat(3u);
x_809 = lean_nat_div(x_807, x_808);
lean_dec(x_807);
x_810 = lean_array_get_size(x_805);
x_811 = lean_nat_dec_le(x_809, x_810);
lean_dec(x_810);
lean_dec(x_809);
if (x_811 == 0)
{
lean_object* x_812; 
x_812 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_805);
lean_ctor_set(x_791, 1, x_812);
lean_ctor_set(x_791, 0, x_803);
return x_789;
}
else
{
lean_ctor_set(x_791, 1, x_805);
lean_ctor_set(x_791, 0, x_803);
return x_789;
}
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
x_813 = lean_box(0);
x_814 = lean_array_uset(x_795, x_799, x_813);
lean_inc(x_793);
x_815 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_793, x_800);
x_816 = lean_array_uset(x_814, x_799, x_815);
lean_ctor_set(x_791, 1, x_816);
return x_789;
}
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; size_t x_821; size_t x_822; size_t x_823; lean_object* x_824; uint8_t x_825; 
x_817 = lean_ctor_get(x_789, 0);
x_818 = lean_ctor_get(x_791, 0);
x_819 = lean_ctor_get(x_791, 1);
lean_inc(x_819);
lean_inc(x_818);
lean_dec(x_791);
x_820 = lean_array_get_size(x_819);
x_821 = lean_usize_of_nat(x_820);
lean_dec(x_820);
x_822 = lean_usize_sub(x_821, x_105);
x_823 = lean_usize_land(x_103, x_822);
x_824 = lean_array_uget(x_819, x_823);
x_825 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_824);
if (x_825 == 0)
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; uint8_t x_835; 
x_826 = lean_unsigned_to_nat(1u);
x_827 = lean_nat_add(x_818, x_826);
lean_dec(x_818);
lean_inc(x_817);
x_828 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_828, 0, x_9);
lean_ctor_set(x_828, 1, x_817);
lean_ctor_set(x_828, 2, x_824);
x_829 = lean_array_uset(x_819, x_823, x_828);
x_830 = lean_unsigned_to_nat(4u);
x_831 = lean_nat_mul(x_827, x_830);
x_832 = lean_unsigned_to_nat(3u);
x_833 = lean_nat_div(x_831, x_832);
lean_dec(x_831);
x_834 = lean_array_get_size(x_829);
x_835 = lean_nat_dec_le(x_833, x_834);
lean_dec(x_834);
lean_dec(x_833);
if (x_835 == 0)
{
lean_object* x_836; lean_object* x_837; 
x_836 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_829);
x_837 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_837, 0, x_827);
lean_ctor_set(x_837, 1, x_836);
lean_ctor_set(x_789, 1, x_837);
return x_789;
}
else
{
lean_object* x_838; 
x_838 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_838, 0, x_827);
lean_ctor_set(x_838, 1, x_829);
lean_ctor_set(x_789, 1, x_838);
return x_789;
}
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; 
x_839 = lean_box(0);
x_840 = lean_array_uset(x_819, x_823, x_839);
lean_inc(x_817);
x_841 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_817, x_824);
x_842 = lean_array_uset(x_840, x_823, x_841);
x_843 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_843, 0, x_818);
lean_ctor_set(x_843, 1, x_842);
lean_ctor_set(x_789, 1, x_843);
return x_789;
}
}
}
else
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; size_t x_850; size_t x_851; size_t x_852; lean_object* x_853; uint8_t x_854; 
x_844 = lean_ctor_get(x_789, 1);
x_845 = lean_ctor_get(x_789, 0);
lean_inc(x_844);
lean_inc(x_845);
lean_dec(x_789);
x_846 = lean_ctor_get(x_844, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_844, 1);
lean_inc(x_847);
if (lean_is_exclusive(x_844)) {
 lean_ctor_release(x_844, 0);
 lean_ctor_release(x_844, 1);
 x_848 = x_844;
} else {
 lean_dec_ref(x_844);
 x_848 = lean_box(0);
}
x_849 = lean_array_get_size(x_847);
x_850 = lean_usize_of_nat(x_849);
lean_dec(x_849);
x_851 = lean_usize_sub(x_850, x_105);
x_852 = lean_usize_land(x_103, x_851);
x_853 = lean_array_uget(x_847, x_852);
x_854 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_853);
if (x_854 == 0)
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; uint8_t x_864; 
x_855 = lean_unsigned_to_nat(1u);
x_856 = lean_nat_add(x_846, x_855);
lean_dec(x_846);
lean_inc(x_845);
x_857 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_857, 0, x_9);
lean_ctor_set(x_857, 1, x_845);
lean_ctor_set(x_857, 2, x_853);
x_858 = lean_array_uset(x_847, x_852, x_857);
x_859 = lean_unsigned_to_nat(4u);
x_860 = lean_nat_mul(x_856, x_859);
x_861 = lean_unsigned_to_nat(3u);
x_862 = lean_nat_div(x_860, x_861);
lean_dec(x_860);
x_863 = lean_array_get_size(x_858);
x_864 = lean_nat_dec_le(x_862, x_863);
lean_dec(x_863);
lean_dec(x_862);
if (x_864 == 0)
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; 
x_865 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_858);
if (lean_is_scalar(x_848)) {
 x_866 = lean_alloc_ctor(0, 2, 0);
} else {
 x_866 = x_848;
}
lean_ctor_set(x_866, 0, x_856);
lean_ctor_set(x_866, 1, x_865);
x_867 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_867, 0, x_845);
lean_ctor_set(x_867, 1, x_866);
return x_867;
}
else
{
lean_object* x_868; lean_object* x_869; 
if (lean_is_scalar(x_848)) {
 x_868 = lean_alloc_ctor(0, 2, 0);
} else {
 x_868 = x_848;
}
lean_ctor_set(x_868, 0, x_856);
lean_ctor_set(x_868, 1, x_858);
x_869 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_869, 0, x_845);
lean_ctor_set(x_869, 1, x_868);
return x_869;
}
}
else
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_870 = lean_box(0);
x_871 = lean_array_uset(x_847, x_852, x_870);
lean_inc(x_845);
x_872 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_845, x_853);
x_873 = lean_array_uset(x_871, x_852, x_872);
if (lean_is_scalar(x_848)) {
 x_874 = lean_alloc_ctor(0, 2, 0);
} else {
 x_874 = x_848;
}
lean_ctor_set(x_874, 0, x_846);
lean_ctor_set(x_874, 1, x_873);
x_875 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_875, 0, x_845);
lean_ctor_set(x_875, 1, x_874);
return x_875;
}
}
}
case 10:
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; size_t x_881; size_t x_882; uint8_t x_883; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
x_876 = lean_ctor_get(x_4, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_4, 1);
lean_inc(x_877);
lean_inc(x_5);
lean_inc(x_877);
x_878 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_877, x_5, x_6);
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
lean_dec(x_878);
x_881 = lean_ptr_addr(x_877);
lean_dec(x_877);
x_882 = lean_ptr_addr(x_879);
x_883 = lean_usize_dec_eq(x_881, x_882);
if (x_883 == 0)
{
lean_object* x_884; 
x_884 = l_Lean_Expr_mdata___override(x_876, x_879);
x_10 = x_884;
x_11 = x_880;
goto block_90;
}
else
{
lean_dec(x_879);
lean_dec(x_876);
lean_inc(x_4);
x_10 = x_4;
x_11 = x_880;
goto block_90;
}
}
default: 
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; size_t x_891; size_t x_892; uint8_t x_893; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
x_885 = lean_ctor_get(x_4, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_4, 1);
lean_inc(x_886);
x_887 = lean_ctor_get(x_4, 2);
lean_inc(x_887);
lean_inc(x_5);
lean_inc(x_887);
x_888 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_887, x_5, x_6);
x_889 = lean_ctor_get(x_888, 0);
lean_inc(x_889);
x_890 = lean_ctor_get(x_888, 1);
lean_inc(x_890);
lean_dec(x_888);
x_891 = lean_ptr_addr(x_887);
lean_dec(x_887);
x_892 = lean_ptr_addr(x_889);
x_893 = lean_usize_dec_eq(x_891, x_892);
if (x_893 == 0)
{
lean_object* x_894; 
x_894 = l_Lean_Expr_proj___override(x_885, x_886, x_889);
x_10 = x_894;
x_11 = x_890;
goto block_90;
}
else
{
lean_dec(x_889);
lean_dec(x_886);
lean_dec(x_885);
lean_inc(x_4);
x_10 = x_4;
x_11 = x_890;
goto block_90;
}
}
}
}
else
{
lean_object* x_895; lean_object* x_896; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_895 = lean_ctor_get(x_109, 0);
lean_inc(x_895);
lean_dec(x_109);
x_896 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_896, 0, x_895);
lean_ctor_set(x_896, 1, x_6);
return x_896;
}
block_90:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
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
x_31 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_13, x_32);
lean_dec(x_13);
lean_inc(x_10);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_9);
lean_ctor_set(x_34, 1, x_10);
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
lean_object* x_42; lean_object* x_43; 
x_42 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_35);
lean_ctor_set(x_11, 1, x_42);
lean_ctor_set(x_11, 0, x_33);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_10);
lean_ctor_set(x_43, 1, x_11);
return x_43;
}
else
{
lean_object* x_44; 
lean_ctor_set(x_11, 1, x_35);
lean_ctor_set(x_11, 0, x_33);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_10);
lean_ctor_set(x_44, 1, x_11);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_box(0);
x_46 = lean_array_uset(x_14, x_29, x_45);
lean_inc(x_10);
x_47 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_10, x_30);
x_48 = lean_array_uset(x_46, x_29, x_47);
lean_ctor_set(x_11, 1, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_10);
lean_ctor_set(x_49, 1, x_11);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; size_t x_62; size_t x_63; size_t x_64; size_t x_65; size_t x_66; lean_object* x_67; uint8_t x_68; 
x_50 = lean_ctor_get(x_11, 0);
x_51 = lean_ctor_get(x_11, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_11);
x_52 = lean_array_get_size(x_51);
x_53 = l_Lean_Expr_hash(x_4);
lean_dec(x_4);
x_54 = lean_uint64_of_nat(x_5);
lean_dec(x_5);
x_55 = lean_uint64_mix_hash(x_53, x_54);
x_56 = 32;
x_57 = lean_uint64_shift_right(x_55, x_56);
x_58 = lean_uint64_xor(x_55, x_57);
x_59 = 16;
x_60 = lean_uint64_shift_right(x_58, x_59);
x_61 = lean_uint64_xor(x_58, x_60);
x_62 = lean_uint64_to_usize(x_61);
x_63 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_64 = 1;
x_65 = lean_usize_sub(x_63, x_64);
x_66 = lean_usize_land(x_62, x_65);
x_67 = lean_array_uget(x_51, x_66);
x_68 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_50, x_69);
lean_dec(x_50);
lean_inc(x_10);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_9);
lean_ctor_set(x_71, 1, x_10);
lean_ctor_set(x_71, 2, x_67);
x_72 = lean_array_uset(x_51, x_66, x_71);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_mul(x_70, x_73);
x_75 = lean_unsigned_to_nat(3u);
x_76 = lean_nat_div(x_74, x_75);
lean_dec(x_74);
x_77 = lean_array_get_size(x_72);
x_78 = lean_nat_dec_le(x_76, x_77);
lean_dec(x_77);
lean_dec(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_72);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_70);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_10);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_70);
lean_ctor_set(x_82, 1, x_72);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_10);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_box(0);
x_85 = lean_array_uset(x_51, x_66, x_84);
lean_inc(x_10);
x_86 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_10, x_67);
x_87 = lean_array_uset(x_85, x_66, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_50);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_10);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
lean_object* x_897; 
lean_dec(x_5);
x_897 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_897, 0, x_4);
lean_ctor_set(x_897, 1, x_6);
return x_897;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Expr_instantiateBetaRevRange_visit___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Expr_instantiateBetaRevRange_visit___spec__7(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_instantiateBetaRevRange_visit___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Expr_instantiateBetaRevRange_visit___spec__9(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
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
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stop ≤ args.size\n    ", 23, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_instantiateBetaRevRange___closed__1;
x_2 = l_Lean_Expr_instantiateBetaRevRange___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Expr.instantiateBetaRevRange", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
x_2 = l_Lean_Expr_instantiateBetaRevRange___closed__4;
x_3 = lean_unsigned_to_nat(28u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Expr_instantiateBetaRevRange___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_instantiateBetaRevRange___closed__6;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_instantiateBetaRevRange___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_5 == 0)
{
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_2, x_3);
if (x_6 == 0)
{
return x_1;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_le(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = l_Lean_Expr_instantiateBetaRevRange___closed__5;
x_10 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_instantiateBetaRevRange___closed__8;
x_13 = l_Lean_Expr_instantiateBetaRevRange_visit(x_2, x_3, x_4, x_1, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
return x_14;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwFunctionExpected___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
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
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwFunctionExpected___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_throwFunctionExpected___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwFunctionExpected___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("function expected", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwFunctionExpected___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwFunctionExpected___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwFunctionExpected___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwFunctionExpected___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwFunctionExpected___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_indentExpr(x_1);
x_8 = l_Lean_Meta_throwFunctionExpected___rarg___closed__2;
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at_Lean_Meta_throwFunctionExpected___spec__1___rarg(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_throwFunctionExpected___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwFunctionExpected___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_throwFunctionExpected___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_throwFunctionExpected___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_nat_dec_lt(x_6, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_24; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 7)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_dec(x_5);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_17 = x_28;
x_18 = x_13;
goto block_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_dec(x_5);
x_30 = l_Lean_Expr_instantiateBetaRevRange(x_24, x_29, x_6, x_2);
lean_dec(x_29);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_31 = lean_whnf(x_30, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 7)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 2);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_6);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_6);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_17 = x_36;
x_18 = x_33;
goto block_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_32);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_6, x_38);
lean_dec(x_6);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_39, x_2, x_40, x_1);
lean_dec(x_39);
x_42 = l_Lean_Meta_throwFunctionExpected___rarg(x_41, x_9, x_10, x_11, x_12, x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
uint8_t x_47; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_31);
if (x_47 == 0)
{
return x_31;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_31, 0);
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_31);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
block_23:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_4, 2);
x_21 = lean_nat_add(x_6, x_20);
lean_dec(x_6);
x_5 = x_19;
x_6 = x_21;
x_7 = lean_box(0);
x_8 = lean_box(0);
x_13 = x_18;
goto _start;
}
}
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_array_get_size(x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(1u);
lean_inc(x_11);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_12);
x_16 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_2, x_14, x_14, x_15, x_12, lean_box(0), lean_box(0), x_3, x_4, x_5, x_6, x_10);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Expr_instantiateBetaRevRange(x_19, x_20, x_11, x_2);
lean_dec(x_11);
lean_dec(x_20);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Lean_Expr_instantiateBetaRevRange(x_24, x_25, x_11, x_2);
lean_dec(x_11);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_11);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_8);
if (x_32 == 0)
{
return x_8;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_8, 0);
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_8);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwIncorrectNumberOfLevels___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
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
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwIncorrectNumberOfLevels___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_throwIncorrectNumberOfLevels___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwIncorrectNumberOfLevels___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("incorrect number of universe levels ", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwIncorrectNumberOfLevels___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwIncorrectNumberOfLevels___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_Expr_const___override(x_1, x_2);
x_9 = l_Lean_MessageData_ofExpr(x_8);
x_10 = l_Lean_Meta_throwIncorrectNumberOfLevels___rarg___closed__2;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___at_Lean_Meta_throwIncorrectNumberOfLevels___spec__1___rarg(x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_throwIncorrectNumberOfLevels___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwIncorrectNumberOfLevels___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_throwIncorrectNumberOfLevels___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_throwIncorrectNumberOfLevels___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_ConstantInfo_levelParams(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_List_lengthTRAux___rarg(x_11, x_12);
lean_dec(x_11);
x_14 = l_List_lengthTRAux___rarg(x_2, x_12);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
x_16 = l_Lean_Meta_throwIncorrectNumberOfLevels___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_1);
x_17 = l_Lean_Core_instantiateTypeLevelParams(x_9, x_2, x_5, x_6, x_10);
lean_dec(x_9);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
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
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid projection", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nfrom type", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_6, 1);
x_17 = lean_nat_dec_lt(x_8, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_26; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_26 = lean_whnf(x_7, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 7)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 2);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_hasLooseBVars(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_29);
x_19 = x_31;
x_20 = x_28;
goto block_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_3);
lean_inc(x_8);
lean_inc(x_1);
x_32 = l_Lean_Expr_proj___override(x_1, x_8, x_3);
x_33 = lean_expr_instantiate1(x_29, x_32);
lean_dec(x_32);
lean_dec(x_29);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_19 = x_34;
x_20 = x_28;
goto block_25;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_27);
lean_dec(x_8);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_37 = l_Lean_indentExpr(x_36);
x_38 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_indentExpr(x_4);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_45, x_11, x_12, x_13, x_14, x_35);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
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
else
{
uint8_t x_51; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_26);
if (x_51 == 0)
{
return x_26;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_26, 0);
x_53 = lean_ctor_get(x_26, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_26);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
block_25:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_6, 2);
x_23 = lean_nat_add(x_8, x_22);
lean_dec(x_8);
x_7 = x_21;
x_8 = x_23;
x_9 = lean_box(0);
x_10 = lean_box(0);
x_15 = x_20;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_14);
x_16 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lambda__1___closed__1;
lean_inc(x_15);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_15, x_18);
lean_dec(x_15);
lean_inc(x_1);
x_20 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_17, x_19);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 2);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_22);
x_24 = lean_array_get_size(x_20);
x_25 = lean_nat_dec_eq(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
x_26 = l_Lean_Expr_proj___override(x_3, x_4, x_5);
x_27 = l_Lean_indentExpr(x_26);
x_28 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_indentExpr(x_1);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_35, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_6, 0);
lean_inc(x_37);
lean_dec(x_6);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Expr_const___override(x_38, x_7);
x_40 = l_Array_toSubarray___rarg(x_20, x_14, x_21);
x_41 = l_Array_ofSubarray___rarg(x_40);
lean_dec(x_40);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_42 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_39, x_41, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_4);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_14);
lean_ctor_set(x_45, 1, x_4);
lean_ctor_set(x_45, 2, x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_46 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2(x_3, x_4, x_5, x_1, x_45, x_45, x_43, x_14, lean_box(0), lean_box(0), x_9, x_10, x_11, x_12, x_44);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_49 = lean_whnf(x_47, x_9, x_10, x_11, x_12, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 7)
{
uint8_t x_51; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_49, 0);
lean_dec(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_expr_consume_type_annotations(x_53);
lean_ctor_set(x_49, 0, x_54);
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_expr_consume_type_annotations(x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_50);
x_59 = lean_ctor_get(x_49, 1);
lean_inc(x_59);
lean_dec(x_49);
x_60 = l_Lean_Expr_proj___override(x_3, x_4, x_5);
x_61 = l_Lean_indentExpr(x_60);
x_62 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_indentExpr(x_1);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_69, x_9, x_10, x_11, x_12, x_59);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_49);
if (x_71 == 0)
{
return x_49;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_49, 0);
x_73 = lean_ctor_get(x_49, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_49);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_46);
if (x_75 == 0)
{
return x_46;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_46, 0);
x_77 = lean_ctor_get(x_46, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_46);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_42);
if (x_79 == 0)
{
return x_42;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_42, 0);
x_81 = lean_ctor_get(x_42, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_42);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_getAppFn(x_13);
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_7, x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_environment_find(x_22, x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_17);
x_24 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_25 = l_Lean_indentExpr(x_24);
x_26 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_25);
lean_ctor_set(x_18, 0, x_26);
x_27 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_indentExpr(x_13);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_32, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_23, 0);
lean_inc(x_34);
lean_dec(x_23);
if (lean_obj_tag(x_34) == 5)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 4);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_35);
lean_dec(x_17);
x_37 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_38 = l_Lean_indentExpr(x_37);
x_39 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_38);
lean_ctor_set(x_18, 0, x_39);
x_40 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_18);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_indentExpr(x_13);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_45, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_36, 1);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_36);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_36, 0);
x_50 = lean_ctor_get(x_36, 1);
lean_dec(x_50);
x_51 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_49, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 6)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_35, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_name_eq(x_56, x_1);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_54);
lean_dec(x_35);
lean_dec(x_17);
x_58 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_59 = l_Lean_indentExpr(x_58);
x_60 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_59);
lean_ctor_set(x_36, 0, x_60);
x_61 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_61);
lean_ctor_set(x_18, 0, x_36);
x_62 = l_Lean_indentExpr(x_13);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_18);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_65, x_4, x_5, x_6, x_7, x_53);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_71; lean_object* x_72; 
lean_free_object(x_36);
lean_free_object(x_18);
x_71 = lean_box(0);
x_72 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lambda__1(x_13, x_35, x_1, x_2, x_3, x_54, x_17, x_71, x_4, x_5, x_6, x_7, x_53);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_52);
lean_dec(x_35);
lean_dec(x_17);
x_73 = lean_ctor_get(x_51, 1);
lean_inc(x_73);
lean_dec(x_51);
x_74 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_75 = l_Lean_indentExpr(x_74);
x_76 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_75);
lean_ctor_set(x_36, 0, x_76);
x_77 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_77);
lean_ctor_set(x_18, 0, x_36);
x_78 = l_Lean_indentExpr(x_13);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_18);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_81, x_4, x_5, x_6, x_7, x_73);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_free_object(x_36);
lean_dec(x_35);
lean_free_object(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_51);
if (x_83 == 0)
{
return x_51;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_51, 0);
x_85 = lean_ctor_get(x_51, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_51);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_36, 0);
lean_inc(x_87);
lean_dec(x_36);
x_88 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_87, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 6)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_35, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_name_eq(x_93, x_1);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_91);
lean_dec(x_35);
lean_dec(x_17);
x_95 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_96 = l_Lean_indentExpr(x_95);
x_97 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_99);
lean_ctor_set(x_18, 0, x_98);
x_100 = l_Lean_indentExpr(x_13);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_18);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_103, x_4, x_5, x_6, x_7, x_90);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_free_object(x_18);
x_109 = lean_box(0);
x_110 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lambda__1(x_13, x_35, x_1, x_2, x_3, x_91, x_17, x_109, x_4, x_5, x_6, x_7, x_90);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_89);
lean_dec(x_35);
lean_dec(x_17);
x_111 = lean_ctor_get(x_88, 1);
lean_inc(x_111);
lean_dec(x_88);
x_112 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_113 = l_Lean_indentExpr(x_112);
x_114 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_116);
lean_ctor_set(x_18, 0, x_115);
x_117 = l_Lean_indentExpr(x_13);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_18);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_120, x_4, x_5, x_6, x_7, x_111);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_35);
lean_free_object(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = lean_ctor_get(x_88, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_88, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_124 = x_88;
} else {
 lean_dec_ref(x_88);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_35);
lean_dec(x_17);
x_126 = !lean_is_exclusive(x_36);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_ctor_get(x_36, 1);
lean_dec(x_127);
x_128 = lean_ctor_get(x_36, 0);
lean_dec(x_128);
x_129 = !lean_is_exclusive(x_47);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_130 = lean_ctor_get(x_47, 1);
lean_dec(x_130);
x_131 = lean_ctor_get(x_47, 0);
lean_dec(x_131);
x_132 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_133 = l_Lean_indentExpr(x_132);
x_134 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_47, 7);
lean_ctor_set(x_47, 1, x_133);
lean_ctor_set(x_47, 0, x_134);
x_135 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_135);
lean_ctor_set(x_36, 0, x_47);
x_136 = l_Lean_indentExpr(x_13);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_136);
lean_ctor_set(x_18, 0, x_36);
x_137 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_18);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_138, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_47);
x_140 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_141 = l_Lean_indentExpr(x_140);
x_142 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
x_144 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_144);
lean_ctor_set(x_36, 0, x_143);
x_145 = l_Lean_indentExpr(x_13);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_145);
lean_ctor_set(x_18, 0, x_36);
x_146 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_18);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_147, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_36);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_149 = x_47;
} else {
 lean_dec_ref(x_47);
 x_149 = lean_box(0);
}
x_150 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_151 = l_Lean_indentExpr(x_150);
x_152 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
if (lean_is_scalar(x_149)) {
 x_153 = lean_alloc_ctor(7, 2, 0);
} else {
 x_153 = x_149;
 lean_ctor_set_tag(x_153, 7);
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lean_indentExpr(x_13);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_156);
lean_ctor_set(x_18, 0, x_155);
x_157 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_18);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_158, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_159;
}
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_34);
lean_dec(x_17);
x_160 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_161 = l_Lean_indentExpr(x_160);
x_162 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_161);
lean_ctor_set(x_18, 0, x_162);
x_163 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_18);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lean_indentExpr(x_13);
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_168, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_18, 0);
x_171 = lean_ctor_get(x_18, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_18);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_environment_find(x_172, x_16);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_17);
x_174 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_175 = l_Lean_indentExpr(x_174);
x_176 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
x_178 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_179 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = l_Lean_indentExpr(x_13);
x_181 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_183 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_183, x_4, x_5, x_6, x_7, x_171);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_184;
}
else
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_173, 0);
lean_inc(x_185);
lean_dec(x_173);
if (lean_obj_tag(x_185) == 5)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
lean_dec(x_185);
x_187 = lean_ctor_get(x_186, 4);
lean_inc(x_187);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_186);
lean_dec(x_17);
x_188 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_189 = l_Lean_indentExpr(x_188);
x_190 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_189);
x_192 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_193 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = l_Lean_indentExpr(x_13);
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_197 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
x_198 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_197, x_4, x_5, x_6, x_7, x_171);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_198;
}
else
{
lean_object* x_199; 
x_199 = lean_ctor_get(x_187, 1);
lean_inc(x_199);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_187, 0);
lean_inc(x_200);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_201 = x_187;
} else {
 lean_dec_ref(x_187);
 x_201 = lean_box(0);
}
x_202 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_200, x_4, x_5, x_6, x_7, x_171);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
if (lean_obj_tag(x_203) == 6)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = lean_ctor_get(x_203, 0);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_ctor_get(x_186, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
lean_dec(x_206);
x_208 = lean_name_eq(x_207, x_1);
lean_dec(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_205);
lean_dec(x_186);
lean_dec(x_17);
x_209 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_210 = l_Lean_indentExpr(x_209);
x_211 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
if (lean_is_scalar(x_201)) {
 x_212 = lean_alloc_ctor(7, 2, 0);
} else {
 x_212 = x_201;
 lean_ctor_set_tag(x_212, 7);
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_210);
x_213 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_214 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_215 = l_Lean_indentExpr(x_13);
x_216 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
x_217 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_218 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_218, x_4, x_5, x_6, x_7, x_204);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_222 = x_219;
} else {
 lean_dec_ref(x_219);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; 
lean_dec(x_201);
x_224 = lean_box(0);
x_225 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lambda__1(x_13, x_186, x_1, x_2, x_3, x_205, x_17, x_224, x_4, x_5, x_6, x_7, x_204);
return x_225;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_203);
lean_dec(x_186);
lean_dec(x_17);
x_226 = lean_ctor_get(x_202, 1);
lean_inc(x_226);
lean_dec(x_202);
x_227 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_228 = l_Lean_indentExpr(x_227);
x_229 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
if (lean_is_scalar(x_201)) {
 x_230 = lean_alloc_ctor(7, 2, 0);
} else {
 x_230 = x_201;
 lean_ctor_set_tag(x_230, 7);
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
x_231 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_232 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lean_indentExpr(x_13);
x_234 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_235 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_236 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
x_237 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_236, x_4, x_5, x_6, x_7, x_226);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_201);
lean_dec(x_186);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_238 = lean_ctor_get(x_202, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_202, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_240 = x_202;
} else {
 lean_dec_ref(x_202);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_186);
lean_dec(x_17);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_242 = x_187;
} else {
 lean_dec_ref(x_187);
 x_242 = lean_box(0);
}
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_243 = x_199;
} else {
 lean_dec_ref(x_199);
 x_243 = lean_box(0);
}
x_244 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_245 = l_Lean_indentExpr(x_244);
x_246 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
if (lean_is_scalar(x_243)) {
 x_247 = lean_alloc_ctor(7, 2, 0);
} else {
 x_247 = x_243;
 lean_ctor_set_tag(x_247, 7);
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_245);
x_248 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
if (lean_is_scalar(x_242)) {
 x_249 = lean_alloc_ctor(7, 2, 0);
} else {
 x_249 = x_242;
 lean_ctor_set_tag(x_249, 7);
}
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
x_250 = l_Lean_indentExpr(x_13);
x_251 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_253 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
x_254 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_253, x_4, x_5, x_6, x_7, x_171);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_254;
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_185);
lean_dec(x_17);
x_255 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_256 = l_Lean_indentExpr(x_255);
x_257 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_258 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_256);
x_259 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_260 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
x_261 = l_Lean_indentExpr(x_13);
x_262 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
x_263 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_264 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
x_265 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_264, x_4, x_5, x_6, x_7, x_171);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_265;
}
}
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_15);
x_266 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_267 = l_Lean_indentExpr(x_266);
x_268 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_269 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_267);
x_270 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_271 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
x_272 = l_Lean_indentExpr(x_13);
x_273 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
x_274 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_275 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
x_276 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_275, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_276;
}
}
else
{
uint8_t x_277; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_277 = !lean_is_exclusive(x_12);
if (x_277 == 0)
{
return x_12;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_12, 0);
x_279 = lean_ctor_get(x_12, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_12);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
return x_280;
}
}
}
else
{
uint8_t x_281; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_281 = !lean_is_exclusive(x_9);
if (x_281 == 0)
{
return x_9;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_9, 0);
x_283 = lean_ctor_get(x_9, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_9);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwTypeExcepted___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
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
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwTypeExcepted___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_throwTypeExcepted___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExcepted___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type expected", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExcepted___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwTypeExcepted___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_indentExpr(x_1);
x_8 = l_Lean_Meta_throwTypeExcepted___rarg___closed__2;
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at_Lean_Meta_throwTypeExcepted___spec__1___rarg(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_throwTypeExcepted___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwTypeExcepted___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_throwTypeExcepted___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_throwTypeExcepted___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_st_ref_take(x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_10, 7);
x_16 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_15, x_1, x_2);
lean_ctor_set(x_10, 7, x_16);
x_17 = lean_st_ref_set(x_4, x_9, x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
x_26 = lean_ctor_get(x_10, 2);
x_27 = lean_ctor_get(x_10, 3);
x_28 = lean_ctor_get(x_10, 4);
x_29 = lean_ctor_get(x_10, 5);
x_30 = lean_ctor_get(x_10, 6);
x_31 = lean_ctor_get(x_10, 7);
x_32 = lean_ctor_get(x_10, 8);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_33 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_31, x_1, x_2);
x_34 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_26);
lean_ctor_set(x_34, 3, x_27);
lean_ctor_set(x_34, 4, x_28);
lean_ctor_set(x_34, 5, x_29);
lean_ctor_set(x_34, 6, x_30);
lean_ctor_set(x_34, 7, x_33);
lean_ctor_set(x_34, 8, x_32);
lean_ctor_set(x_9, 0, x_34);
x_35 = lean_st_ref_set(x_4, x_9, x_11);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = lean_box(0);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_40 = lean_ctor_get(x_9, 1);
x_41 = lean_ctor_get(x_9, 2);
x_42 = lean_ctor_get(x_9, 3);
x_43 = lean_ctor_get(x_9, 4);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_9);
x_44 = lean_ctor_get(x_10, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_10, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_10, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_10, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_10, 4);
lean_inc(x_48);
x_49 = lean_ctor_get(x_10, 5);
lean_inc(x_49);
x_50 = lean_ctor_get(x_10, 6);
lean_inc(x_50);
x_51 = lean_ctor_get(x_10, 7);
lean_inc(x_51);
x_52 = lean_ctor_get(x_10, 8);
lean_inc(x_52);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 lean_ctor_release(x_10, 5);
 lean_ctor_release(x_10, 6);
 lean_ctor_release(x_10, 7);
 lean_ctor_release(x_10, 8);
 x_53 = x_10;
} else {
 lean_dec_ref(x_10);
 x_53 = lean_box(0);
}
x_54 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_51, x_1, x_2);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 9, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_44);
lean_ctor_set(x_55, 1, x_45);
lean_ctor_set(x_55, 2, x_46);
lean_ctor_set(x_55, 3, x_47);
lean_ctor_set(x_55, 4, x_48);
lean_ctor_set(x_55, 5, x_49);
lean_ctor_set(x_55, 6, x_50);
lean_ctor_set(x_55, 7, x_54);
lean_ctor_set(x_55, 8, x_52);
x_56 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_40);
lean_ctor_set(x_56, 2, x_41);
lean_ctor_set(x_56, 3, x_42);
lean_ctor_set(x_56, 4, x_43);
x_57 = lean_st_ref_set(x_4, x_56, x_11);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
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
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_19);
x_21 = l_Lean_Expr_sort___override(x_19);
x_22 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_13, x_21, x_2, x_3, x_4, x_5, x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_28 = l_Lean_Meta_throwTypeExcepted___rarg(x_1, x_2, x_3, x_4, x_5, x_27);
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
x_40 = l_Lean_Meta_throwTypeExcepted___rarg(x_1, x_2, x_3, x_4, x_5, x_39);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_9);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_getLevel(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_array_get_size(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = l_Lean_Level_normalize(x_10);
lean_dec(x_10);
x_16 = l_Lean_Expr_sort___override(x_15);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
lean_free_object(x_8);
x_17 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_18 = 0;
x_19 = l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__1(x_1, x_17, x_18, x_10, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_Level_normalize(x_21);
lean_dec(x_21);
x_23 = l_Lean_Expr_sort___override(x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = l_Lean_Level_normalize(x_24);
lean_dec(x_24);
x_27 = l_Lean_Expr_sort___override(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
return x_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_8, 0);
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_8);
x_35 = lean_array_get_size(x_1);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_lt(x_36, x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_35);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = l_Lean_Level_normalize(x_33);
lean_dec(x_33);
x_39 = l_Lean_Expr_sort___override(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
return x_40;
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
x_41 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_42 = 0;
x_43 = l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__1(x_1, x_41, x_42, x_33, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = l_Lean_Level_normalize(x_44);
lean_dec(x_44);
x_48 = l_Lean_Expr_sort___override(x_47);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_52 = x_43;
} else {
 lean_dec_ref(x_43);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_8);
if (x_54 == 0)
{
return x_8;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_8, 0);
x_56 = lean_ctor_get(x_8, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_8);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1;
x_8 = 0;
x_9 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_1, x_7, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = 1;
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_10, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 0;
x_12 = 1;
x_13 = 1;
x_14 = l_Lean_Meta_mkForallFVars(x_1, x_9, x_11, x_12, x_13, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1;
x_8 = 0;
x_9 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_1, x_7, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownMVar___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
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
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownMVar___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_throwUnknownMVar___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown metavariable '\?", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwUnknownMVar___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwUnknownMVar___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_MessageData_ofName(x_1);
x_8 = l_Lean_Meta_throwUnknownMVar___rarg___closed__2;
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_Meta_throwUnknownMVar___rarg___closed__4;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at_Lean_Meta_throwUnknownMVar___spec__1___rarg(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_throwUnknownMVar___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownMVar___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_throwUnknownMVar___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_throwUnknownMVar___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
x_12 = l_Lean_MetavarContext_findDecl_x3f(x_11, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_free_object(x_7);
x_13 = l_Lean_Meta_throwUnknownMVar___rarg(x_1, x_2, x_3, x_4, x_5, x_10);
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
x_19 = l_Lean_MetavarContext_findDecl_x3f(x_18, x_1);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = l_Lean_Meta_throwUnknownMVar___rarg(x_1, x_2, x_3, x_4, x_5, x_17);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_1);
x_8 = lean_local_ctx_find(x_7, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Lean_FVarId_throwUnknown___rarg(x_1, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_LocalDecl_type(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_expr_equal(x_10, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_14;
goto _start;
}
else
{
uint64_t x_16; uint64_t x_17; uint8_t x_18; 
x_16 = lean_ctor_get_uint64(x_5, sizeof(void*)*1);
x_17 = lean_ctor_get_uint64(x_9, sizeof(void*)*1);
lean_dec(x_9);
x_18 = lean_uint64_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_4, x_19);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___closed__2;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_expr_equal(x_14, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_free_object(x_1);
x_17 = lean_box(0);
return x_17;
}
else
{
uint64_t x_18; uint64_t x_19; uint8_t x_20; 
x_18 = lean_ctor_get_uint64(x_3, sizeof(void*)*1);
x_19 = lean_ctor_get_uint64(x_12, sizeof(void*)*1);
lean_dec(x_12);
x_20 = lean_uint64_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_13);
lean_free_object(x_1);
x_21 = lean_box(0);
return x_21;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
}
case 1:
{
lean_object* x_22; size_t x_23; 
lean_free_object(x_1);
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_usize_shift_right(x_2, x_6);
x_1 = x_22;
x_2 = x_23;
goto _start;
}
default: 
{
lean_object* x_25; 
lean_free_object(x_1);
x_25 = lean_box(0);
return x_25;
}
}
}
else
{
lean_object* x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = 5;
x_28 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___closed__2;
x_29 = lean_usize_land(x_2, x_28);
x_30 = lean_usize_to_nat(x_29);
x_31 = lean_box(2);
x_32 = lean_array_get(x_31, x_26, x_30);
lean_dec(x_30);
lean_dec(x_26);
switch (lean_obj_tag(x_32)) {
case 0:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_3, 0);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
x_37 = lean_expr_equal(x_35, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_33);
x_38 = lean_box(0);
return x_38;
}
else
{
uint64_t x_39; uint64_t x_40; uint8_t x_41; 
x_39 = lean_ctor_get_uint64(x_3, sizeof(void*)*1);
x_40 = lean_ctor_get_uint64(x_33, sizeof(void*)*1);
lean_dec(x_33);
x_41 = lean_uint64_dec_eq(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_34);
x_42 = lean_box(0);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_34);
return x_43;
}
}
}
case 1:
{
lean_object* x_44; size_t x_45; 
x_44 = lean_ctor_get(x_32, 0);
lean_inc(x_44);
lean_dec(x_32);
x_45 = lean_usize_shift_right(x_2, x_27);
x_1 = x_44;
x_2 = x_45;
goto _start;
}
default: 
{
lean_object* x_47; 
x_47 = lean_box(0);
return x_47;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 1);
lean_inc(x_49);
lean_dec(x_1);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__3(x_48, x_49, lean_box(0), x_50, x_3);
lean_dec(x_49);
lean_dec(x_48);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; size_t x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
x_5 = l_Lean_Expr_hash(x_3);
x_6 = lean_uint64_mix_hash(x_5, x_4);
x_7 = lean_uint64_to_usize(x_6);
x_8 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2(x_1, x_7, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__6(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = 1;
x_12 = lean_usize_sub(x_1, x_11);
x_13 = 5;
x_14 = lean_usize_mul(x_13, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_9, sizeof(void*)*1);
x_19 = l_Lean_Expr_hash(x_17);
lean_dec(x_17);
x_20 = lean_uint64_mix_hash(x_19, x_18);
x_21 = lean_uint64_to_usize(x_20);
x_22 = lean_usize_shift_right(x_21, x_14);
x_23 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5(x_6, x_22, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_16;
x_6 = x_23;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_expr_equal(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
lean_dec(x_2);
x_2 = x_22;
goto _start;
}
else
{
uint64_t x_24; uint64_t x_25; uint8_t x_26; 
x_24 = lean_ctor_get_uint64(x_3, sizeof(void*)*1);
x_25 = lean_ctor_get_uint64(x_17, sizeof(void*)*1);
lean_dec(x_17);
x_26 = lean_uint64_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
lean_dec(x_5);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_2, x_27);
lean_dec(x_2);
x_2 = x_28;
goto _start;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_1, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_1, 0);
lean_dec(x_32);
x_33 = lean_array_fset(x_5, x_2, x_3);
x_34 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_35 = lean_array_fset(x_5, x_2, x_3);
x_36 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_expr_equal(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_15);
x_24 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_array_fset(x_17, x_12, x_25);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
else
{
uint64_t x_27; uint64_t x_28; uint8_t x_29; 
x_27 = lean_ctor_get_uint64(x_4, sizeof(void*)*1);
x_28 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_29 = lean_uint64_dec_eq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_15);
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_array_fset(x_17, x_12, x_31);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_32);
return x_1;
}
else
{
lean_object* x_33; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_33 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
x_38 = lean_expr_equal(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_34, x_35, x_4, x_5);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_array_fset(x_17, x_12, x_40);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_41);
return x_1;
}
else
{
uint64_t x_42; uint64_t x_43; uint8_t x_44; 
x_42 = lean_ctor_get_uint64(x_4, sizeof(void*)*1);
x_43 = lean_ctor_get_uint64(x_34, sizeof(void*)*1);
x_44 = lean_uint64_dec_eq(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_34, x_35, x_4, x_5);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_35);
lean_dec(x_34);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_49 = lean_array_fset(x_17, x_12, x_48);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_49);
return x_1;
}
}
}
}
case 1:
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_15, 0);
x_52 = lean_usize_shift_right(x_2, x_9);
x_53 = lean_usize_add(x_3, x_8);
x_54 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5(x_51, x_52, x_53, x_4, x_5);
lean_ctor_set(x_15, 0, x_54);
x_55 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_55);
return x_1;
}
else
{
lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_15, 0);
lean_inc(x_56);
lean_dec(x_15);
x_57 = lean_usize_shift_right(x_2, x_9);
x_58 = lean_usize_add(x_3, x_8);
x_59 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5(x_56, x_57, x_58, x_4, x_5);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_array_fset(x_17, x_12, x_60);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_61);
return x_1;
}
}
default: 
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_4);
lean_ctor_set(x_62, 1, x_5);
x_63 = lean_array_fset(x_17, x_12, x_62);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_63);
return x_1;
}
}
}
}
else
{
lean_object* x_64; size_t x_65; size_t x_66; size_t x_67; size_t x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
lean_dec(x_1);
x_65 = 1;
x_66 = 5;
x_67 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___closed__2;
x_68 = lean_usize_land(x_2, x_67);
x_69 = lean_usize_to_nat(x_68);
x_70 = lean_array_get_size(x_64);
x_71 = lean_nat_dec_lt(x_69, x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_69);
lean_dec(x_5);
lean_dec(x_4);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_64);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_array_fget(x_64, x_69);
x_74 = lean_box(0);
x_75 = lean_array_fset(x_64, x_69, x_74);
switch (lean_obj_tag(x_73)) {
case 0:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_78 = x_73;
} else {
 lean_dec_ref(x_73);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_4, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
x_81 = lean_expr_equal(x_79, x_80);
lean_dec(x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_78);
x_82 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_76, x_77, x_4, x_5);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_array_fset(x_75, x_69, x_83);
lean_dec(x_69);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
else
{
uint64_t x_86; uint64_t x_87; uint8_t x_88; 
x_86 = lean_ctor_get_uint64(x_4, sizeof(void*)*1);
x_87 = lean_ctor_get_uint64(x_76, sizeof(void*)*1);
x_88 = lean_uint64_dec_eq(x_86, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_78);
x_89 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_76, x_77, x_4, x_5);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_array_fset(x_75, x_69, x_90);
lean_dec(x_69);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_77);
lean_dec(x_76);
if (lean_is_scalar(x_78)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_78;
}
lean_ctor_set(x_93, 0, x_4);
lean_ctor_set(x_93, 1, x_5);
x_94 = lean_array_fset(x_75, x_69, x_93);
lean_dec(x_69);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
case 1:
{
lean_object* x_96; lean_object* x_97; size_t x_98; size_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = lean_ctor_get(x_73, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_97 = x_73;
} else {
 lean_dec_ref(x_73);
 x_97 = lean_box(0);
}
x_98 = lean_usize_shift_right(x_2, x_66);
x_99 = lean_usize_add(x_3, x_65);
x_100 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5(x_96, x_98, x_99, x_4, x_5);
if (lean_is_scalar(x_97)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_97;
}
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_array_fset(x_75, x_69, x_101);
lean_dec(x_69);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
default: 
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_4);
lean_ctor_set(x_104, 1, x_5);
x_105 = lean_array_fset(x_75, x_69, x_104);
lean_dec(x_69);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
}
}
else
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_1);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; size_t x_110; uint8_t x_111; 
x_108 = lean_unsigned_to_nat(0u);
x_109 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__7(x_1, x_108, x_4, x_5);
x_110 = 7;
x_111 = lean_usize_dec_le(x_110, x_3);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_109);
x_113 = lean_unsigned_to_nat(4u);
x_114 = lean_nat_dec_lt(x_112, x_113);
lean_dec(x_112);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_109, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_109, 1);
lean_inc(x_116);
lean_dec(x_109);
x_117 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5___closed__1;
x_118 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__6(x_3, x_115, x_116, lean_box(0), x_108, x_117);
lean_dec(x_116);
lean_dec(x_115);
return x_118;
}
else
{
return x_109;
}
}
else
{
return x_109;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; size_t x_124; uint8_t x_125; 
x_119 = lean_ctor_get(x_1, 0);
x_120 = lean_ctor_get(x_1, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_1);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_unsigned_to_nat(0u);
x_123 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__7(x_121, x_122, x_4, x_5);
x_124 = 7;
x_125 = lean_usize_dec_le(x_124, x_3);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_123);
x_127 = lean_unsigned_to_nat(4u);
x_128 = lean_nat_dec_lt(x_126, x_127);
lean_dec(x_126);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_123, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_123, 1);
lean_inc(x_130);
lean_dec(x_123);
x_131 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5___closed__1;
x_132 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__6(x_3, x_129, x_130, lean_box(0), x_122, x_131);
lean_dec(x_130);
lean_dec(x_129);
return x_132;
}
else
{
return x_123;
}
}
else
{
return x_123;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; size_t x_9; lean_object* x_10; 
x_4 = 1;
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
x_7 = l_Lean_Expr_hash(x_5);
lean_dec(x_5);
x_8 = lean_uint64_mix_hash(x_7, x_6);
x_9 = lean_uint64_to_usize(x_8);
x_10 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5(x_1, x_9, x_4, x_2, x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_hasMVar(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_Meta_mkExprConfigCacheKey(x_1, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_4, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_17, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_free_object(x_12);
lean_inc(x_4);
x_19 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = l_Lean_Expr_hasMVar(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_free_object(x_19);
x_24 = lean_st_ref_take(x_4, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_25, 1);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_21);
x_32 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_31, x_10, x_21);
lean_ctor_set(x_26, 0, x_32);
x_33 = lean_st_ref_set(x_4, x_25, x_27);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_21);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_21);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 1);
x_40 = lean_ctor_get(x_26, 2);
x_41 = lean_ctor_get(x_26, 3);
x_42 = lean_ctor_get(x_26, 4);
x_43 = lean_ctor_get(x_26, 5);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_26);
lean_inc(x_21);
x_44 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_38, x_10, x_21);
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
lean_ctor_set(x_45, 2, x_40);
lean_ctor_set(x_45, 3, x_41);
lean_ctor_set(x_45, 4, x_42);
lean_ctor_set(x_45, 5, x_43);
lean_ctor_set(x_25, 1, x_45);
x_46 = lean_st_ref_set(x_4, x_25, x_27);
lean_dec(x_4);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_21);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_50 = lean_ctor_get(x_25, 0);
x_51 = lean_ctor_get(x_25, 2);
x_52 = lean_ctor_get(x_25, 3);
x_53 = lean_ctor_get(x_25, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_25);
x_54 = lean_ctor_get(x_26, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_26, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_26, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_26, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_26, 4);
lean_inc(x_58);
x_59 = lean_ctor_get(x_26, 5);
lean_inc(x_59);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 lean_ctor_release(x_26, 5);
 x_60 = x_26;
} else {
 lean_dec_ref(x_26);
 x_60 = lean_box(0);
}
lean_inc(x_21);
x_61 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_54, x_10, x_21);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 6, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_55);
lean_ctor_set(x_62, 2, x_56);
lean_ctor_set(x_62, 3, x_57);
lean_ctor_set(x_62, 4, x_58);
lean_ctor_set(x_62, 5, x_59);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_50);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_51);
lean_ctor_set(x_63, 3, x_52);
lean_ctor_set(x_63, 4, x_53);
x_64 = lean_st_ref_set(x_4, x_63, x_27);
lean_dec(x_4);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_21);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_dec(x_10);
lean_dec(x_4);
return x_19;
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_19, 0);
x_69 = lean_ctor_get(x_19, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_19);
x_70 = l_Lean_Expr_hasMVar(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_71 = lean_st_ref_take(x_4, x_69);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_72, 4);
lean_inc(x_78);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 x_79 = x_72;
} else {
 lean_dec_ref(x_72);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_73, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_73, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_73, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_73, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_73, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_73, 5);
lean_inc(x_85);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 lean_ctor_release(x_73, 3);
 lean_ctor_release(x_73, 4);
 lean_ctor_release(x_73, 5);
 x_86 = x_73;
} else {
 lean_dec_ref(x_73);
 x_86 = lean_box(0);
}
lean_inc(x_68);
x_87 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_80, x_10, x_68);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 6, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_81);
lean_ctor_set(x_88, 2, x_82);
lean_ctor_set(x_88, 3, x_83);
lean_ctor_set(x_88, 4, x_84);
lean_ctor_set(x_88, 5, x_85);
if (lean_is_scalar(x_79)) {
 x_89 = lean_alloc_ctor(0, 5, 0);
} else {
 x_89 = x_79;
}
lean_ctor_set(x_89, 0, x_75);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 2, x_76);
lean_ctor_set(x_89, 3, x_77);
lean_ctor_set(x_89, 4, x_78);
x_90 = lean_st_ref_set(x_4, x_89, x_74);
lean_dec(x_4);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_68);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
else
{
lean_object* x_94; 
lean_dec(x_10);
lean_dec(x_4);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_68);
lean_ctor_set(x_94, 1, x_69);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_10);
lean_dec(x_4);
x_95 = !lean_is_exclusive(x_19);
if (x_95 == 0)
{
return x_19;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_19, 0);
x_97 = lean_ctor_get(x_19, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_19);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_99 = lean_ctor_get(x_18, 0);
lean_inc(x_99);
lean_dec(x_18);
lean_ctor_set(x_12, 0, x_99);
return x_12;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_12, 0);
x_101 = lean_ctor_get(x_12, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_12);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_103, x_10);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
lean_inc(x_4);
x_105 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_101);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
x_109 = l_Lean_Expr_hasMVar(x_106);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_108);
x_110 = lean_st_ref_take(x_4, x_107);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_111, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 3);
lean_inc(x_116);
x_117 = lean_ctor_get(x_111, 4);
lean_inc(x_117);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 lean_ctor_release(x_111, 4);
 x_118 = x_111;
} else {
 lean_dec_ref(x_111);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_112, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_112, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_112, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_112, 3);
lean_inc(x_122);
x_123 = lean_ctor_get(x_112, 4);
lean_inc(x_123);
x_124 = lean_ctor_get(x_112, 5);
lean_inc(x_124);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 lean_ctor_release(x_112, 3);
 lean_ctor_release(x_112, 4);
 lean_ctor_release(x_112, 5);
 x_125 = x_112;
} else {
 lean_dec_ref(x_112);
 x_125 = lean_box(0);
}
lean_inc(x_106);
x_126 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_119, x_10, x_106);
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 6, 0);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_120);
lean_ctor_set(x_127, 2, x_121);
lean_ctor_set(x_127, 3, x_122);
lean_ctor_set(x_127, 4, x_123);
lean_ctor_set(x_127, 5, x_124);
if (lean_is_scalar(x_118)) {
 x_128 = lean_alloc_ctor(0, 5, 0);
} else {
 x_128 = x_118;
}
lean_ctor_set(x_128, 0, x_114);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_128, 2, x_115);
lean_ctor_set(x_128, 3, x_116);
lean_ctor_set(x_128, 4, x_117);
x_129 = lean_st_ref_set(x_4, x_128, x_113);
lean_dec(x_4);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_131 = x_129;
} else {
 lean_dec_ref(x_129);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_106);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
else
{
lean_object* x_133; 
lean_dec(x_10);
lean_dec(x_4);
if (lean_is_scalar(x_108)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_108;
}
lean_ctor_set(x_133, 0, x_106);
lean_ctor_set(x_133, 1, x_107);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_10);
lean_dec(x_4);
x_134 = lean_ctor_get(x_105, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_105, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_136 = x_105;
} else {
 lean_dec_ref(x_105);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_138 = lean_ctor_get(x_104, 0);
lean_inc(x_138);
lean_dec(x_104);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_101);
return x_139;
}
}
}
else
{
lean_object* x_140; 
lean_dec(x_1);
x_140 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_140;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__6(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static uint64_t _init_l_Lean_Meta_withInferTypeConfig___rarg___closed__1() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 1;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint64_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; 
x_10 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_2, 3);
x_15 = lean_ctor_get(x_2, 4);
x_16 = lean_ctor_get(x_2, 5);
x_17 = lean_ctor_get(x_2, 6);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
x_20 = lean_ctor_get_uint8(x_8, 0);
x_21 = lean_ctor_get_uint8(x_8, 1);
x_22 = lean_ctor_get_uint8(x_8, 2);
x_23 = lean_ctor_get_uint8(x_8, 3);
x_24 = lean_ctor_get_uint8(x_8, 4);
x_25 = lean_ctor_get_uint8(x_8, 5);
x_26 = lean_ctor_get_uint8(x_8, 6);
x_27 = lean_ctor_get_uint8(x_8, 7);
x_28 = lean_ctor_get_uint8(x_8, 8);
x_29 = lean_ctor_get_uint8(x_8, 9);
x_30 = lean_ctor_get_uint8(x_8, 10);
x_31 = lean_ctor_get_uint8(x_8, 11);
x_32 = 1;
x_33 = l_Lean_Meta_TransparencyMode_lt(x_29, x_32);
x_34 = 2;
x_35 = lean_uint64_shift_right(x_10, x_34);
x_36 = lean_uint64_shift_left(x_35, x_34);
if (x_33 == 0)
{
uint64_t x_37; uint64_t x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = l_Lean_Meta_TransparencyMode_toUInt64(x_29);
x_38 = lean_uint64_lor(x_36, x_37);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_38);
x_39 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_40, 13);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_40);
lean_dec(x_2);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = 1;
x_44 = 2;
x_45 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_45, 0, x_20);
lean_ctor_set_uint8(x_45, 1, x_21);
lean_ctor_set_uint8(x_45, 2, x_22);
lean_ctor_set_uint8(x_45, 3, x_23);
lean_ctor_set_uint8(x_45, 4, x_24);
lean_ctor_set_uint8(x_45, 5, x_25);
lean_ctor_set_uint8(x_45, 6, x_26);
lean_ctor_set_uint8(x_45, 7, x_27);
lean_ctor_set_uint8(x_45, 8, x_28);
lean_ctor_set_uint8(x_45, 9, x_29);
lean_ctor_set_uint8(x_45, 10, x_30);
lean_ctor_set_uint8(x_45, 11, x_31);
lean_ctor_set_uint8(x_45, 12, x_43);
lean_ctor_set_uint8(x_45, 13, x_43);
lean_ctor_set_uint8(x_45, 14, x_44);
lean_ctor_set_uint8(x_45, 15, x_43);
lean_ctor_set_uint8(x_45, 16, x_43);
x_46 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_45);
x_47 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_12);
lean_ctor_set(x_47, 2, x_13);
lean_ctor_set(x_47, 3, x_14);
lean_ctor_set(x_47, 4, x_15);
lean_ctor_set(x_47, 5, x_16);
lean_ctor_set(x_47, 6, x_17);
lean_ctor_set_uint64(x_47, sizeof(void*)*7, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_47, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_47, sizeof(void*)*7 + 10, x_19);
x_48 = lean_apply_5(x_1, x_47, x_3, x_4, x_5, x_42);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
return x_48;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_48, 0);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_48);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_40, 12);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; uint64_t x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_40);
lean_dec(x_2);
x_58 = lean_ctor_get(x_39, 1);
lean_inc(x_58);
lean_dec(x_39);
x_59 = 1;
x_60 = 2;
x_61 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_61, 0, x_20);
lean_ctor_set_uint8(x_61, 1, x_21);
lean_ctor_set_uint8(x_61, 2, x_22);
lean_ctor_set_uint8(x_61, 3, x_23);
lean_ctor_set_uint8(x_61, 4, x_24);
lean_ctor_set_uint8(x_61, 5, x_25);
lean_ctor_set_uint8(x_61, 6, x_26);
lean_ctor_set_uint8(x_61, 7, x_27);
lean_ctor_set_uint8(x_61, 8, x_28);
lean_ctor_set_uint8(x_61, 9, x_29);
lean_ctor_set_uint8(x_61, 10, x_30);
lean_ctor_set_uint8(x_61, 11, x_31);
lean_ctor_set_uint8(x_61, 12, x_59);
lean_ctor_set_uint8(x_61, 13, x_59);
lean_ctor_set_uint8(x_61, 14, x_60);
lean_ctor_set_uint8(x_61, 15, x_59);
lean_ctor_set_uint8(x_61, 16, x_59);
x_62 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_61);
x_63 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_12);
lean_ctor_set(x_63, 2, x_13);
lean_ctor_set(x_63, 3, x_14);
lean_ctor_set(x_63, 4, x_15);
lean_ctor_set(x_63, 5, x_16);
lean_ctor_set(x_63, 6, x_17);
lean_ctor_set_uint64(x_63, sizeof(void*)*7, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 10, x_19);
x_64 = lean_apply_5(x_1, x_63, x_3, x_4, x_5, x_58);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
return x_64;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_64);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_64);
if (x_69 == 0)
{
return x_64;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_64, 0);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_64);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
x_73 = lean_ctor_get_uint8(x_40, 15);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; uint64_t x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_40);
lean_dec(x_2);
x_74 = lean_ctor_get(x_39, 1);
lean_inc(x_74);
lean_dec(x_39);
x_75 = 1;
x_76 = 2;
x_77 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_77, 0, x_20);
lean_ctor_set_uint8(x_77, 1, x_21);
lean_ctor_set_uint8(x_77, 2, x_22);
lean_ctor_set_uint8(x_77, 3, x_23);
lean_ctor_set_uint8(x_77, 4, x_24);
lean_ctor_set_uint8(x_77, 5, x_25);
lean_ctor_set_uint8(x_77, 6, x_26);
lean_ctor_set_uint8(x_77, 7, x_27);
lean_ctor_set_uint8(x_77, 8, x_28);
lean_ctor_set_uint8(x_77, 9, x_29);
lean_ctor_set_uint8(x_77, 10, x_30);
lean_ctor_set_uint8(x_77, 11, x_31);
lean_ctor_set_uint8(x_77, 12, x_75);
lean_ctor_set_uint8(x_77, 13, x_75);
lean_ctor_set_uint8(x_77, 14, x_76);
lean_ctor_set_uint8(x_77, 15, x_75);
lean_ctor_set_uint8(x_77, 16, x_75);
x_78 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_77);
x_79 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_12);
lean_ctor_set(x_79, 2, x_13);
lean_ctor_set(x_79, 3, x_14);
lean_ctor_set(x_79, 4, x_15);
lean_ctor_set(x_79, 5, x_16);
lean_ctor_set(x_79, 6, x_17);
lean_ctor_set_uint64(x_79, sizeof(void*)*7, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 10, x_19);
x_80 = lean_apply_5(x_1, x_79, x_3, x_4, x_5, x_74);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
return x_80;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_80);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_80);
if (x_85 == 0)
{
return x_80;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_80, 0);
x_87 = lean_ctor_get(x_80, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_80);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
x_89 = lean_ctor_get_uint8(x_40, 16);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; uint8_t x_92; lean_object* x_93; uint64_t x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_40);
lean_dec(x_2);
x_90 = lean_ctor_get(x_39, 1);
lean_inc(x_90);
lean_dec(x_39);
x_91 = 1;
x_92 = 2;
x_93 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_93, 0, x_20);
lean_ctor_set_uint8(x_93, 1, x_21);
lean_ctor_set_uint8(x_93, 2, x_22);
lean_ctor_set_uint8(x_93, 3, x_23);
lean_ctor_set_uint8(x_93, 4, x_24);
lean_ctor_set_uint8(x_93, 5, x_25);
lean_ctor_set_uint8(x_93, 6, x_26);
lean_ctor_set_uint8(x_93, 7, x_27);
lean_ctor_set_uint8(x_93, 8, x_28);
lean_ctor_set_uint8(x_93, 9, x_29);
lean_ctor_set_uint8(x_93, 10, x_30);
lean_ctor_set_uint8(x_93, 11, x_31);
lean_ctor_set_uint8(x_93, 12, x_91);
lean_ctor_set_uint8(x_93, 13, x_91);
lean_ctor_set_uint8(x_93, 14, x_92);
lean_ctor_set_uint8(x_93, 15, x_91);
lean_ctor_set_uint8(x_93, 16, x_91);
x_94 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_93);
x_95 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_12);
lean_ctor_set(x_95, 2, x_13);
lean_ctor_set(x_95, 3, x_14);
lean_ctor_set(x_95, 4, x_15);
lean_ctor_set(x_95, 5, x_16);
lean_ctor_set(x_95, 6, x_17);
lean_ctor_set_uint64(x_95, sizeof(void*)*7, x_94);
lean_ctor_set_uint8(x_95, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_95, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_95, sizeof(void*)*7 + 10, x_19);
x_96 = lean_apply_5(x_1, x_95, x_3, x_4, x_5, x_90);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
return x_96;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_96);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
else
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_96);
if (x_101 == 0)
{
return x_96;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_96, 0);
x_103 = lean_ctor_get(x_96, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_96);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_39, 1);
lean_inc(x_105);
lean_dec(x_39);
x_106 = lean_ctor_get_uint8(x_40, 14);
lean_dec(x_40);
x_107 = 2;
x_108 = l_Lean_Meta_instDecidableEqProjReductionKind(x_106, x_107);
if (x_108 == 0)
{
uint8_t x_109; lean_object* x_110; uint64_t x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_2);
x_109 = 1;
x_110 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_110, 0, x_20);
lean_ctor_set_uint8(x_110, 1, x_21);
lean_ctor_set_uint8(x_110, 2, x_22);
lean_ctor_set_uint8(x_110, 3, x_23);
lean_ctor_set_uint8(x_110, 4, x_24);
lean_ctor_set_uint8(x_110, 5, x_25);
lean_ctor_set_uint8(x_110, 6, x_26);
lean_ctor_set_uint8(x_110, 7, x_27);
lean_ctor_set_uint8(x_110, 8, x_28);
lean_ctor_set_uint8(x_110, 9, x_29);
lean_ctor_set_uint8(x_110, 10, x_30);
lean_ctor_set_uint8(x_110, 11, x_31);
lean_ctor_set_uint8(x_110, 12, x_109);
lean_ctor_set_uint8(x_110, 13, x_109);
lean_ctor_set_uint8(x_110, 14, x_107);
lean_ctor_set_uint8(x_110, 15, x_109);
lean_ctor_set_uint8(x_110, 16, x_109);
x_111 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_110);
x_112 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_12);
lean_ctor_set(x_112, 2, x_13);
lean_ctor_set(x_112, 3, x_14);
lean_ctor_set(x_112, 4, x_15);
lean_ctor_set(x_112, 5, x_16);
lean_ctor_set(x_112, 6, x_17);
lean_ctor_set_uint64(x_112, sizeof(void*)*7, x_111);
lean_ctor_set_uint8(x_112, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_112, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_112, sizeof(void*)*7 + 10, x_19);
x_113 = lean_apply_5(x_1, x_112, x_3, x_4, x_5, x_105);
if (lean_obj_tag(x_113) == 0)
{
uint8_t x_114; 
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
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
else
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_113);
if (x_118 == 0)
{
return x_113;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_113, 0);
x_120 = lean_ctor_get(x_113, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_113);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
lean_object* x_122; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_122 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_105);
if (lean_obj_tag(x_122) == 0)
{
uint8_t x_123; 
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
return x_122;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_122, 0);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_122);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
else
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_122);
if (x_127 == 0)
{
return x_122;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_122, 0);
x_129 = lean_ctor_get(x_122, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_122);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
}
}
}
}
else
{
uint64_t x_131; uint64_t x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_ctor_set_uint8(x_8, 9, x_32);
x_131 = l_Lean_Meta_withInferTypeConfig___rarg___closed__1;
x_132 = lean_uint64_lor(x_36, x_131);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_132);
x_133 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get_uint8(x_134, 13);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; uint8_t x_138; lean_object* x_139; uint64_t x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_134);
lean_dec(x_2);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_137 = 1;
x_138 = 2;
x_139 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_139, 0, x_20);
lean_ctor_set_uint8(x_139, 1, x_21);
lean_ctor_set_uint8(x_139, 2, x_22);
lean_ctor_set_uint8(x_139, 3, x_23);
lean_ctor_set_uint8(x_139, 4, x_24);
lean_ctor_set_uint8(x_139, 5, x_25);
lean_ctor_set_uint8(x_139, 6, x_26);
lean_ctor_set_uint8(x_139, 7, x_27);
lean_ctor_set_uint8(x_139, 8, x_28);
lean_ctor_set_uint8(x_139, 9, x_32);
lean_ctor_set_uint8(x_139, 10, x_30);
lean_ctor_set_uint8(x_139, 11, x_31);
lean_ctor_set_uint8(x_139, 12, x_137);
lean_ctor_set_uint8(x_139, 13, x_137);
lean_ctor_set_uint8(x_139, 14, x_138);
lean_ctor_set_uint8(x_139, 15, x_137);
lean_ctor_set_uint8(x_139, 16, x_137);
x_140 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_139);
x_141 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_12);
lean_ctor_set(x_141, 2, x_13);
lean_ctor_set(x_141, 3, x_14);
lean_ctor_set(x_141, 4, x_15);
lean_ctor_set(x_141, 5, x_16);
lean_ctor_set(x_141, 6, x_17);
lean_ctor_set_uint64(x_141, sizeof(void*)*7, x_140);
lean_ctor_set_uint8(x_141, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_141, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_141, sizeof(void*)*7 + 10, x_19);
x_142 = lean_apply_5(x_1, x_141, x_3, x_4, x_5, x_136);
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
return x_142;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_142);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
else
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_142);
if (x_147 == 0)
{
return x_142;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_142, 0);
x_149 = lean_ctor_get(x_142, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_142);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; 
x_151 = lean_ctor_get_uint8(x_134, 12);
if (x_151 == 0)
{
lean_object* x_152; uint8_t x_153; uint8_t x_154; lean_object* x_155; uint64_t x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_134);
lean_dec(x_2);
x_152 = lean_ctor_get(x_133, 1);
lean_inc(x_152);
lean_dec(x_133);
x_153 = 1;
x_154 = 2;
x_155 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_155, 0, x_20);
lean_ctor_set_uint8(x_155, 1, x_21);
lean_ctor_set_uint8(x_155, 2, x_22);
lean_ctor_set_uint8(x_155, 3, x_23);
lean_ctor_set_uint8(x_155, 4, x_24);
lean_ctor_set_uint8(x_155, 5, x_25);
lean_ctor_set_uint8(x_155, 6, x_26);
lean_ctor_set_uint8(x_155, 7, x_27);
lean_ctor_set_uint8(x_155, 8, x_28);
lean_ctor_set_uint8(x_155, 9, x_32);
lean_ctor_set_uint8(x_155, 10, x_30);
lean_ctor_set_uint8(x_155, 11, x_31);
lean_ctor_set_uint8(x_155, 12, x_153);
lean_ctor_set_uint8(x_155, 13, x_153);
lean_ctor_set_uint8(x_155, 14, x_154);
lean_ctor_set_uint8(x_155, 15, x_153);
lean_ctor_set_uint8(x_155, 16, x_153);
x_156 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_155);
x_157 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_12);
lean_ctor_set(x_157, 2, x_13);
lean_ctor_set(x_157, 3, x_14);
lean_ctor_set(x_157, 4, x_15);
lean_ctor_set(x_157, 5, x_16);
lean_ctor_set(x_157, 6, x_17);
lean_ctor_set_uint64(x_157, sizeof(void*)*7, x_156);
lean_ctor_set_uint8(x_157, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_157, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_157, sizeof(void*)*7 + 10, x_19);
x_158 = lean_apply_5(x_1, x_157, x_3, x_4, x_5, x_152);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
return x_158;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_158, 0);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_158);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
else
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_158);
if (x_163 == 0)
{
return x_158;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_158, 0);
x_165 = lean_ctor_get(x_158, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_158);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
uint8_t x_167; 
x_167 = lean_ctor_get_uint8(x_134, 15);
if (x_167 == 0)
{
lean_object* x_168; uint8_t x_169; uint8_t x_170; lean_object* x_171; uint64_t x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_134);
lean_dec(x_2);
x_168 = lean_ctor_get(x_133, 1);
lean_inc(x_168);
lean_dec(x_133);
x_169 = 1;
x_170 = 2;
x_171 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_171, 0, x_20);
lean_ctor_set_uint8(x_171, 1, x_21);
lean_ctor_set_uint8(x_171, 2, x_22);
lean_ctor_set_uint8(x_171, 3, x_23);
lean_ctor_set_uint8(x_171, 4, x_24);
lean_ctor_set_uint8(x_171, 5, x_25);
lean_ctor_set_uint8(x_171, 6, x_26);
lean_ctor_set_uint8(x_171, 7, x_27);
lean_ctor_set_uint8(x_171, 8, x_28);
lean_ctor_set_uint8(x_171, 9, x_32);
lean_ctor_set_uint8(x_171, 10, x_30);
lean_ctor_set_uint8(x_171, 11, x_31);
lean_ctor_set_uint8(x_171, 12, x_169);
lean_ctor_set_uint8(x_171, 13, x_169);
lean_ctor_set_uint8(x_171, 14, x_170);
lean_ctor_set_uint8(x_171, 15, x_169);
lean_ctor_set_uint8(x_171, 16, x_169);
x_172 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_171);
x_173 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_12);
lean_ctor_set(x_173, 2, x_13);
lean_ctor_set(x_173, 3, x_14);
lean_ctor_set(x_173, 4, x_15);
lean_ctor_set(x_173, 5, x_16);
lean_ctor_set(x_173, 6, x_17);
lean_ctor_set_uint64(x_173, sizeof(void*)*7, x_172);
lean_ctor_set_uint8(x_173, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_173, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_173, sizeof(void*)*7 + 10, x_19);
x_174 = lean_apply_5(x_1, x_173, x_3, x_4, x_5, x_168);
if (lean_obj_tag(x_174) == 0)
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
return x_174;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_174, 0);
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_174);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
else
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_174);
if (x_179 == 0)
{
return x_174;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_174, 0);
x_181 = lean_ctor_get(x_174, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_174);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
else
{
uint8_t x_183; 
x_183 = lean_ctor_get_uint8(x_134, 16);
if (x_183 == 0)
{
lean_object* x_184; uint8_t x_185; uint8_t x_186; lean_object* x_187; uint64_t x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_134);
lean_dec(x_2);
x_184 = lean_ctor_get(x_133, 1);
lean_inc(x_184);
lean_dec(x_133);
x_185 = 1;
x_186 = 2;
x_187 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_187, 0, x_20);
lean_ctor_set_uint8(x_187, 1, x_21);
lean_ctor_set_uint8(x_187, 2, x_22);
lean_ctor_set_uint8(x_187, 3, x_23);
lean_ctor_set_uint8(x_187, 4, x_24);
lean_ctor_set_uint8(x_187, 5, x_25);
lean_ctor_set_uint8(x_187, 6, x_26);
lean_ctor_set_uint8(x_187, 7, x_27);
lean_ctor_set_uint8(x_187, 8, x_28);
lean_ctor_set_uint8(x_187, 9, x_32);
lean_ctor_set_uint8(x_187, 10, x_30);
lean_ctor_set_uint8(x_187, 11, x_31);
lean_ctor_set_uint8(x_187, 12, x_185);
lean_ctor_set_uint8(x_187, 13, x_185);
lean_ctor_set_uint8(x_187, 14, x_186);
lean_ctor_set_uint8(x_187, 15, x_185);
lean_ctor_set_uint8(x_187, 16, x_185);
x_188 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_187);
x_189 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_12);
lean_ctor_set(x_189, 2, x_13);
lean_ctor_set(x_189, 3, x_14);
lean_ctor_set(x_189, 4, x_15);
lean_ctor_set(x_189, 5, x_16);
lean_ctor_set(x_189, 6, x_17);
lean_ctor_set_uint64(x_189, sizeof(void*)*7, x_188);
lean_ctor_set_uint8(x_189, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_189, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_189, sizeof(void*)*7 + 10, x_19);
x_190 = lean_apply_5(x_1, x_189, x_3, x_4, x_5, x_184);
if (lean_obj_tag(x_190) == 0)
{
uint8_t x_191; 
x_191 = !lean_is_exclusive(x_190);
if (x_191 == 0)
{
return x_190;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_190, 0);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_190);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
else
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_190);
if (x_195 == 0)
{
return x_190;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_190, 0);
x_197 = lean_ctor_get(x_190, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_190);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
lean_object* x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; 
x_199 = lean_ctor_get(x_133, 1);
lean_inc(x_199);
lean_dec(x_133);
x_200 = lean_ctor_get_uint8(x_134, 14);
lean_dec(x_134);
x_201 = 2;
x_202 = l_Lean_Meta_instDecidableEqProjReductionKind(x_200, x_201);
if (x_202 == 0)
{
uint8_t x_203; lean_object* x_204; uint64_t x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_2);
x_203 = 1;
x_204 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_204, 0, x_20);
lean_ctor_set_uint8(x_204, 1, x_21);
lean_ctor_set_uint8(x_204, 2, x_22);
lean_ctor_set_uint8(x_204, 3, x_23);
lean_ctor_set_uint8(x_204, 4, x_24);
lean_ctor_set_uint8(x_204, 5, x_25);
lean_ctor_set_uint8(x_204, 6, x_26);
lean_ctor_set_uint8(x_204, 7, x_27);
lean_ctor_set_uint8(x_204, 8, x_28);
lean_ctor_set_uint8(x_204, 9, x_32);
lean_ctor_set_uint8(x_204, 10, x_30);
lean_ctor_set_uint8(x_204, 11, x_31);
lean_ctor_set_uint8(x_204, 12, x_203);
lean_ctor_set_uint8(x_204, 13, x_203);
lean_ctor_set_uint8(x_204, 14, x_201);
lean_ctor_set_uint8(x_204, 15, x_203);
lean_ctor_set_uint8(x_204, 16, x_203);
x_205 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_204);
x_206 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_12);
lean_ctor_set(x_206, 2, x_13);
lean_ctor_set(x_206, 3, x_14);
lean_ctor_set(x_206, 4, x_15);
lean_ctor_set(x_206, 5, x_16);
lean_ctor_set(x_206, 6, x_17);
lean_ctor_set_uint64(x_206, sizeof(void*)*7, x_205);
lean_ctor_set_uint8(x_206, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_206, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_206, sizeof(void*)*7 + 10, x_19);
x_207 = lean_apply_5(x_1, x_206, x_3, x_4, x_5, x_199);
if (lean_obj_tag(x_207) == 0)
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
return x_207;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_207, 0);
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_207);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
else
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_207);
if (x_212 == 0)
{
return x_207;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_207, 0);
x_214 = lean_ctor_get(x_207, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_207);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
else
{
lean_object* x_216; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_216 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_199);
if (lean_obj_tag(x_216) == 0)
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_216);
if (x_217 == 0)
{
return x_216;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_216, 0);
x_219 = lean_ctor_get(x_216, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_216);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
else
{
uint8_t x_221; 
x_221 = !lean_is_exclusive(x_216);
if (x_221 == 0)
{
return x_216;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_216, 0);
x_223 = lean_ctor_get(x_216, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_216);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
}
}
}
}
}
}
else
{
uint64_t x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; uint8_t x_234; uint8_t x_235; uint8_t x_236; uint8_t x_237; uint8_t x_238; uint8_t x_239; uint8_t x_240; uint8_t x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; uint8_t x_245; uint8_t x_246; uint8_t x_247; uint8_t x_248; uint8_t x_249; uint8_t x_250; uint8_t x_251; uint8_t x_252; uint8_t x_253; uint64_t x_254; uint64_t x_255; uint64_t x_256; 
x_225 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_226 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_227 = lean_ctor_get(x_2, 1);
x_228 = lean_ctor_get(x_2, 2);
x_229 = lean_ctor_get(x_2, 3);
x_230 = lean_ctor_get(x_2, 4);
x_231 = lean_ctor_get(x_2, 5);
x_232 = lean_ctor_get(x_2, 6);
x_233 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_234 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
x_235 = lean_ctor_get_uint8(x_8, 0);
x_236 = lean_ctor_get_uint8(x_8, 1);
x_237 = lean_ctor_get_uint8(x_8, 2);
x_238 = lean_ctor_get_uint8(x_8, 3);
x_239 = lean_ctor_get_uint8(x_8, 4);
x_240 = lean_ctor_get_uint8(x_8, 5);
x_241 = lean_ctor_get_uint8(x_8, 6);
x_242 = lean_ctor_get_uint8(x_8, 7);
x_243 = lean_ctor_get_uint8(x_8, 8);
x_244 = lean_ctor_get_uint8(x_8, 9);
x_245 = lean_ctor_get_uint8(x_8, 10);
x_246 = lean_ctor_get_uint8(x_8, 11);
x_247 = lean_ctor_get_uint8(x_8, 12);
x_248 = lean_ctor_get_uint8(x_8, 13);
x_249 = lean_ctor_get_uint8(x_8, 14);
x_250 = lean_ctor_get_uint8(x_8, 15);
x_251 = lean_ctor_get_uint8(x_8, 16);
lean_dec(x_8);
x_252 = 1;
x_253 = l_Lean_Meta_TransparencyMode_lt(x_244, x_252);
x_254 = 2;
x_255 = lean_uint64_shift_right(x_225, x_254);
x_256 = lean_uint64_shift_left(x_255, x_254);
if (x_253 == 0)
{
lean_object* x_257; uint64_t x_258; uint64_t x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_257 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_257, 0, x_235);
lean_ctor_set_uint8(x_257, 1, x_236);
lean_ctor_set_uint8(x_257, 2, x_237);
lean_ctor_set_uint8(x_257, 3, x_238);
lean_ctor_set_uint8(x_257, 4, x_239);
lean_ctor_set_uint8(x_257, 5, x_240);
lean_ctor_set_uint8(x_257, 6, x_241);
lean_ctor_set_uint8(x_257, 7, x_242);
lean_ctor_set_uint8(x_257, 8, x_243);
lean_ctor_set_uint8(x_257, 9, x_244);
lean_ctor_set_uint8(x_257, 10, x_245);
lean_ctor_set_uint8(x_257, 11, x_246);
lean_ctor_set_uint8(x_257, 12, x_247);
lean_ctor_set_uint8(x_257, 13, x_248);
lean_ctor_set_uint8(x_257, 14, x_249);
lean_ctor_set_uint8(x_257, 15, x_250);
lean_ctor_set_uint8(x_257, 16, x_251);
x_258 = l_Lean_Meta_TransparencyMode_toUInt64(x_244);
x_259 = lean_uint64_lor(x_256, x_258);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_ctor_set(x_2, 0, x_257);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_259);
x_260 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get_uint8(x_261, 13);
if (x_262 == 0)
{
lean_object* x_263; uint8_t x_264; uint8_t x_265; lean_object* x_266; uint64_t x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_261);
lean_dec(x_2);
x_263 = lean_ctor_get(x_260, 1);
lean_inc(x_263);
lean_dec(x_260);
x_264 = 1;
x_265 = 2;
x_266 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_266, 0, x_235);
lean_ctor_set_uint8(x_266, 1, x_236);
lean_ctor_set_uint8(x_266, 2, x_237);
lean_ctor_set_uint8(x_266, 3, x_238);
lean_ctor_set_uint8(x_266, 4, x_239);
lean_ctor_set_uint8(x_266, 5, x_240);
lean_ctor_set_uint8(x_266, 6, x_241);
lean_ctor_set_uint8(x_266, 7, x_242);
lean_ctor_set_uint8(x_266, 8, x_243);
lean_ctor_set_uint8(x_266, 9, x_244);
lean_ctor_set_uint8(x_266, 10, x_245);
lean_ctor_set_uint8(x_266, 11, x_246);
lean_ctor_set_uint8(x_266, 12, x_264);
lean_ctor_set_uint8(x_266, 13, x_264);
lean_ctor_set_uint8(x_266, 14, x_265);
lean_ctor_set_uint8(x_266, 15, x_264);
lean_ctor_set_uint8(x_266, 16, x_264);
x_267 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_266);
x_268 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_227);
lean_ctor_set(x_268, 2, x_228);
lean_ctor_set(x_268, 3, x_229);
lean_ctor_set(x_268, 4, x_230);
lean_ctor_set(x_268, 5, x_231);
lean_ctor_set(x_268, 6, x_232);
lean_ctor_set_uint64(x_268, sizeof(void*)*7, x_267);
lean_ctor_set_uint8(x_268, sizeof(void*)*7 + 8, x_226);
lean_ctor_set_uint8(x_268, sizeof(void*)*7 + 9, x_233);
lean_ctor_set_uint8(x_268, sizeof(void*)*7 + 10, x_234);
x_269 = lean_apply_5(x_1, x_268, x_3, x_4, x_5, x_263);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_272 = x_269;
} else {
 lean_dec_ref(x_269);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_271);
return x_273;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_274 = lean_ctor_get(x_269, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_269, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_276 = x_269;
} else {
 lean_dec_ref(x_269);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_274);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
else
{
uint8_t x_278; 
x_278 = lean_ctor_get_uint8(x_261, 12);
if (x_278 == 0)
{
lean_object* x_279; uint8_t x_280; uint8_t x_281; lean_object* x_282; uint64_t x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_261);
lean_dec(x_2);
x_279 = lean_ctor_get(x_260, 1);
lean_inc(x_279);
lean_dec(x_260);
x_280 = 1;
x_281 = 2;
x_282 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_282, 0, x_235);
lean_ctor_set_uint8(x_282, 1, x_236);
lean_ctor_set_uint8(x_282, 2, x_237);
lean_ctor_set_uint8(x_282, 3, x_238);
lean_ctor_set_uint8(x_282, 4, x_239);
lean_ctor_set_uint8(x_282, 5, x_240);
lean_ctor_set_uint8(x_282, 6, x_241);
lean_ctor_set_uint8(x_282, 7, x_242);
lean_ctor_set_uint8(x_282, 8, x_243);
lean_ctor_set_uint8(x_282, 9, x_244);
lean_ctor_set_uint8(x_282, 10, x_245);
lean_ctor_set_uint8(x_282, 11, x_246);
lean_ctor_set_uint8(x_282, 12, x_280);
lean_ctor_set_uint8(x_282, 13, x_280);
lean_ctor_set_uint8(x_282, 14, x_281);
lean_ctor_set_uint8(x_282, 15, x_280);
lean_ctor_set_uint8(x_282, 16, x_280);
x_283 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_282);
x_284 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_227);
lean_ctor_set(x_284, 2, x_228);
lean_ctor_set(x_284, 3, x_229);
lean_ctor_set(x_284, 4, x_230);
lean_ctor_set(x_284, 5, x_231);
lean_ctor_set(x_284, 6, x_232);
lean_ctor_set_uint64(x_284, sizeof(void*)*7, x_283);
lean_ctor_set_uint8(x_284, sizeof(void*)*7 + 8, x_226);
lean_ctor_set_uint8(x_284, sizeof(void*)*7 + 9, x_233);
lean_ctor_set_uint8(x_284, sizeof(void*)*7 + 10, x_234);
x_285 = lean_apply_5(x_1, x_284, x_3, x_4, x_5, x_279);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_288 = x_285;
} else {
 lean_dec_ref(x_285);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
return x_289;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_290 = lean_ctor_get(x_285, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_285, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_292 = x_285;
} else {
 lean_dec_ref(x_285);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
}
else
{
uint8_t x_294; 
x_294 = lean_ctor_get_uint8(x_261, 15);
if (x_294 == 0)
{
lean_object* x_295; uint8_t x_296; uint8_t x_297; lean_object* x_298; uint64_t x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_261);
lean_dec(x_2);
x_295 = lean_ctor_get(x_260, 1);
lean_inc(x_295);
lean_dec(x_260);
x_296 = 1;
x_297 = 2;
x_298 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_298, 0, x_235);
lean_ctor_set_uint8(x_298, 1, x_236);
lean_ctor_set_uint8(x_298, 2, x_237);
lean_ctor_set_uint8(x_298, 3, x_238);
lean_ctor_set_uint8(x_298, 4, x_239);
lean_ctor_set_uint8(x_298, 5, x_240);
lean_ctor_set_uint8(x_298, 6, x_241);
lean_ctor_set_uint8(x_298, 7, x_242);
lean_ctor_set_uint8(x_298, 8, x_243);
lean_ctor_set_uint8(x_298, 9, x_244);
lean_ctor_set_uint8(x_298, 10, x_245);
lean_ctor_set_uint8(x_298, 11, x_246);
lean_ctor_set_uint8(x_298, 12, x_296);
lean_ctor_set_uint8(x_298, 13, x_296);
lean_ctor_set_uint8(x_298, 14, x_297);
lean_ctor_set_uint8(x_298, 15, x_296);
lean_ctor_set_uint8(x_298, 16, x_296);
x_299 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_298);
x_300 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_227);
lean_ctor_set(x_300, 2, x_228);
lean_ctor_set(x_300, 3, x_229);
lean_ctor_set(x_300, 4, x_230);
lean_ctor_set(x_300, 5, x_231);
lean_ctor_set(x_300, 6, x_232);
lean_ctor_set_uint64(x_300, sizeof(void*)*7, x_299);
lean_ctor_set_uint8(x_300, sizeof(void*)*7 + 8, x_226);
lean_ctor_set_uint8(x_300, sizeof(void*)*7 + 9, x_233);
lean_ctor_set_uint8(x_300, sizeof(void*)*7 + 10, x_234);
x_301 = lean_apply_5(x_1, x_300, x_3, x_4, x_5, x_295);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_304 = x_301;
} else {
 lean_dec_ref(x_301);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_302);
lean_ctor_set(x_305, 1, x_303);
return x_305;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_306 = lean_ctor_get(x_301, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_301, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_308 = x_301;
} else {
 lean_dec_ref(x_301);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
else
{
uint8_t x_310; 
x_310 = lean_ctor_get_uint8(x_261, 16);
if (x_310 == 0)
{
lean_object* x_311; uint8_t x_312; uint8_t x_313; lean_object* x_314; uint64_t x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_261);
lean_dec(x_2);
x_311 = lean_ctor_get(x_260, 1);
lean_inc(x_311);
lean_dec(x_260);
x_312 = 1;
x_313 = 2;
x_314 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_314, 0, x_235);
lean_ctor_set_uint8(x_314, 1, x_236);
lean_ctor_set_uint8(x_314, 2, x_237);
lean_ctor_set_uint8(x_314, 3, x_238);
lean_ctor_set_uint8(x_314, 4, x_239);
lean_ctor_set_uint8(x_314, 5, x_240);
lean_ctor_set_uint8(x_314, 6, x_241);
lean_ctor_set_uint8(x_314, 7, x_242);
lean_ctor_set_uint8(x_314, 8, x_243);
lean_ctor_set_uint8(x_314, 9, x_244);
lean_ctor_set_uint8(x_314, 10, x_245);
lean_ctor_set_uint8(x_314, 11, x_246);
lean_ctor_set_uint8(x_314, 12, x_312);
lean_ctor_set_uint8(x_314, 13, x_312);
lean_ctor_set_uint8(x_314, 14, x_313);
lean_ctor_set_uint8(x_314, 15, x_312);
lean_ctor_set_uint8(x_314, 16, x_312);
x_315 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_314);
x_316 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_227);
lean_ctor_set(x_316, 2, x_228);
lean_ctor_set(x_316, 3, x_229);
lean_ctor_set(x_316, 4, x_230);
lean_ctor_set(x_316, 5, x_231);
lean_ctor_set(x_316, 6, x_232);
lean_ctor_set_uint64(x_316, sizeof(void*)*7, x_315);
lean_ctor_set_uint8(x_316, sizeof(void*)*7 + 8, x_226);
lean_ctor_set_uint8(x_316, sizeof(void*)*7 + 9, x_233);
lean_ctor_set_uint8(x_316, sizeof(void*)*7 + 10, x_234);
x_317 = lean_apply_5(x_1, x_316, x_3, x_4, x_5, x_311);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_320 = x_317;
} else {
 lean_dec_ref(x_317);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_319);
return x_321;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_322 = lean_ctor_get(x_317, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_317, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_324 = x_317;
} else {
 lean_dec_ref(x_317);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(1, 2, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_322);
lean_ctor_set(x_325, 1, x_323);
return x_325;
}
}
else
{
lean_object* x_326; uint8_t x_327; uint8_t x_328; uint8_t x_329; 
x_326 = lean_ctor_get(x_260, 1);
lean_inc(x_326);
lean_dec(x_260);
x_327 = lean_ctor_get_uint8(x_261, 14);
lean_dec(x_261);
x_328 = 2;
x_329 = l_Lean_Meta_instDecidableEqProjReductionKind(x_327, x_328);
if (x_329 == 0)
{
uint8_t x_330; lean_object* x_331; uint64_t x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_2);
x_330 = 1;
x_331 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_331, 0, x_235);
lean_ctor_set_uint8(x_331, 1, x_236);
lean_ctor_set_uint8(x_331, 2, x_237);
lean_ctor_set_uint8(x_331, 3, x_238);
lean_ctor_set_uint8(x_331, 4, x_239);
lean_ctor_set_uint8(x_331, 5, x_240);
lean_ctor_set_uint8(x_331, 6, x_241);
lean_ctor_set_uint8(x_331, 7, x_242);
lean_ctor_set_uint8(x_331, 8, x_243);
lean_ctor_set_uint8(x_331, 9, x_244);
lean_ctor_set_uint8(x_331, 10, x_245);
lean_ctor_set_uint8(x_331, 11, x_246);
lean_ctor_set_uint8(x_331, 12, x_330);
lean_ctor_set_uint8(x_331, 13, x_330);
lean_ctor_set_uint8(x_331, 14, x_328);
lean_ctor_set_uint8(x_331, 15, x_330);
lean_ctor_set_uint8(x_331, 16, x_330);
x_332 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_331);
x_333 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_227);
lean_ctor_set(x_333, 2, x_228);
lean_ctor_set(x_333, 3, x_229);
lean_ctor_set(x_333, 4, x_230);
lean_ctor_set(x_333, 5, x_231);
lean_ctor_set(x_333, 6, x_232);
lean_ctor_set_uint64(x_333, sizeof(void*)*7, x_332);
lean_ctor_set_uint8(x_333, sizeof(void*)*7 + 8, x_226);
lean_ctor_set_uint8(x_333, sizeof(void*)*7 + 9, x_233);
lean_ctor_set_uint8(x_333, sizeof(void*)*7 + 10, x_234);
x_334 = lean_apply_5(x_1, x_333, x_3, x_4, x_5, x_326);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_337 = x_334;
} else {
 lean_dec_ref(x_334);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(0, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_336);
return x_338;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_339 = lean_ctor_get(x_334, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_334, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_341 = x_334;
} else {
 lean_dec_ref(x_334);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(1, 2, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_339);
lean_ctor_set(x_342, 1, x_340);
return x_342;
}
}
else
{
lean_object* x_343; 
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
x_343 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_326);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_346 = x_343;
} else {
 lean_dec_ref(x_343);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(0, 2, 0);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_344);
lean_ctor_set(x_347, 1, x_345);
return x_347;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_348 = lean_ctor_get(x_343, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_343, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_350 = x_343;
} else {
 lean_dec_ref(x_343);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(1, 2, 0);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_348);
lean_ctor_set(x_351, 1, x_349);
return x_351;
}
}
}
}
}
}
}
else
{
lean_object* x_352; uint64_t x_353; uint64_t x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_352 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_352, 0, x_235);
lean_ctor_set_uint8(x_352, 1, x_236);
lean_ctor_set_uint8(x_352, 2, x_237);
lean_ctor_set_uint8(x_352, 3, x_238);
lean_ctor_set_uint8(x_352, 4, x_239);
lean_ctor_set_uint8(x_352, 5, x_240);
lean_ctor_set_uint8(x_352, 6, x_241);
lean_ctor_set_uint8(x_352, 7, x_242);
lean_ctor_set_uint8(x_352, 8, x_243);
lean_ctor_set_uint8(x_352, 9, x_252);
lean_ctor_set_uint8(x_352, 10, x_245);
lean_ctor_set_uint8(x_352, 11, x_246);
lean_ctor_set_uint8(x_352, 12, x_247);
lean_ctor_set_uint8(x_352, 13, x_248);
lean_ctor_set_uint8(x_352, 14, x_249);
lean_ctor_set_uint8(x_352, 15, x_250);
lean_ctor_set_uint8(x_352, 16, x_251);
x_353 = l_Lean_Meta_withInferTypeConfig___rarg___closed__1;
x_354 = lean_uint64_lor(x_256, x_353);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_ctor_set(x_2, 0, x_352);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_354);
x_355 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get_uint8(x_356, 13);
if (x_357 == 0)
{
lean_object* x_358; uint8_t x_359; uint8_t x_360; lean_object* x_361; uint64_t x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_356);
lean_dec(x_2);
x_358 = lean_ctor_get(x_355, 1);
lean_inc(x_358);
lean_dec(x_355);
x_359 = 1;
x_360 = 2;
x_361 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_361, 0, x_235);
lean_ctor_set_uint8(x_361, 1, x_236);
lean_ctor_set_uint8(x_361, 2, x_237);
lean_ctor_set_uint8(x_361, 3, x_238);
lean_ctor_set_uint8(x_361, 4, x_239);
lean_ctor_set_uint8(x_361, 5, x_240);
lean_ctor_set_uint8(x_361, 6, x_241);
lean_ctor_set_uint8(x_361, 7, x_242);
lean_ctor_set_uint8(x_361, 8, x_243);
lean_ctor_set_uint8(x_361, 9, x_252);
lean_ctor_set_uint8(x_361, 10, x_245);
lean_ctor_set_uint8(x_361, 11, x_246);
lean_ctor_set_uint8(x_361, 12, x_359);
lean_ctor_set_uint8(x_361, 13, x_359);
lean_ctor_set_uint8(x_361, 14, x_360);
lean_ctor_set_uint8(x_361, 15, x_359);
lean_ctor_set_uint8(x_361, 16, x_359);
x_362 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_361);
x_363 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_227);
lean_ctor_set(x_363, 2, x_228);
lean_ctor_set(x_363, 3, x_229);
lean_ctor_set(x_363, 4, x_230);
lean_ctor_set(x_363, 5, x_231);
lean_ctor_set(x_363, 6, x_232);
lean_ctor_set_uint64(x_363, sizeof(void*)*7, x_362);
lean_ctor_set_uint8(x_363, sizeof(void*)*7 + 8, x_226);
lean_ctor_set_uint8(x_363, sizeof(void*)*7 + 9, x_233);
lean_ctor_set_uint8(x_363, sizeof(void*)*7 + 10, x_234);
x_364 = lean_apply_5(x_1, x_363, x_3, x_4, x_5, x_358);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_367 = x_364;
} else {
 lean_dec_ref(x_364);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_365);
lean_ctor_set(x_368, 1, x_366);
return x_368;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_369 = lean_ctor_get(x_364, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_364, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_371 = x_364;
} else {
 lean_dec_ref(x_364);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(1, 2, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_369);
lean_ctor_set(x_372, 1, x_370);
return x_372;
}
}
else
{
uint8_t x_373; 
x_373 = lean_ctor_get_uint8(x_356, 12);
if (x_373 == 0)
{
lean_object* x_374; uint8_t x_375; uint8_t x_376; lean_object* x_377; uint64_t x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_356);
lean_dec(x_2);
x_374 = lean_ctor_get(x_355, 1);
lean_inc(x_374);
lean_dec(x_355);
x_375 = 1;
x_376 = 2;
x_377 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_377, 0, x_235);
lean_ctor_set_uint8(x_377, 1, x_236);
lean_ctor_set_uint8(x_377, 2, x_237);
lean_ctor_set_uint8(x_377, 3, x_238);
lean_ctor_set_uint8(x_377, 4, x_239);
lean_ctor_set_uint8(x_377, 5, x_240);
lean_ctor_set_uint8(x_377, 6, x_241);
lean_ctor_set_uint8(x_377, 7, x_242);
lean_ctor_set_uint8(x_377, 8, x_243);
lean_ctor_set_uint8(x_377, 9, x_252);
lean_ctor_set_uint8(x_377, 10, x_245);
lean_ctor_set_uint8(x_377, 11, x_246);
lean_ctor_set_uint8(x_377, 12, x_375);
lean_ctor_set_uint8(x_377, 13, x_375);
lean_ctor_set_uint8(x_377, 14, x_376);
lean_ctor_set_uint8(x_377, 15, x_375);
lean_ctor_set_uint8(x_377, 16, x_375);
x_378 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_377);
x_379 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_227);
lean_ctor_set(x_379, 2, x_228);
lean_ctor_set(x_379, 3, x_229);
lean_ctor_set(x_379, 4, x_230);
lean_ctor_set(x_379, 5, x_231);
lean_ctor_set(x_379, 6, x_232);
lean_ctor_set_uint64(x_379, sizeof(void*)*7, x_378);
lean_ctor_set_uint8(x_379, sizeof(void*)*7 + 8, x_226);
lean_ctor_set_uint8(x_379, sizeof(void*)*7 + 9, x_233);
lean_ctor_set_uint8(x_379, sizeof(void*)*7 + 10, x_234);
x_380 = lean_apply_5(x_1, x_379, x_3, x_4, x_5, x_374);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_383 = x_380;
} else {
 lean_dec_ref(x_380);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_382);
return x_384;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_385 = lean_ctor_get(x_380, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_380, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_387 = x_380;
} else {
 lean_dec_ref(x_380);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 2, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_386);
return x_388;
}
}
else
{
uint8_t x_389; 
x_389 = lean_ctor_get_uint8(x_356, 15);
if (x_389 == 0)
{
lean_object* x_390; uint8_t x_391; uint8_t x_392; lean_object* x_393; uint64_t x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_356);
lean_dec(x_2);
x_390 = lean_ctor_get(x_355, 1);
lean_inc(x_390);
lean_dec(x_355);
x_391 = 1;
x_392 = 2;
x_393 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_393, 0, x_235);
lean_ctor_set_uint8(x_393, 1, x_236);
lean_ctor_set_uint8(x_393, 2, x_237);
lean_ctor_set_uint8(x_393, 3, x_238);
lean_ctor_set_uint8(x_393, 4, x_239);
lean_ctor_set_uint8(x_393, 5, x_240);
lean_ctor_set_uint8(x_393, 6, x_241);
lean_ctor_set_uint8(x_393, 7, x_242);
lean_ctor_set_uint8(x_393, 8, x_243);
lean_ctor_set_uint8(x_393, 9, x_252);
lean_ctor_set_uint8(x_393, 10, x_245);
lean_ctor_set_uint8(x_393, 11, x_246);
lean_ctor_set_uint8(x_393, 12, x_391);
lean_ctor_set_uint8(x_393, 13, x_391);
lean_ctor_set_uint8(x_393, 14, x_392);
lean_ctor_set_uint8(x_393, 15, x_391);
lean_ctor_set_uint8(x_393, 16, x_391);
x_394 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_393);
x_395 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_227);
lean_ctor_set(x_395, 2, x_228);
lean_ctor_set(x_395, 3, x_229);
lean_ctor_set(x_395, 4, x_230);
lean_ctor_set(x_395, 5, x_231);
lean_ctor_set(x_395, 6, x_232);
lean_ctor_set_uint64(x_395, sizeof(void*)*7, x_394);
lean_ctor_set_uint8(x_395, sizeof(void*)*7 + 8, x_226);
lean_ctor_set_uint8(x_395, sizeof(void*)*7 + 9, x_233);
lean_ctor_set_uint8(x_395, sizeof(void*)*7 + 10, x_234);
x_396 = lean_apply_5(x_1, x_395, x_3, x_4, x_5, x_390);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_399 = x_396;
} else {
 lean_dec_ref(x_396);
 x_399 = lean_box(0);
}
if (lean_is_scalar(x_399)) {
 x_400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_400 = x_399;
}
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_398);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_401 = lean_ctor_get(x_396, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_396, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_403 = x_396;
} else {
 lean_dec_ref(x_396);
 x_403 = lean_box(0);
}
if (lean_is_scalar(x_403)) {
 x_404 = lean_alloc_ctor(1, 2, 0);
} else {
 x_404 = x_403;
}
lean_ctor_set(x_404, 0, x_401);
lean_ctor_set(x_404, 1, x_402);
return x_404;
}
}
else
{
uint8_t x_405; 
x_405 = lean_ctor_get_uint8(x_356, 16);
if (x_405 == 0)
{
lean_object* x_406; uint8_t x_407; uint8_t x_408; lean_object* x_409; uint64_t x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_356);
lean_dec(x_2);
x_406 = lean_ctor_get(x_355, 1);
lean_inc(x_406);
lean_dec(x_355);
x_407 = 1;
x_408 = 2;
x_409 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_409, 0, x_235);
lean_ctor_set_uint8(x_409, 1, x_236);
lean_ctor_set_uint8(x_409, 2, x_237);
lean_ctor_set_uint8(x_409, 3, x_238);
lean_ctor_set_uint8(x_409, 4, x_239);
lean_ctor_set_uint8(x_409, 5, x_240);
lean_ctor_set_uint8(x_409, 6, x_241);
lean_ctor_set_uint8(x_409, 7, x_242);
lean_ctor_set_uint8(x_409, 8, x_243);
lean_ctor_set_uint8(x_409, 9, x_252);
lean_ctor_set_uint8(x_409, 10, x_245);
lean_ctor_set_uint8(x_409, 11, x_246);
lean_ctor_set_uint8(x_409, 12, x_407);
lean_ctor_set_uint8(x_409, 13, x_407);
lean_ctor_set_uint8(x_409, 14, x_408);
lean_ctor_set_uint8(x_409, 15, x_407);
lean_ctor_set_uint8(x_409, 16, x_407);
x_410 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_409);
x_411 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_227);
lean_ctor_set(x_411, 2, x_228);
lean_ctor_set(x_411, 3, x_229);
lean_ctor_set(x_411, 4, x_230);
lean_ctor_set(x_411, 5, x_231);
lean_ctor_set(x_411, 6, x_232);
lean_ctor_set_uint64(x_411, sizeof(void*)*7, x_410);
lean_ctor_set_uint8(x_411, sizeof(void*)*7 + 8, x_226);
lean_ctor_set_uint8(x_411, sizeof(void*)*7 + 9, x_233);
lean_ctor_set_uint8(x_411, sizeof(void*)*7 + 10, x_234);
x_412 = lean_apply_5(x_1, x_411, x_3, x_4, x_5, x_406);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 x_415 = x_412;
} else {
 lean_dec_ref(x_412);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_414);
return x_416;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_417 = lean_ctor_get(x_412, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_412, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 x_419 = x_412;
} else {
 lean_dec_ref(x_412);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(1, 2, 0);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_418);
return x_420;
}
}
else
{
lean_object* x_421; uint8_t x_422; uint8_t x_423; uint8_t x_424; 
x_421 = lean_ctor_get(x_355, 1);
lean_inc(x_421);
lean_dec(x_355);
x_422 = lean_ctor_get_uint8(x_356, 14);
lean_dec(x_356);
x_423 = 2;
x_424 = l_Lean_Meta_instDecidableEqProjReductionKind(x_422, x_423);
if (x_424 == 0)
{
uint8_t x_425; lean_object* x_426; uint64_t x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_2);
x_425 = 1;
x_426 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_426, 0, x_235);
lean_ctor_set_uint8(x_426, 1, x_236);
lean_ctor_set_uint8(x_426, 2, x_237);
lean_ctor_set_uint8(x_426, 3, x_238);
lean_ctor_set_uint8(x_426, 4, x_239);
lean_ctor_set_uint8(x_426, 5, x_240);
lean_ctor_set_uint8(x_426, 6, x_241);
lean_ctor_set_uint8(x_426, 7, x_242);
lean_ctor_set_uint8(x_426, 8, x_243);
lean_ctor_set_uint8(x_426, 9, x_252);
lean_ctor_set_uint8(x_426, 10, x_245);
lean_ctor_set_uint8(x_426, 11, x_246);
lean_ctor_set_uint8(x_426, 12, x_425);
lean_ctor_set_uint8(x_426, 13, x_425);
lean_ctor_set_uint8(x_426, 14, x_423);
lean_ctor_set_uint8(x_426, 15, x_425);
lean_ctor_set_uint8(x_426, 16, x_425);
x_427 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_426);
x_428 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_227);
lean_ctor_set(x_428, 2, x_228);
lean_ctor_set(x_428, 3, x_229);
lean_ctor_set(x_428, 4, x_230);
lean_ctor_set(x_428, 5, x_231);
lean_ctor_set(x_428, 6, x_232);
lean_ctor_set_uint64(x_428, sizeof(void*)*7, x_427);
lean_ctor_set_uint8(x_428, sizeof(void*)*7 + 8, x_226);
lean_ctor_set_uint8(x_428, sizeof(void*)*7 + 9, x_233);
lean_ctor_set_uint8(x_428, sizeof(void*)*7 + 10, x_234);
x_429 = lean_apply_5(x_1, x_428, x_3, x_4, x_5, x_421);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_429, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 x_432 = x_429;
} else {
 lean_dec_ref(x_429);
 x_432 = lean_box(0);
}
if (lean_is_scalar(x_432)) {
 x_433 = lean_alloc_ctor(0, 2, 0);
} else {
 x_433 = x_432;
}
lean_ctor_set(x_433, 0, x_430);
lean_ctor_set(x_433, 1, x_431);
return x_433;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_434 = lean_ctor_get(x_429, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_429, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 x_436 = x_429;
} else {
 lean_dec_ref(x_429);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 2, 0);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_434);
lean_ctor_set(x_437, 1, x_435);
return x_437;
}
}
else
{
lean_object* x_438; 
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
x_438 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_421);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_441 = x_438;
} else {
 lean_dec_ref(x_438);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(0, 2, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_439);
lean_ctor_set(x_442, 1, x_440);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_443 = lean_ctor_get(x_438, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_438, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_445 = x_438;
} else {
 lean_dec_ref(x_438);
 x_445 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_446 = lean_alloc_ctor(1, 2, 0);
} else {
 x_446 = x_445;
}
lean_ctor_set(x_446, 0, x_443);
lean_ctor_set(x_446, 1, x_444);
return x_446;
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_447; uint64_t x_448; uint8_t x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; uint8_t x_456; uint8_t x_457; uint8_t x_458; uint8_t x_459; uint8_t x_460; uint8_t x_461; uint8_t x_462; uint8_t x_463; uint8_t x_464; uint8_t x_465; uint8_t x_466; uint8_t x_467; uint8_t x_468; uint8_t x_469; uint8_t x_470; uint8_t x_471; uint8_t x_472; uint8_t x_473; uint8_t x_474; lean_object* x_475; uint8_t x_476; uint8_t x_477; uint64_t x_478; uint64_t x_479; uint64_t x_480; 
x_447 = lean_ctor_get(x_2, 0);
x_448 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_449 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_450 = lean_ctor_get(x_2, 1);
x_451 = lean_ctor_get(x_2, 2);
x_452 = lean_ctor_get(x_2, 3);
x_453 = lean_ctor_get(x_2, 4);
x_454 = lean_ctor_get(x_2, 5);
x_455 = lean_ctor_get(x_2, 6);
x_456 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_457 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
lean_inc(x_455);
lean_inc(x_454);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_451);
lean_inc(x_450);
lean_inc(x_447);
lean_dec(x_2);
x_458 = lean_ctor_get_uint8(x_447, 0);
x_459 = lean_ctor_get_uint8(x_447, 1);
x_460 = lean_ctor_get_uint8(x_447, 2);
x_461 = lean_ctor_get_uint8(x_447, 3);
x_462 = lean_ctor_get_uint8(x_447, 4);
x_463 = lean_ctor_get_uint8(x_447, 5);
x_464 = lean_ctor_get_uint8(x_447, 6);
x_465 = lean_ctor_get_uint8(x_447, 7);
x_466 = lean_ctor_get_uint8(x_447, 8);
x_467 = lean_ctor_get_uint8(x_447, 9);
x_468 = lean_ctor_get_uint8(x_447, 10);
x_469 = lean_ctor_get_uint8(x_447, 11);
x_470 = lean_ctor_get_uint8(x_447, 12);
x_471 = lean_ctor_get_uint8(x_447, 13);
x_472 = lean_ctor_get_uint8(x_447, 14);
x_473 = lean_ctor_get_uint8(x_447, 15);
x_474 = lean_ctor_get_uint8(x_447, 16);
if (lean_is_exclusive(x_447)) {
 x_475 = x_447;
} else {
 lean_dec_ref(x_447);
 x_475 = lean_box(0);
}
x_476 = 1;
x_477 = l_Lean_Meta_TransparencyMode_lt(x_467, x_476);
x_478 = 2;
x_479 = lean_uint64_shift_right(x_448, x_478);
x_480 = lean_uint64_shift_left(x_479, x_478);
if (x_477 == 0)
{
lean_object* x_481; uint64_t x_482; uint64_t x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; 
if (lean_is_scalar(x_475)) {
 x_481 = lean_alloc_ctor(0, 0, 17);
} else {
 x_481 = x_475;
}
lean_ctor_set_uint8(x_481, 0, x_458);
lean_ctor_set_uint8(x_481, 1, x_459);
lean_ctor_set_uint8(x_481, 2, x_460);
lean_ctor_set_uint8(x_481, 3, x_461);
lean_ctor_set_uint8(x_481, 4, x_462);
lean_ctor_set_uint8(x_481, 5, x_463);
lean_ctor_set_uint8(x_481, 6, x_464);
lean_ctor_set_uint8(x_481, 7, x_465);
lean_ctor_set_uint8(x_481, 8, x_466);
lean_ctor_set_uint8(x_481, 9, x_467);
lean_ctor_set_uint8(x_481, 10, x_468);
lean_ctor_set_uint8(x_481, 11, x_469);
lean_ctor_set_uint8(x_481, 12, x_470);
lean_ctor_set_uint8(x_481, 13, x_471);
lean_ctor_set_uint8(x_481, 14, x_472);
lean_ctor_set_uint8(x_481, 15, x_473);
lean_ctor_set_uint8(x_481, 16, x_474);
x_482 = l_Lean_Meta_TransparencyMode_toUInt64(x_467);
x_483 = lean_uint64_lor(x_480, x_482);
lean_inc(x_455);
lean_inc(x_454);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_451);
lean_inc(x_450);
x_484 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_484, 0, x_481);
lean_ctor_set(x_484, 1, x_450);
lean_ctor_set(x_484, 2, x_451);
lean_ctor_set(x_484, 3, x_452);
lean_ctor_set(x_484, 4, x_453);
lean_ctor_set(x_484, 5, x_454);
lean_ctor_set(x_484, 6, x_455);
lean_ctor_set_uint64(x_484, sizeof(void*)*7, x_483);
lean_ctor_set_uint8(x_484, sizeof(void*)*7 + 8, x_449);
lean_ctor_set_uint8(x_484, sizeof(void*)*7 + 9, x_456);
lean_ctor_set_uint8(x_484, sizeof(void*)*7 + 10, x_457);
x_485 = l_Lean_Meta_getConfig(x_484, x_3, x_4, x_5, x_6);
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get_uint8(x_486, 13);
if (x_487 == 0)
{
lean_object* x_488; uint8_t x_489; uint8_t x_490; lean_object* x_491; uint64_t x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_486);
lean_dec(x_484);
x_488 = lean_ctor_get(x_485, 1);
lean_inc(x_488);
lean_dec(x_485);
x_489 = 1;
x_490 = 2;
x_491 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_491, 0, x_458);
lean_ctor_set_uint8(x_491, 1, x_459);
lean_ctor_set_uint8(x_491, 2, x_460);
lean_ctor_set_uint8(x_491, 3, x_461);
lean_ctor_set_uint8(x_491, 4, x_462);
lean_ctor_set_uint8(x_491, 5, x_463);
lean_ctor_set_uint8(x_491, 6, x_464);
lean_ctor_set_uint8(x_491, 7, x_465);
lean_ctor_set_uint8(x_491, 8, x_466);
lean_ctor_set_uint8(x_491, 9, x_467);
lean_ctor_set_uint8(x_491, 10, x_468);
lean_ctor_set_uint8(x_491, 11, x_469);
lean_ctor_set_uint8(x_491, 12, x_489);
lean_ctor_set_uint8(x_491, 13, x_489);
lean_ctor_set_uint8(x_491, 14, x_490);
lean_ctor_set_uint8(x_491, 15, x_489);
lean_ctor_set_uint8(x_491, 16, x_489);
x_492 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_491);
x_493 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_450);
lean_ctor_set(x_493, 2, x_451);
lean_ctor_set(x_493, 3, x_452);
lean_ctor_set(x_493, 4, x_453);
lean_ctor_set(x_493, 5, x_454);
lean_ctor_set(x_493, 6, x_455);
lean_ctor_set_uint64(x_493, sizeof(void*)*7, x_492);
lean_ctor_set_uint8(x_493, sizeof(void*)*7 + 8, x_449);
lean_ctor_set_uint8(x_493, sizeof(void*)*7 + 9, x_456);
lean_ctor_set_uint8(x_493, sizeof(void*)*7 + 10, x_457);
x_494 = lean_apply_5(x_1, x_493, x_3, x_4, x_5, x_488);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_497 = x_494;
} else {
 lean_dec_ref(x_494);
 x_497 = lean_box(0);
}
if (lean_is_scalar(x_497)) {
 x_498 = lean_alloc_ctor(0, 2, 0);
} else {
 x_498 = x_497;
}
lean_ctor_set(x_498, 0, x_495);
lean_ctor_set(x_498, 1, x_496);
return x_498;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_499 = lean_ctor_get(x_494, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_494, 1);
lean_inc(x_500);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_501 = x_494;
} else {
 lean_dec_ref(x_494);
 x_501 = lean_box(0);
}
if (lean_is_scalar(x_501)) {
 x_502 = lean_alloc_ctor(1, 2, 0);
} else {
 x_502 = x_501;
}
lean_ctor_set(x_502, 0, x_499);
lean_ctor_set(x_502, 1, x_500);
return x_502;
}
}
else
{
uint8_t x_503; 
x_503 = lean_ctor_get_uint8(x_486, 12);
if (x_503 == 0)
{
lean_object* x_504; uint8_t x_505; uint8_t x_506; lean_object* x_507; uint64_t x_508; lean_object* x_509; lean_object* x_510; 
lean_dec(x_486);
lean_dec(x_484);
x_504 = lean_ctor_get(x_485, 1);
lean_inc(x_504);
lean_dec(x_485);
x_505 = 1;
x_506 = 2;
x_507 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_507, 0, x_458);
lean_ctor_set_uint8(x_507, 1, x_459);
lean_ctor_set_uint8(x_507, 2, x_460);
lean_ctor_set_uint8(x_507, 3, x_461);
lean_ctor_set_uint8(x_507, 4, x_462);
lean_ctor_set_uint8(x_507, 5, x_463);
lean_ctor_set_uint8(x_507, 6, x_464);
lean_ctor_set_uint8(x_507, 7, x_465);
lean_ctor_set_uint8(x_507, 8, x_466);
lean_ctor_set_uint8(x_507, 9, x_467);
lean_ctor_set_uint8(x_507, 10, x_468);
lean_ctor_set_uint8(x_507, 11, x_469);
lean_ctor_set_uint8(x_507, 12, x_505);
lean_ctor_set_uint8(x_507, 13, x_505);
lean_ctor_set_uint8(x_507, 14, x_506);
lean_ctor_set_uint8(x_507, 15, x_505);
lean_ctor_set_uint8(x_507, 16, x_505);
x_508 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_507);
x_509 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_509, 0, x_507);
lean_ctor_set(x_509, 1, x_450);
lean_ctor_set(x_509, 2, x_451);
lean_ctor_set(x_509, 3, x_452);
lean_ctor_set(x_509, 4, x_453);
lean_ctor_set(x_509, 5, x_454);
lean_ctor_set(x_509, 6, x_455);
lean_ctor_set_uint64(x_509, sizeof(void*)*7, x_508);
lean_ctor_set_uint8(x_509, sizeof(void*)*7 + 8, x_449);
lean_ctor_set_uint8(x_509, sizeof(void*)*7 + 9, x_456);
lean_ctor_set_uint8(x_509, sizeof(void*)*7 + 10, x_457);
x_510 = lean_apply_5(x_1, x_509, x_3, x_4, x_5, x_504);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
if (lean_is_exclusive(x_510)) {
 lean_ctor_release(x_510, 0);
 lean_ctor_release(x_510, 1);
 x_513 = x_510;
} else {
 lean_dec_ref(x_510);
 x_513 = lean_box(0);
}
if (lean_is_scalar(x_513)) {
 x_514 = lean_alloc_ctor(0, 2, 0);
} else {
 x_514 = x_513;
}
lean_ctor_set(x_514, 0, x_511);
lean_ctor_set(x_514, 1, x_512);
return x_514;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_515 = lean_ctor_get(x_510, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_510, 1);
lean_inc(x_516);
if (lean_is_exclusive(x_510)) {
 lean_ctor_release(x_510, 0);
 lean_ctor_release(x_510, 1);
 x_517 = x_510;
} else {
 lean_dec_ref(x_510);
 x_517 = lean_box(0);
}
if (lean_is_scalar(x_517)) {
 x_518 = lean_alloc_ctor(1, 2, 0);
} else {
 x_518 = x_517;
}
lean_ctor_set(x_518, 0, x_515);
lean_ctor_set(x_518, 1, x_516);
return x_518;
}
}
else
{
uint8_t x_519; 
x_519 = lean_ctor_get_uint8(x_486, 15);
if (x_519 == 0)
{
lean_object* x_520; uint8_t x_521; uint8_t x_522; lean_object* x_523; uint64_t x_524; lean_object* x_525; lean_object* x_526; 
lean_dec(x_486);
lean_dec(x_484);
x_520 = lean_ctor_get(x_485, 1);
lean_inc(x_520);
lean_dec(x_485);
x_521 = 1;
x_522 = 2;
x_523 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_523, 0, x_458);
lean_ctor_set_uint8(x_523, 1, x_459);
lean_ctor_set_uint8(x_523, 2, x_460);
lean_ctor_set_uint8(x_523, 3, x_461);
lean_ctor_set_uint8(x_523, 4, x_462);
lean_ctor_set_uint8(x_523, 5, x_463);
lean_ctor_set_uint8(x_523, 6, x_464);
lean_ctor_set_uint8(x_523, 7, x_465);
lean_ctor_set_uint8(x_523, 8, x_466);
lean_ctor_set_uint8(x_523, 9, x_467);
lean_ctor_set_uint8(x_523, 10, x_468);
lean_ctor_set_uint8(x_523, 11, x_469);
lean_ctor_set_uint8(x_523, 12, x_521);
lean_ctor_set_uint8(x_523, 13, x_521);
lean_ctor_set_uint8(x_523, 14, x_522);
lean_ctor_set_uint8(x_523, 15, x_521);
lean_ctor_set_uint8(x_523, 16, x_521);
x_524 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_523);
x_525 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_525, 0, x_523);
lean_ctor_set(x_525, 1, x_450);
lean_ctor_set(x_525, 2, x_451);
lean_ctor_set(x_525, 3, x_452);
lean_ctor_set(x_525, 4, x_453);
lean_ctor_set(x_525, 5, x_454);
lean_ctor_set(x_525, 6, x_455);
lean_ctor_set_uint64(x_525, sizeof(void*)*7, x_524);
lean_ctor_set_uint8(x_525, sizeof(void*)*7 + 8, x_449);
lean_ctor_set_uint8(x_525, sizeof(void*)*7 + 9, x_456);
lean_ctor_set_uint8(x_525, sizeof(void*)*7 + 10, x_457);
x_526 = lean_apply_5(x_1, x_525, x_3, x_4, x_5, x_520);
if (lean_obj_tag(x_526) == 0)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_526, 1);
lean_inc(x_528);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 x_529 = x_526;
} else {
 lean_dec_ref(x_526);
 x_529 = lean_box(0);
}
if (lean_is_scalar(x_529)) {
 x_530 = lean_alloc_ctor(0, 2, 0);
} else {
 x_530 = x_529;
}
lean_ctor_set(x_530, 0, x_527);
lean_ctor_set(x_530, 1, x_528);
return x_530;
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_531 = lean_ctor_get(x_526, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_526, 1);
lean_inc(x_532);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 x_533 = x_526;
} else {
 lean_dec_ref(x_526);
 x_533 = lean_box(0);
}
if (lean_is_scalar(x_533)) {
 x_534 = lean_alloc_ctor(1, 2, 0);
} else {
 x_534 = x_533;
}
lean_ctor_set(x_534, 0, x_531);
lean_ctor_set(x_534, 1, x_532);
return x_534;
}
}
else
{
uint8_t x_535; 
x_535 = lean_ctor_get_uint8(x_486, 16);
if (x_535 == 0)
{
lean_object* x_536; uint8_t x_537; uint8_t x_538; lean_object* x_539; uint64_t x_540; lean_object* x_541; lean_object* x_542; 
lean_dec(x_486);
lean_dec(x_484);
x_536 = lean_ctor_get(x_485, 1);
lean_inc(x_536);
lean_dec(x_485);
x_537 = 1;
x_538 = 2;
x_539 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_539, 0, x_458);
lean_ctor_set_uint8(x_539, 1, x_459);
lean_ctor_set_uint8(x_539, 2, x_460);
lean_ctor_set_uint8(x_539, 3, x_461);
lean_ctor_set_uint8(x_539, 4, x_462);
lean_ctor_set_uint8(x_539, 5, x_463);
lean_ctor_set_uint8(x_539, 6, x_464);
lean_ctor_set_uint8(x_539, 7, x_465);
lean_ctor_set_uint8(x_539, 8, x_466);
lean_ctor_set_uint8(x_539, 9, x_467);
lean_ctor_set_uint8(x_539, 10, x_468);
lean_ctor_set_uint8(x_539, 11, x_469);
lean_ctor_set_uint8(x_539, 12, x_537);
lean_ctor_set_uint8(x_539, 13, x_537);
lean_ctor_set_uint8(x_539, 14, x_538);
lean_ctor_set_uint8(x_539, 15, x_537);
lean_ctor_set_uint8(x_539, 16, x_537);
x_540 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_539);
x_541 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_541, 0, x_539);
lean_ctor_set(x_541, 1, x_450);
lean_ctor_set(x_541, 2, x_451);
lean_ctor_set(x_541, 3, x_452);
lean_ctor_set(x_541, 4, x_453);
lean_ctor_set(x_541, 5, x_454);
lean_ctor_set(x_541, 6, x_455);
lean_ctor_set_uint64(x_541, sizeof(void*)*7, x_540);
lean_ctor_set_uint8(x_541, sizeof(void*)*7 + 8, x_449);
lean_ctor_set_uint8(x_541, sizeof(void*)*7 + 9, x_456);
lean_ctor_set_uint8(x_541, sizeof(void*)*7 + 10, x_457);
x_542 = lean_apply_5(x_1, x_541, x_3, x_4, x_5, x_536);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_542, 1);
lean_inc(x_544);
if (lean_is_exclusive(x_542)) {
 lean_ctor_release(x_542, 0);
 lean_ctor_release(x_542, 1);
 x_545 = x_542;
} else {
 lean_dec_ref(x_542);
 x_545 = lean_box(0);
}
if (lean_is_scalar(x_545)) {
 x_546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_546 = x_545;
}
lean_ctor_set(x_546, 0, x_543);
lean_ctor_set(x_546, 1, x_544);
return x_546;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_547 = lean_ctor_get(x_542, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_542, 1);
lean_inc(x_548);
if (lean_is_exclusive(x_542)) {
 lean_ctor_release(x_542, 0);
 lean_ctor_release(x_542, 1);
 x_549 = x_542;
} else {
 lean_dec_ref(x_542);
 x_549 = lean_box(0);
}
if (lean_is_scalar(x_549)) {
 x_550 = lean_alloc_ctor(1, 2, 0);
} else {
 x_550 = x_549;
}
lean_ctor_set(x_550, 0, x_547);
lean_ctor_set(x_550, 1, x_548);
return x_550;
}
}
else
{
lean_object* x_551; uint8_t x_552; uint8_t x_553; uint8_t x_554; 
x_551 = lean_ctor_get(x_485, 1);
lean_inc(x_551);
lean_dec(x_485);
x_552 = lean_ctor_get_uint8(x_486, 14);
lean_dec(x_486);
x_553 = 2;
x_554 = l_Lean_Meta_instDecidableEqProjReductionKind(x_552, x_553);
if (x_554 == 0)
{
uint8_t x_555; lean_object* x_556; uint64_t x_557; lean_object* x_558; lean_object* x_559; 
lean_dec(x_484);
x_555 = 1;
x_556 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_556, 0, x_458);
lean_ctor_set_uint8(x_556, 1, x_459);
lean_ctor_set_uint8(x_556, 2, x_460);
lean_ctor_set_uint8(x_556, 3, x_461);
lean_ctor_set_uint8(x_556, 4, x_462);
lean_ctor_set_uint8(x_556, 5, x_463);
lean_ctor_set_uint8(x_556, 6, x_464);
lean_ctor_set_uint8(x_556, 7, x_465);
lean_ctor_set_uint8(x_556, 8, x_466);
lean_ctor_set_uint8(x_556, 9, x_467);
lean_ctor_set_uint8(x_556, 10, x_468);
lean_ctor_set_uint8(x_556, 11, x_469);
lean_ctor_set_uint8(x_556, 12, x_555);
lean_ctor_set_uint8(x_556, 13, x_555);
lean_ctor_set_uint8(x_556, 14, x_553);
lean_ctor_set_uint8(x_556, 15, x_555);
lean_ctor_set_uint8(x_556, 16, x_555);
x_557 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_556);
x_558 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_558, 0, x_556);
lean_ctor_set(x_558, 1, x_450);
lean_ctor_set(x_558, 2, x_451);
lean_ctor_set(x_558, 3, x_452);
lean_ctor_set(x_558, 4, x_453);
lean_ctor_set(x_558, 5, x_454);
lean_ctor_set(x_558, 6, x_455);
lean_ctor_set_uint64(x_558, sizeof(void*)*7, x_557);
lean_ctor_set_uint8(x_558, sizeof(void*)*7 + 8, x_449);
lean_ctor_set_uint8(x_558, sizeof(void*)*7 + 9, x_456);
lean_ctor_set_uint8(x_558, sizeof(void*)*7 + 10, x_457);
x_559 = lean_apply_5(x_1, x_558, x_3, x_4, x_5, x_551);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 lean_ctor_release(x_559, 1);
 x_562 = x_559;
} else {
 lean_dec_ref(x_559);
 x_562 = lean_box(0);
}
if (lean_is_scalar(x_562)) {
 x_563 = lean_alloc_ctor(0, 2, 0);
} else {
 x_563 = x_562;
}
lean_ctor_set(x_563, 0, x_560);
lean_ctor_set(x_563, 1, x_561);
return x_563;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_564 = lean_ctor_get(x_559, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_559, 1);
lean_inc(x_565);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 lean_ctor_release(x_559, 1);
 x_566 = x_559;
} else {
 lean_dec_ref(x_559);
 x_566 = lean_box(0);
}
if (lean_is_scalar(x_566)) {
 x_567 = lean_alloc_ctor(1, 2, 0);
} else {
 x_567 = x_566;
}
lean_ctor_set(x_567, 0, x_564);
lean_ctor_set(x_567, 1, x_565);
return x_567;
}
}
else
{
lean_object* x_568; 
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_450);
x_568 = lean_apply_5(x_1, x_484, x_3, x_4, x_5, x_551);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_568, 1);
lean_inc(x_570);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 lean_ctor_release(x_568, 1);
 x_571 = x_568;
} else {
 lean_dec_ref(x_568);
 x_571 = lean_box(0);
}
if (lean_is_scalar(x_571)) {
 x_572 = lean_alloc_ctor(0, 2, 0);
} else {
 x_572 = x_571;
}
lean_ctor_set(x_572, 0, x_569);
lean_ctor_set(x_572, 1, x_570);
return x_572;
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_573 = lean_ctor_get(x_568, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_568, 1);
lean_inc(x_574);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 lean_ctor_release(x_568, 1);
 x_575 = x_568;
} else {
 lean_dec_ref(x_568);
 x_575 = lean_box(0);
}
if (lean_is_scalar(x_575)) {
 x_576 = lean_alloc_ctor(1, 2, 0);
} else {
 x_576 = x_575;
}
lean_ctor_set(x_576, 0, x_573);
lean_ctor_set(x_576, 1, x_574);
return x_576;
}
}
}
}
}
}
}
else
{
lean_object* x_577; uint64_t x_578; uint64_t x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; uint8_t x_583; 
if (lean_is_scalar(x_475)) {
 x_577 = lean_alloc_ctor(0, 0, 17);
} else {
 x_577 = x_475;
}
lean_ctor_set_uint8(x_577, 0, x_458);
lean_ctor_set_uint8(x_577, 1, x_459);
lean_ctor_set_uint8(x_577, 2, x_460);
lean_ctor_set_uint8(x_577, 3, x_461);
lean_ctor_set_uint8(x_577, 4, x_462);
lean_ctor_set_uint8(x_577, 5, x_463);
lean_ctor_set_uint8(x_577, 6, x_464);
lean_ctor_set_uint8(x_577, 7, x_465);
lean_ctor_set_uint8(x_577, 8, x_466);
lean_ctor_set_uint8(x_577, 9, x_476);
lean_ctor_set_uint8(x_577, 10, x_468);
lean_ctor_set_uint8(x_577, 11, x_469);
lean_ctor_set_uint8(x_577, 12, x_470);
lean_ctor_set_uint8(x_577, 13, x_471);
lean_ctor_set_uint8(x_577, 14, x_472);
lean_ctor_set_uint8(x_577, 15, x_473);
lean_ctor_set_uint8(x_577, 16, x_474);
x_578 = l_Lean_Meta_withInferTypeConfig___rarg___closed__1;
x_579 = lean_uint64_lor(x_480, x_578);
lean_inc(x_455);
lean_inc(x_454);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_451);
lean_inc(x_450);
x_580 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_580, 0, x_577);
lean_ctor_set(x_580, 1, x_450);
lean_ctor_set(x_580, 2, x_451);
lean_ctor_set(x_580, 3, x_452);
lean_ctor_set(x_580, 4, x_453);
lean_ctor_set(x_580, 5, x_454);
lean_ctor_set(x_580, 6, x_455);
lean_ctor_set_uint64(x_580, sizeof(void*)*7, x_579);
lean_ctor_set_uint8(x_580, sizeof(void*)*7 + 8, x_449);
lean_ctor_set_uint8(x_580, sizeof(void*)*7 + 9, x_456);
lean_ctor_set_uint8(x_580, sizeof(void*)*7 + 10, x_457);
x_581 = l_Lean_Meta_getConfig(x_580, x_3, x_4, x_5, x_6);
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
x_583 = lean_ctor_get_uint8(x_582, 13);
if (x_583 == 0)
{
lean_object* x_584; uint8_t x_585; uint8_t x_586; lean_object* x_587; uint64_t x_588; lean_object* x_589; lean_object* x_590; 
lean_dec(x_582);
lean_dec(x_580);
x_584 = lean_ctor_get(x_581, 1);
lean_inc(x_584);
lean_dec(x_581);
x_585 = 1;
x_586 = 2;
x_587 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_587, 0, x_458);
lean_ctor_set_uint8(x_587, 1, x_459);
lean_ctor_set_uint8(x_587, 2, x_460);
lean_ctor_set_uint8(x_587, 3, x_461);
lean_ctor_set_uint8(x_587, 4, x_462);
lean_ctor_set_uint8(x_587, 5, x_463);
lean_ctor_set_uint8(x_587, 6, x_464);
lean_ctor_set_uint8(x_587, 7, x_465);
lean_ctor_set_uint8(x_587, 8, x_466);
lean_ctor_set_uint8(x_587, 9, x_476);
lean_ctor_set_uint8(x_587, 10, x_468);
lean_ctor_set_uint8(x_587, 11, x_469);
lean_ctor_set_uint8(x_587, 12, x_585);
lean_ctor_set_uint8(x_587, 13, x_585);
lean_ctor_set_uint8(x_587, 14, x_586);
lean_ctor_set_uint8(x_587, 15, x_585);
lean_ctor_set_uint8(x_587, 16, x_585);
x_588 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_587);
x_589 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_589, 0, x_587);
lean_ctor_set(x_589, 1, x_450);
lean_ctor_set(x_589, 2, x_451);
lean_ctor_set(x_589, 3, x_452);
lean_ctor_set(x_589, 4, x_453);
lean_ctor_set(x_589, 5, x_454);
lean_ctor_set(x_589, 6, x_455);
lean_ctor_set_uint64(x_589, sizeof(void*)*7, x_588);
lean_ctor_set_uint8(x_589, sizeof(void*)*7 + 8, x_449);
lean_ctor_set_uint8(x_589, sizeof(void*)*7 + 9, x_456);
lean_ctor_set_uint8(x_589, sizeof(void*)*7 + 10, x_457);
x_590 = lean_apply_5(x_1, x_589, x_3, x_4, x_5, x_584);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_590, 1);
lean_inc(x_592);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 lean_ctor_release(x_590, 1);
 x_593 = x_590;
} else {
 lean_dec_ref(x_590);
 x_593 = lean_box(0);
}
if (lean_is_scalar(x_593)) {
 x_594 = lean_alloc_ctor(0, 2, 0);
} else {
 x_594 = x_593;
}
lean_ctor_set(x_594, 0, x_591);
lean_ctor_set(x_594, 1, x_592);
return x_594;
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_595 = lean_ctor_get(x_590, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_590, 1);
lean_inc(x_596);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 lean_ctor_release(x_590, 1);
 x_597 = x_590;
} else {
 lean_dec_ref(x_590);
 x_597 = lean_box(0);
}
if (lean_is_scalar(x_597)) {
 x_598 = lean_alloc_ctor(1, 2, 0);
} else {
 x_598 = x_597;
}
lean_ctor_set(x_598, 0, x_595);
lean_ctor_set(x_598, 1, x_596);
return x_598;
}
}
else
{
uint8_t x_599; 
x_599 = lean_ctor_get_uint8(x_582, 12);
if (x_599 == 0)
{
lean_object* x_600; uint8_t x_601; uint8_t x_602; lean_object* x_603; uint64_t x_604; lean_object* x_605; lean_object* x_606; 
lean_dec(x_582);
lean_dec(x_580);
x_600 = lean_ctor_get(x_581, 1);
lean_inc(x_600);
lean_dec(x_581);
x_601 = 1;
x_602 = 2;
x_603 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_603, 0, x_458);
lean_ctor_set_uint8(x_603, 1, x_459);
lean_ctor_set_uint8(x_603, 2, x_460);
lean_ctor_set_uint8(x_603, 3, x_461);
lean_ctor_set_uint8(x_603, 4, x_462);
lean_ctor_set_uint8(x_603, 5, x_463);
lean_ctor_set_uint8(x_603, 6, x_464);
lean_ctor_set_uint8(x_603, 7, x_465);
lean_ctor_set_uint8(x_603, 8, x_466);
lean_ctor_set_uint8(x_603, 9, x_476);
lean_ctor_set_uint8(x_603, 10, x_468);
lean_ctor_set_uint8(x_603, 11, x_469);
lean_ctor_set_uint8(x_603, 12, x_601);
lean_ctor_set_uint8(x_603, 13, x_601);
lean_ctor_set_uint8(x_603, 14, x_602);
lean_ctor_set_uint8(x_603, 15, x_601);
lean_ctor_set_uint8(x_603, 16, x_601);
x_604 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_603);
x_605 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_605, 0, x_603);
lean_ctor_set(x_605, 1, x_450);
lean_ctor_set(x_605, 2, x_451);
lean_ctor_set(x_605, 3, x_452);
lean_ctor_set(x_605, 4, x_453);
lean_ctor_set(x_605, 5, x_454);
lean_ctor_set(x_605, 6, x_455);
lean_ctor_set_uint64(x_605, sizeof(void*)*7, x_604);
lean_ctor_set_uint8(x_605, sizeof(void*)*7 + 8, x_449);
lean_ctor_set_uint8(x_605, sizeof(void*)*7 + 9, x_456);
lean_ctor_set_uint8(x_605, sizeof(void*)*7 + 10, x_457);
x_606 = lean_apply_5(x_1, x_605, x_3, x_4, x_5, x_600);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_607 = lean_ctor_get(x_606, 0);
lean_inc(x_607);
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_609 = x_606;
} else {
 lean_dec_ref(x_606);
 x_609 = lean_box(0);
}
if (lean_is_scalar(x_609)) {
 x_610 = lean_alloc_ctor(0, 2, 0);
} else {
 x_610 = x_609;
}
lean_ctor_set(x_610, 0, x_607);
lean_ctor_set(x_610, 1, x_608);
return x_610;
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_611 = lean_ctor_get(x_606, 0);
lean_inc(x_611);
x_612 = lean_ctor_get(x_606, 1);
lean_inc(x_612);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_613 = x_606;
} else {
 lean_dec_ref(x_606);
 x_613 = lean_box(0);
}
if (lean_is_scalar(x_613)) {
 x_614 = lean_alloc_ctor(1, 2, 0);
} else {
 x_614 = x_613;
}
lean_ctor_set(x_614, 0, x_611);
lean_ctor_set(x_614, 1, x_612);
return x_614;
}
}
else
{
uint8_t x_615; 
x_615 = lean_ctor_get_uint8(x_582, 15);
if (x_615 == 0)
{
lean_object* x_616; uint8_t x_617; uint8_t x_618; lean_object* x_619; uint64_t x_620; lean_object* x_621; lean_object* x_622; 
lean_dec(x_582);
lean_dec(x_580);
x_616 = lean_ctor_get(x_581, 1);
lean_inc(x_616);
lean_dec(x_581);
x_617 = 1;
x_618 = 2;
x_619 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_619, 0, x_458);
lean_ctor_set_uint8(x_619, 1, x_459);
lean_ctor_set_uint8(x_619, 2, x_460);
lean_ctor_set_uint8(x_619, 3, x_461);
lean_ctor_set_uint8(x_619, 4, x_462);
lean_ctor_set_uint8(x_619, 5, x_463);
lean_ctor_set_uint8(x_619, 6, x_464);
lean_ctor_set_uint8(x_619, 7, x_465);
lean_ctor_set_uint8(x_619, 8, x_466);
lean_ctor_set_uint8(x_619, 9, x_476);
lean_ctor_set_uint8(x_619, 10, x_468);
lean_ctor_set_uint8(x_619, 11, x_469);
lean_ctor_set_uint8(x_619, 12, x_617);
lean_ctor_set_uint8(x_619, 13, x_617);
lean_ctor_set_uint8(x_619, 14, x_618);
lean_ctor_set_uint8(x_619, 15, x_617);
lean_ctor_set_uint8(x_619, 16, x_617);
x_620 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_619);
x_621 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_621, 0, x_619);
lean_ctor_set(x_621, 1, x_450);
lean_ctor_set(x_621, 2, x_451);
lean_ctor_set(x_621, 3, x_452);
lean_ctor_set(x_621, 4, x_453);
lean_ctor_set(x_621, 5, x_454);
lean_ctor_set(x_621, 6, x_455);
lean_ctor_set_uint64(x_621, sizeof(void*)*7, x_620);
lean_ctor_set_uint8(x_621, sizeof(void*)*7 + 8, x_449);
lean_ctor_set_uint8(x_621, sizeof(void*)*7 + 9, x_456);
lean_ctor_set_uint8(x_621, sizeof(void*)*7 + 10, x_457);
x_622 = lean_apply_5(x_1, x_621, x_3, x_4, x_5, x_616);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_623 = lean_ctor_get(x_622, 0);
lean_inc(x_623);
x_624 = lean_ctor_get(x_622, 1);
lean_inc(x_624);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 x_625 = x_622;
} else {
 lean_dec_ref(x_622);
 x_625 = lean_box(0);
}
if (lean_is_scalar(x_625)) {
 x_626 = lean_alloc_ctor(0, 2, 0);
} else {
 x_626 = x_625;
}
lean_ctor_set(x_626, 0, x_623);
lean_ctor_set(x_626, 1, x_624);
return x_626;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_627 = lean_ctor_get(x_622, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_622, 1);
lean_inc(x_628);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 x_629 = x_622;
} else {
 lean_dec_ref(x_622);
 x_629 = lean_box(0);
}
if (lean_is_scalar(x_629)) {
 x_630 = lean_alloc_ctor(1, 2, 0);
} else {
 x_630 = x_629;
}
lean_ctor_set(x_630, 0, x_627);
lean_ctor_set(x_630, 1, x_628);
return x_630;
}
}
else
{
uint8_t x_631; 
x_631 = lean_ctor_get_uint8(x_582, 16);
if (x_631 == 0)
{
lean_object* x_632; uint8_t x_633; uint8_t x_634; lean_object* x_635; uint64_t x_636; lean_object* x_637; lean_object* x_638; 
lean_dec(x_582);
lean_dec(x_580);
x_632 = lean_ctor_get(x_581, 1);
lean_inc(x_632);
lean_dec(x_581);
x_633 = 1;
x_634 = 2;
x_635 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_635, 0, x_458);
lean_ctor_set_uint8(x_635, 1, x_459);
lean_ctor_set_uint8(x_635, 2, x_460);
lean_ctor_set_uint8(x_635, 3, x_461);
lean_ctor_set_uint8(x_635, 4, x_462);
lean_ctor_set_uint8(x_635, 5, x_463);
lean_ctor_set_uint8(x_635, 6, x_464);
lean_ctor_set_uint8(x_635, 7, x_465);
lean_ctor_set_uint8(x_635, 8, x_466);
lean_ctor_set_uint8(x_635, 9, x_476);
lean_ctor_set_uint8(x_635, 10, x_468);
lean_ctor_set_uint8(x_635, 11, x_469);
lean_ctor_set_uint8(x_635, 12, x_633);
lean_ctor_set_uint8(x_635, 13, x_633);
lean_ctor_set_uint8(x_635, 14, x_634);
lean_ctor_set_uint8(x_635, 15, x_633);
lean_ctor_set_uint8(x_635, 16, x_633);
x_636 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_635);
x_637 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_637, 0, x_635);
lean_ctor_set(x_637, 1, x_450);
lean_ctor_set(x_637, 2, x_451);
lean_ctor_set(x_637, 3, x_452);
lean_ctor_set(x_637, 4, x_453);
lean_ctor_set(x_637, 5, x_454);
lean_ctor_set(x_637, 6, x_455);
lean_ctor_set_uint64(x_637, sizeof(void*)*7, x_636);
lean_ctor_set_uint8(x_637, sizeof(void*)*7 + 8, x_449);
lean_ctor_set_uint8(x_637, sizeof(void*)*7 + 9, x_456);
lean_ctor_set_uint8(x_637, sizeof(void*)*7 + 10, x_457);
x_638 = lean_apply_5(x_1, x_637, x_3, x_4, x_5, x_632);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_638, 1);
lean_inc(x_640);
if (lean_is_exclusive(x_638)) {
 lean_ctor_release(x_638, 0);
 lean_ctor_release(x_638, 1);
 x_641 = x_638;
} else {
 lean_dec_ref(x_638);
 x_641 = lean_box(0);
}
if (lean_is_scalar(x_641)) {
 x_642 = lean_alloc_ctor(0, 2, 0);
} else {
 x_642 = x_641;
}
lean_ctor_set(x_642, 0, x_639);
lean_ctor_set(x_642, 1, x_640);
return x_642;
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_643 = lean_ctor_get(x_638, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_638, 1);
lean_inc(x_644);
if (lean_is_exclusive(x_638)) {
 lean_ctor_release(x_638, 0);
 lean_ctor_release(x_638, 1);
 x_645 = x_638;
} else {
 lean_dec_ref(x_638);
 x_645 = lean_box(0);
}
if (lean_is_scalar(x_645)) {
 x_646 = lean_alloc_ctor(1, 2, 0);
} else {
 x_646 = x_645;
}
lean_ctor_set(x_646, 0, x_643);
lean_ctor_set(x_646, 1, x_644);
return x_646;
}
}
else
{
lean_object* x_647; uint8_t x_648; uint8_t x_649; uint8_t x_650; 
x_647 = lean_ctor_get(x_581, 1);
lean_inc(x_647);
lean_dec(x_581);
x_648 = lean_ctor_get_uint8(x_582, 14);
lean_dec(x_582);
x_649 = 2;
x_650 = l_Lean_Meta_instDecidableEqProjReductionKind(x_648, x_649);
if (x_650 == 0)
{
uint8_t x_651; lean_object* x_652; uint64_t x_653; lean_object* x_654; lean_object* x_655; 
lean_dec(x_580);
x_651 = 1;
x_652 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_652, 0, x_458);
lean_ctor_set_uint8(x_652, 1, x_459);
lean_ctor_set_uint8(x_652, 2, x_460);
lean_ctor_set_uint8(x_652, 3, x_461);
lean_ctor_set_uint8(x_652, 4, x_462);
lean_ctor_set_uint8(x_652, 5, x_463);
lean_ctor_set_uint8(x_652, 6, x_464);
lean_ctor_set_uint8(x_652, 7, x_465);
lean_ctor_set_uint8(x_652, 8, x_466);
lean_ctor_set_uint8(x_652, 9, x_476);
lean_ctor_set_uint8(x_652, 10, x_468);
lean_ctor_set_uint8(x_652, 11, x_469);
lean_ctor_set_uint8(x_652, 12, x_651);
lean_ctor_set_uint8(x_652, 13, x_651);
lean_ctor_set_uint8(x_652, 14, x_649);
lean_ctor_set_uint8(x_652, 15, x_651);
lean_ctor_set_uint8(x_652, 16, x_651);
x_653 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_652);
x_654 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_654, 0, x_652);
lean_ctor_set(x_654, 1, x_450);
lean_ctor_set(x_654, 2, x_451);
lean_ctor_set(x_654, 3, x_452);
lean_ctor_set(x_654, 4, x_453);
lean_ctor_set(x_654, 5, x_454);
lean_ctor_set(x_654, 6, x_455);
lean_ctor_set_uint64(x_654, sizeof(void*)*7, x_653);
lean_ctor_set_uint8(x_654, sizeof(void*)*7 + 8, x_449);
lean_ctor_set_uint8(x_654, sizeof(void*)*7 + 9, x_456);
lean_ctor_set_uint8(x_654, sizeof(void*)*7 + 10, x_457);
x_655 = lean_apply_5(x_1, x_654, x_3, x_4, x_5, x_647);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_655, 1);
lean_inc(x_657);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 x_658 = x_655;
} else {
 lean_dec_ref(x_655);
 x_658 = lean_box(0);
}
if (lean_is_scalar(x_658)) {
 x_659 = lean_alloc_ctor(0, 2, 0);
} else {
 x_659 = x_658;
}
lean_ctor_set(x_659, 0, x_656);
lean_ctor_set(x_659, 1, x_657);
return x_659;
}
else
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_660 = lean_ctor_get(x_655, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_655, 1);
lean_inc(x_661);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 x_662 = x_655;
} else {
 lean_dec_ref(x_655);
 x_662 = lean_box(0);
}
if (lean_is_scalar(x_662)) {
 x_663 = lean_alloc_ctor(1, 2, 0);
} else {
 x_663 = x_662;
}
lean_ctor_set(x_663, 0, x_660);
lean_ctor_set(x_663, 1, x_661);
return x_663;
}
}
else
{
lean_object* x_664; 
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_450);
x_664 = lean_apply_5(x_1, x_580, x_3, x_4, x_5, x_647);
if (lean_obj_tag(x_664) == 0)
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_664, 1);
lean_inc(x_666);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 lean_ctor_release(x_664, 1);
 x_667 = x_664;
} else {
 lean_dec_ref(x_664);
 x_667 = lean_box(0);
}
if (lean_is_scalar(x_667)) {
 x_668 = lean_alloc_ctor(0, 2, 0);
} else {
 x_668 = x_667;
}
lean_ctor_set(x_668, 0, x_665);
lean_ctor_set(x_668, 1, x_666);
return x_668;
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_669 = lean_ctor_get(x_664, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_664, 1);
lean_inc(x_670);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 lean_ctor_release(x_664, 1);
 x_671 = x_664;
} else {
 lean_dec_ref(x_664);
 x_671 = lean_box(0);
}
if (lean_is_scalar(x_671)) {
 x_672 = lean_alloc_ctor(1, 2, 0);
} else {
 x_672 = x_671;
}
lean_ctor_set(x_672, 0, x_669);
lean_ctor_set(x_672, 1, x_670);
return x_672;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withInferTypeConfig___rarg), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_inferTypeImp_infer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected bound variable ", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_inferTypeImp_infer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_inferTypeImp_infer___closed__1;
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
x_8 = l_Lean_Expr_bvar___override(x_7);
x_9 = l_Lean_MessageData_ofExpr(x_8);
x_10 = l_Lean_Meta_inferTypeImp_infer___closed__2;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_13, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(x_15, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_24, x_25, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = l_Lean_Expr_hasMVar(x_1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = l_Lean_Meta_mkExprConfigCacheKey(x_1, x_2, x_3, x_4, x_5, x_6);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_st_ref_get(x_3, x_31);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_37, x_30);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_free_object(x_32);
x_39 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_27, x_23, x_2, x_3, x_4, x_5, x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = l_Lean_Expr_hasMVar(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_free_object(x_39);
x_44 = lean_st_ref_take(x_3, x_42);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_45, 1);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_41);
x_52 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_51, x_30, x_41);
lean_ctor_set(x_46, 0, x_52);
x_53 = lean_st_ref_set(x_3, x_45, x_47);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_41);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_41);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_58 = lean_ctor_get(x_46, 0);
x_59 = lean_ctor_get(x_46, 1);
x_60 = lean_ctor_get(x_46, 2);
x_61 = lean_ctor_get(x_46, 3);
x_62 = lean_ctor_get(x_46, 4);
x_63 = lean_ctor_get(x_46, 5);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_46);
lean_inc(x_41);
x_64 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_58, x_30, x_41);
x_65 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_59);
lean_ctor_set(x_65, 2, x_60);
lean_ctor_set(x_65, 3, x_61);
lean_ctor_set(x_65, 4, x_62);
lean_ctor_set(x_65, 5, x_63);
lean_ctor_set(x_45, 1, x_65);
x_66 = lean_st_ref_set(x_3, x_45, x_47);
lean_dec(x_3);
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
lean_ctor_set(x_69, 0, x_41);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_70 = lean_ctor_get(x_45, 0);
x_71 = lean_ctor_get(x_45, 2);
x_72 = lean_ctor_get(x_45, 3);
x_73 = lean_ctor_get(x_45, 4);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_45);
x_74 = lean_ctor_get(x_46, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_46, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_46, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_46, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_46, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_46, 5);
lean_inc(x_79);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 lean_ctor_release(x_46, 4);
 lean_ctor_release(x_46, 5);
 x_80 = x_46;
} else {
 lean_dec_ref(x_46);
 x_80 = lean_box(0);
}
lean_inc(x_41);
x_81 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_74, x_30, x_41);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 6, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_75);
lean_ctor_set(x_82, 2, x_76);
lean_ctor_set(x_82, 3, x_77);
lean_ctor_set(x_82, 4, x_78);
lean_ctor_set(x_82, 5, x_79);
x_83 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_83, 0, x_70);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_71);
lean_ctor_set(x_83, 3, x_72);
lean_ctor_set(x_83, 4, x_73);
x_84 = lean_st_ref_set(x_3, x_83, x_47);
lean_dec(x_3);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_41);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_dec(x_30);
lean_dec(x_3);
return x_39;
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_39, 0);
x_89 = lean_ctor_get(x_39, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_39);
x_90 = l_Lean_Expr_hasMVar(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_91 = lean_st_ref_take(x_3, x_89);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_92, 2);
lean_inc(x_96);
x_97 = lean_ctor_get(x_92, 3);
lean_inc(x_97);
x_98 = lean_ctor_get(x_92, 4);
lean_inc(x_98);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 lean_ctor_release(x_92, 2);
 lean_ctor_release(x_92, 3);
 lean_ctor_release(x_92, 4);
 x_99 = x_92;
} else {
 lean_dec_ref(x_92);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_93, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_93, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_93, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_93, 3);
lean_inc(x_103);
x_104 = lean_ctor_get(x_93, 4);
lean_inc(x_104);
x_105 = lean_ctor_get(x_93, 5);
lean_inc(x_105);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 lean_ctor_release(x_93, 2);
 lean_ctor_release(x_93, 3);
 lean_ctor_release(x_93, 4);
 lean_ctor_release(x_93, 5);
 x_106 = x_93;
} else {
 lean_dec_ref(x_93);
 x_106 = lean_box(0);
}
lean_inc(x_88);
x_107 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_100, x_30, x_88);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 6, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_101);
lean_ctor_set(x_108, 2, x_102);
lean_ctor_set(x_108, 3, x_103);
lean_ctor_set(x_108, 4, x_104);
lean_ctor_set(x_108, 5, x_105);
if (lean_is_scalar(x_99)) {
 x_109 = lean_alloc_ctor(0, 5, 0);
} else {
 x_109 = x_99;
}
lean_ctor_set(x_109, 0, x_95);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_109, 2, x_96);
lean_ctor_set(x_109, 3, x_97);
lean_ctor_set(x_109, 4, x_98);
x_110 = lean_st_ref_set(x_3, x_109, x_94);
lean_dec(x_3);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_88);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
else
{
lean_object* x_114; 
lean_dec(x_30);
lean_dec(x_3);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_88);
lean_ctor_set(x_114, 1, x_89);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_30);
lean_dec(x_3);
x_115 = !lean_is_exclusive(x_39);
if (x_115 == 0)
{
return x_39;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_39, 0);
x_117 = lean_ctor_get(x_39, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_39);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_119 = lean_ctor_get(x_38, 0);
lean_inc(x_119);
lean_dec(x_38);
lean_ctor_set(x_32, 0, x_119);
return x_32;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_32, 0);
x_121 = lean_ctor_get(x_32, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_32);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec(x_122);
x_124 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_123, x_30);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
x_125 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_27, x_23, x_2, x_3, x_4, x_5, x_121);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
x_129 = l_Lean_Expr_hasMVar(x_126);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_128);
x_130 = lean_st_ref_take(x_3, x_127);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_131, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_131, 4);
lean_inc(x_137);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 lean_ctor_release(x_131, 4);
 x_138 = x_131;
} else {
 lean_dec_ref(x_131);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_132, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_132, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_132, 2);
lean_inc(x_141);
x_142 = lean_ctor_get(x_132, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_132, 4);
lean_inc(x_143);
x_144 = lean_ctor_get(x_132, 5);
lean_inc(x_144);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 lean_ctor_release(x_132, 2);
 lean_ctor_release(x_132, 3);
 lean_ctor_release(x_132, 4);
 lean_ctor_release(x_132, 5);
 x_145 = x_132;
} else {
 lean_dec_ref(x_132);
 x_145 = lean_box(0);
}
lean_inc(x_126);
x_146 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_139, x_30, x_126);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 6, 0);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_140);
lean_ctor_set(x_147, 2, x_141);
lean_ctor_set(x_147, 3, x_142);
lean_ctor_set(x_147, 4, x_143);
lean_ctor_set(x_147, 5, x_144);
if (lean_is_scalar(x_138)) {
 x_148 = lean_alloc_ctor(0, 5, 0);
} else {
 x_148 = x_138;
}
lean_ctor_set(x_148, 0, x_134);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_148, 2, x_135);
lean_ctor_set(x_148, 3, x_136);
lean_ctor_set(x_148, 4, x_137);
x_149 = lean_st_ref_set(x_3, x_148, x_133);
lean_dec(x_3);
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
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_126);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
else
{
lean_object* x_153; 
lean_dec(x_30);
lean_dec(x_3);
if (lean_is_scalar(x_128)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_128;
}
lean_ctor_set(x_153, 0, x_126);
lean_ctor_set(x_153, 1, x_127);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_30);
lean_dec(x_3);
x_154 = lean_ctor_get(x_125, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_125, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_156 = x_125;
} else {
 lean_dec_ref(x_125);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_158 = lean_ctor_get(x_124, 0);
lean_inc(x_158);
lean_dec(x_124);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_121);
return x_159;
}
}
}
else
{
lean_object* x_160; 
lean_dec(x_1);
x_160 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_27, x_23, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_160;
}
}
}
case 5:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_161 = lean_ctor_get(x_1, 0);
lean_inc(x_161);
x_162 = l_Lean_Expr_getAppFn(x_161);
lean_dec(x_161);
x_163 = lean_unsigned_to_nat(0u);
x_164 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_163);
x_165 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lambda__1___closed__1;
lean_inc(x_164);
x_166 = lean_mk_array(x_164, x_165);
x_167 = lean_unsigned_to_nat(1u);
x_168 = lean_nat_sub(x_164, x_167);
lean_dec(x_164);
lean_inc(x_1);
x_169 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_166, x_168);
x_170 = l_Lean_Expr_hasMVar(x_1);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_171 = l_Lean_Meta_mkExprConfigCacheKey(x_1, x_2, x_3, x_4, x_5, x_6);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_st_ref_get(x_3, x_173);
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = lean_ctor_get(x_174, 0);
x_177 = lean_ctor_get(x_174, 1);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
lean_dec(x_178);
x_180 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_179, x_172);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
lean_free_object(x_174);
lean_inc(x_3);
x_181 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_162, x_169, x_2, x_3, x_4, x_5, x_177);
lean_dec(x_169);
if (lean_obj_tag(x_181) == 0)
{
uint8_t x_182; 
x_182 = !lean_is_exclusive(x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_183 = lean_ctor_get(x_181, 0);
x_184 = lean_ctor_get(x_181, 1);
x_185 = l_Lean_Expr_hasMVar(x_183);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
lean_free_object(x_181);
x_186 = lean_st_ref_take(x_3, x_184);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; uint8_t x_192; 
x_191 = lean_ctor_get(x_187, 1);
lean_dec(x_191);
x_192 = !lean_is_exclusive(x_188);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_193 = lean_ctor_get(x_188, 0);
lean_inc(x_183);
x_194 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_193, x_172, x_183);
lean_ctor_set(x_188, 0, x_194);
x_195 = lean_st_ref_set(x_3, x_187, x_189);
lean_dec(x_3);
x_196 = !lean_is_exclusive(x_195);
if (x_196 == 0)
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_195, 0);
lean_dec(x_197);
lean_ctor_set(x_195, 0, x_183);
return x_195;
}
else
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
lean_dec(x_195);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_183);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_200 = lean_ctor_get(x_188, 0);
x_201 = lean_ctor_get(x_188, 1);
x_202 = lean_ctor_get(x_188, 2);
x_203 = lean_ctor_get(x_188, 3);
x_204 = lean_ctor_get(x_188, 4);
x_205 = lean_ctor_get(x_188, 5);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_188);
lean_inc(x_183);
x_206 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_200, x_172, x_183);
x_207 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_201);
lean_ctor_set(x_207, 2, x_202);
lean_ctor_set(x_207, 3, x_203);
lean_ctor_set(x_207, 4, x_204);
lean_ctor_set(x_207, 5, x_205);
lean_ctor_set(x_187, 1, x_207);
x_208 = lean_st_ref_set(x_3, x_187, x_189);
lean_dec(x_3);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_210 = x_208;
} else {
 lean_dec_ref(x_208);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_183);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_212 = lean_ctor_get(x_187, 0);
x_213 = lean_ctor_get(x_187, 2);
x_214 = lean_ctor_get(x_187, 3);
x_215 = lean_ctor_get(x_187, 4);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_187);
x_216 = lean_ctor_get(x_188, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_188, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_188, 2);
lean_inc(x_218);
x_219 = lean_ctor_get(x_188, 3);
lean_inc(x_219);
x_220 = lean_ctor_get(x_188, 4);
lean_inc(x_220);
x_221 = lean_ctor_get(x_188, 5);
lean_inc(x_221);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 lean_ctor_release(x_188, 4);
 lean_ctor_release(x_188, 5);
 x_222 = x_188;
} else {
 lean_dec_ref(x_188);
 x_222 = lean_box(0);
}
lean_inc(x_183);
x_223 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_216, x_172, x_183);
if (lean_is_scalar(x_222)) {
 x_224 = lean_alloc_ctor(0, 6, 0);
} else {
 x_224 = x_222;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_217);
lean_ctor_set(x_224, 2, x_218);
lean_ctor_set(x_224, 3, x_219);
lean_ctor_set(x_224, 4, x_220);
lean_ctor_set(x_224, 5, x_221);
x_225 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_225, 0, x_212);
lean_ctor_set(x_225, 1, x_224);
lean_ctor_set(x_225, 2, x_213);
lean_ctor_set(x_225, 3, x_214);
lean_ctor_set(x_225, 4, x_215);
x_226 = lean_st_ref_set(x_3, x_225, x_189);
lean_dec(x_3);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_228 = x_226;
} else {
 lean_dec_ref(x_226);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_183);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
else
{
lean_dec(x_172);
lean_dec(x_3);
return x_181;
}
}
else
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_230 = lean_ctor_get(x_181, 0);
x_231 = lean_ctor_get(x_181, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_181);
x_232 = l_Lean_Expr_hasMVar(x_230);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_233 = lean_st_ref_take(x_3, x_231);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_233, 1);
lean_inc(x_236);
lean_dec(x_233);
x_237 = lean_ctor_get(x_234, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_234, 2);
lean_inc(x_238);
x_239 = lean_ctor_get(x_234, 3);
lean_inc(x_239);
x_240 = lean_ctor_get(x_234, 4);
lean_inc(x_240);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 lean_ctor_release(x_234, 4);
 x_241 = x_234;
} else {
 lean_dec_ref(x_234);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_235, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_235, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_235, 2);
lean_inc(x_244);
x_245 = lean_ctor_get(x_235, 3);
lean_inc(x_245);
x_246 = lean_ctor_get(x_235, 4);
lean_inc(x_246);
x_247 = lean_ctor_get(x_235, 5);
lean_inc(x_247);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 lean_ctor_release(x_235, 4);
 lean_ctor_release(x_235, 5);
 x_248 = x_235;
} else {
 lean_dec_ref(x_235);
 x_248 = lean_box(0);
}
lean_inc(x_230);
x_249 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_242, x_172, x_230);
if (lean_is_scalar(x_248)) {
 x_250 = lean_alloc_ctor(0, 6, 0);
} else {
 x_250 = x_248;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_243);
lean_ctor_set(x_250, 2, x_244);
lean_ctor_set(x_250, 3, x_245);
lean_ctor_set(x_250, 4, x_246);
lean_ctor_set(x_250, 5, x_247);
if (lean_is_scalar(x_241)) {
 x_251 = lean_alloc_ctor(0, 5, 0);
} else {
 x_251 = x_241;
}
lean_ctor_set(x_251, 0, x_237);
lean_ctor_set(x_251, 1, x_250);
lean_ctor_set(x_251, 2, x_238);
lean_ctor_set(x_251, 3, x_239);
lean_ctor_set(x_251, 4, x_240);
x_252 = lean_st_ref_set(x_3, x_251, x_236);
lean_dec(x_3);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_254 = x_252;
} else {
 lean_dec_ref(x_252);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_230);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
else
{
lean_object* x_256; 
lean_dec(x_172);
lean_dec(x_3);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_230);
lean_ctor_set(x_256, 1, x_231);
return x_256;
}
}
}
else
{
uint8_t x_257; 
lean_dec(x_172);
lean_dec(x_3);
x_257 = !lean_is_exclusive(x_181);
if (x_257 == 0)
{
return x_181;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_181, 0);
x_259 = lean_ctor_get(x_181, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_181);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
else
{
lean_object* x_261; 
lean_dec(x_172);
lean_dec(x_169);
lean_dec(x_162);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_261 = lean_ctor_get(x_180, 0);
lean_inc(x_261);
lean_dec(x_180);
lean_ctor_set(x_174, 0, x_261);
return x_174;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_262 = lean_ctor_get(x_174, 0);
x_263 = lean_ctor_get(x_174, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_174);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
lean_dec(x_264);
x_266 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_265, x_172);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; 
lean_inc(x_3);
x_267 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_162, x_169, x_2, x_3, x_4, x_5, x_263);
lean_dec(x_169);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_270 = x_267;
} else {
 lean_dec_ref(x_267);
 x_270 = lean_box(0);
}
x_271 = l_Lean_Expr_hasMVar(x_268);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_270);
x_272 = lean_st_ref_take(x_3, x_269);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
x_275 = lean_ctor_get(x_272, 1);
lean_inc(x_275);
lean_dec(x_272);
x_276 = lean_ctor_get(x_273, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_273, 2);
lean_inc(x_277);
x_278 = lean_ctor_get(x_273, 3);
lean_inc(x_278);
x_279 = lean_ctor_get(x_273, 4);
lean_inc(x_279);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 lean_ctor_release(x_273, 2);
 lean_ctor_release(x_273, 3);
 lean_ctor_release(x_273, 4);
 x_280 = x_273;
} else {
 lean_dec_ref(x_273);
 x_280 = lean_box(0);
}
x_281 = lean_ctor_get(x_274, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_274, 1);
lean_inc(x_282);
x_283 = lean_ctor_get(x_274, 2);
lean_inc(x_283);
x_284 = lean_ctor_get(x_274, 3);
lean_inc(x_284);
x_285 = lean_ctor_get(x_274, 4);
lean_inc(x_285);
x_286 = lean_ctor_get(x_274, 5);
lean_inc(x_286);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 lean_ctor_release(x_274, 2);
 lean_ctor_release(x_274, 3);
 lean_ctor_release(x_274, 4);
 lean_ctor_release(x_274, 5);
 x_287 = x_274;
} else {
 lean_dec_ref(x_274);
 x_287 = lean_box(0);
}
lean_inc(x_268);
x_288 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_281, x_172, x_268);
if (lean_is_scalar(x_287)) {
 x_289 = lean_alloc_ctor(0, 6, 0);
} else {
 x_289 = x_287;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_282);
lean_ctor_set(x_289, 2, x_283);
lean_ctor_set(x_289, 3, x_284);
lean_ctor_set(x_289, 4, x_285);
lean_ctor_set(x_289, 5, x_286);
if (lean_is_scalar(x_280)) {
 x_290 = lean_alloc_ctor(0, 5, 0);
} else {
 x_290 = x_280;
}
lean_ctor_set(x_290, 0, x_276);
lean_ctor_set(x_290, 1, x_289);
lean_ctor_set(x_290, 2, x_277);
lean_ctor_set(x_290, 3, x_278);
lean_ctor_set(x_290, 4, x_279);
x_291 = lean_st_ref_set(x_3, x_290, x_275);
lean_dec(x_3);
x_292 = lean_ctor_get(x_291, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_293 = x_291;
} else {
 lean_dec_ref(x_291);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_268);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
else
{
lean_object* x_295; 
lean_dec(x_172);
lean_dec(x_3);
if (lean_is_scalar(x_270)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_270;
}
lean_ctor_set(x_295, 0, x_268);
lean_ctor_set(x_295, 1, x_269);
return x_295;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_172);
lean_dec(x_3);
x_296 = lean_ctor_get(x_267, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_267, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_298 = x_267;
} else {
 lean_dec_ref(x_267);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_297);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; 
lean_dec(x_172);
lean_dec(x_169);
lean_dec(x_162);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_300 = lean_ctor_get(x_266, 0);
lean_inc(x_300);
lean_dec(x_266);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_263);
return x_301;
}
}
}
else
{
lean_object* x_302; 
lean_dec(x_1);
x_302 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_162, x_169, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_169);
return x_302;
}
}
case 7:
{
uint8_t x_303; 
x_303 = l_Lean_Expr_hasMVar(x_1);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
lean_inc(x_1);
x_304 = l_Lean_Meta_mkExprConfigCacheKey(x_1, x_2, x_3, x_4, x_5, x_6);
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_st_ref_get(x_3, x_306);
x_308 = !lean_is_exclusive(x_307);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_309 = lean_ctor_get(x_307, 0);
x_310 = lean_ctor_get(x_307, 1);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
lean_dec(x_311);
x_313 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_312, x_305);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; uint8_t x_315; lean_object* x_316; 
lean_free_object(x_307);
x_314 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1;
x_315 = 0;
lean_inc(x_3);
x_316 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_1, x_314, x_315, x_2, x_3, x_4, x_5, x_310);
if (lean_obj_tag(x_316) == 0)
{
uint8_t x_317; 
x_317 = !lean_is_exclusive(x_316);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; uint8_t x_320; 
x_318 = lean_ctor_get(x_316, 0);
x_319 = lean_ctor_get(x_316, 1);
x_320 = l_Lean_Expr_hasMVar(x_318);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; 
lean_free_object(x_316);
x_321 = lean_st_ref_take(x_3, x_319);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_322, 1);
lean_inc(x_323);
x_324 = lean_ctor_get(x_321, 1);
lean_inc(x_324);
lean_dec(x_321);
x_325 = !lean_is_exclusive(x_322);
if (x_325 == 0)
{
lean_object* x_326; uint8_t x_327; 
x_326 = lean_ctor_get(x_322, 1);
lean_dec(x_326);
x_327 = !lean_is_exclusive(x_323);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_328 = lean_ctor_get(x_323, 0);
lean_inc(x_318);
x_329 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_328, x_305, x_318);
lean_ctor_set(x_323, 0, x_329);
x_330 = lean_st_ref_set(x_3, x_322, x_324);
lean_dec(x_3);
x_331 = !lean_is_exclusive(x_330);
if (x_331 == 0)
{
lean_object* x_332; 
x_332 = lean_ctor_get(x_330, 0);
lean_dec(x_332);
lean_ctor_set(x_330, 0, x_318);
return x_330;
}
else
{
lean_object* x_333; lean_object* x_334; 
x_333 = lean_ctor_get(x_330, 1);
lean_inc(x_333);
lean_dec(x_330);
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_318);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_335 = lean_ctor_get(x_323, 0);
x_336 = lean_ctor_get(x_323, 1);
x_337 = lean_ctor_get(x_323, 2);
x_338 = lean_ctor_get(x_323, 3);
x_339 = lean_ctor_get(x_323, 4);
x_340 = lean_ctor_get(x_323, 5);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_323);
lean_inc(x_318);
x_341 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_335, x_305, x_318);
x_342 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_336);
lean_ctor_set(x_342, 2, x_337);
lean_ctor_set(x_342, 3, x_338);
lean_ctor_set(x_342, 4, x_339);
lean_ctor_set(x_342, 5, x_340);
lean_ctor_set(x_322, 1, x_342);
x_343 = lean_st_ref_set(x_3, x_322, x_324);
lean_dec(x_3);
x_344 = lean_ctor_get(x_343, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_345 = x_343;
} else {
 lean_dec_ref(x_343);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_345)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_345;
}
lean_ctor_set(x_346, 0, x_318);
lean_ctor_set(x_346, 1, x_344);
return x_346;
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_347 = lean_ctor_get(x_322, 0);
x_348 = lean_ctor_get(x_322, 2);
x_349 = lean_ctor_get(x_322, 3);
x_350 = lean_ctor_get(x_322, 4);
lean_inc(x_350);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_322);
x_351 = lean_ctor_get(x_323, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_323, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_323, 2);
lean_inc(x_353);
x_354 = lean_ctor_get(x_323, 3);
lean_inc(x_354);
x_355 = lean_ctor_get(x_323, 4);
lean_inc(x_355);
x_356 = lean_ctor_get(x_323, 5);
lean_inc(x_356);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 lean_ctor_release(x_323, 2);
 lean_ctor_release(x_323, 3);
 lean_ctor_release(x_323, 4);
 lean_ctor_release(x_323, 5);
 x_357 = x_323;
} else {
 lean_dec_ref(x_323);
 x_357 = lean_box(0);
}
lean_inc(x_318);
x_358 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_351, x_305, x_318);
if (lean_is_scalar(x_357)) {
 x_359 = lean_alloc_ctor(0, 6, 0);
} else {
 x_359 = x_357;
}
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_352);
lean_ctor_set(x_359, 2, x_353);
lean_ctor_set(x_359, 3, x_354);
lean_ctor_set(x_359, 4, x_355);
lean_ctor_set(x_359, 5, x_356);
x_360 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_360, 0, x_347);
lean_ctor_set(x_360, 1, x_359);
lean_ctor_set(x_360, 2, x_348);
lean_ctor_set(x_360, 3, x_349);
lean_ctor_set(x_360, 4, x_350);
x_361 = lean_st_ref_set(x_3, x_360, x_324);
lean_dec(x_3);
x_362 = lean_ctor_get(x_361, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_363 = x_361;
} else {
 lean_dec_ref(x_361);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(0, 2, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_318);
lean_ctor_set(x_364, 1, x_362);
return x_364;
}
}
else
{
lean_dec(x_305);
lean_dec(x_3);
return x_316;
}
}
else
{
lean_object* x_365; lean_object* x_366; uint8_t x_367; 
x_365 = lean_ctor_get(x_316, 0);
x_366 = lean_ctor_get(x_316, 1);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_316);
x_367 = l_Lean_Expr_hasMVar(x_365);
if (x_367 == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_368 = lean_st_ref_take(x_3, x_366);
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_369, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_368, 1);
lean_inc(x_371);
lean_dec(x_368);
x_372 = lean_ctor_get(x_369, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_369, 2);
lean_inc(x_373);
x_374 = lean_ctor_get(x_369, 3);
lean_inc(x_374);
x_375 = lean_ctor_get(x_369, 4);
lean_inc(x_375);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 lean_ctor_release(x_369, 2);
 lean_ctor_release(x_369, 3);
 lean_ctor_release(x_369, 4);
 x_376 = x_369;
} else {
 lean_dec_ref(x_369);
 x_376 = lean_box(0);
}
x_377 = lean_ctor_get(x_370, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_370, 1);
lean_inc(x_378);
x_379 = lean_ctor_get(x_370, 2);
lean_inc(x_379);
x_380 = lean_ctor_get(x_370, 3);
lean_inc(x_380);
x_381 = lean_ctor_get(x_370, 4);
lean_inc(x_381);
x_382 = lean_ctor_get(x_370, 5);
lean_inc(x_382);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 lean_ctor_release(x_370, 2);
 lean_ctor_release(x_370, 3);
 lean_ctor_release(x_370, 4);
 lean_ctor_release(x_370, 5);
 x_383 = x_370;
} else {
 lean_dec_ref(x_370);
 x_383 = lean_box(0);
}
lean_inc(x_365);
x_384 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_377, x_305, x_365);
if (lean_is_scalar(x_383)) {
 x_385 = lean_alloc_ctor(0, 6, 0);
} else {
 x_385 = x_383;
}
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_378);
lean_ctor_set(x_385, 2, x_379);
lean_ctor_set(x_385, 3, x_380);
lean_ctor_set(x_385, 4, x_381);
lean_ctor_set(x_385, 5, x_382);
if (lean_is_scalar(x_376)) {
 x_386 = lean_alloc_ctor(0, 5, 0);
} else {
 x_386 = x_376;
}
lean_ctor_set(x_386, 0, x_372);
lean_ctor_set(x_386, 1, x_385);
lean_ctor_set(x_386, 2, x_373);
lean_ctor_set(x_386, 3, x_374);
lean_ctor_set(x_386, 4, x_375);
x_387 = lean_st_ref_set(x_3, x_386, x_371);
lean_dec(x_3);
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_389 = x_387;
} else {
 lean_dec_ref(x_387);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_390 = x_389;
}
lean_ctor_set(x_390, 0, x_365);
lean_ctor_set(x_390, 1, x_388);
return x_390;
}
else
{
lean_object* x_391; 
lean_dec(x_305);
lean_dec(x_3);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_365);
lean_ctor_set(x_391, 1, x_366);
return x_391;
}
}
}
else
{
uint8_t x_392; 
lean_dec(x_305);
lean_dec(x_3);
x_392 = !lean_is_exclusive(x_316);
if (x_392 == 0)
{
return x_316;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_ctor_get(x_316, 0);
x_394 = lean_ctor_get(x_316, 1);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_316);
x_395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
return x_395;
}
}
}
else
{
lean_object* x_396; 
lean_dec(x_305);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_396 = lean_ctor_get(x_313, 0);
lean_inc(x_396);
lean_dec(x_313);
lean_ctor_set(x_307, 0, x_396);
return x_307;
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_397 = lean_ctor_get(x_307, 0);
x_398 = lean_ctor_get(x_307, 1);
lean_inc(x_398);
lean_inc(x_397);
lean_dec(x_307);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
lean_dec(x_397);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
lean_dec(x_399);
x_401 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_400, x_305);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; uint8_t x_403; lean_object* x_404; 
x_402 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1;
x_403 = 0;
lean_inc(x_3);
x_404 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_1, x_402, x_403, x_2, x_3, x_4, x_5, x_398);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_407 = x_404;
} else {
 lean_dec_ref(x_404);
 x_407 = lean_box(0);
}
x_408 = l_Lean_Expr_hasMVar(x_405);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_407);
x_409 = lean_st_ref_take(x_3, x_406);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_410, 1);
lean_inc(x_411);
x_412 = lean_ctor_get(x_409, 1);
lean_inc(x_412);
lean_dec(x_409);
x_413 = lean_ctor_get(x_410, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_410, 2);
lean_inc(x_414);
x_415 = lean_ctor_get(x_410, 3);
lean_inc(x_415);
x_416 = lean_ctor_get(x_410, 4);
lean_inc(x_416);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 x_417 = x_410;
} else {
 lean_dec_ref(x_410);
 x_417 = lean_box(0);
}
x_418 = lean_ctor_get(x_411, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_411, 1);
lean_inc(x_419);
x_420 = lean_ctor_get(x_411, 2);
lean_inc(x_420);
x_421 = lean_ctor_get(x_411, 3);
lean_inc(x_421);
x_422 = lean_ctor_get(x_411, 4);
lean_inc(x_422);
x_423 = lean_ctor_get(x_411, 5);
lean_inc(x_423);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 lean_ctor_release(x_411, 2);
 lean_ctor_release(x_411, 3);
 lean_ctor_release(x_411, 4);
 lean_ctor_release(x_411, 5);
 x_424 = x_411;
} else {
 lean_dec_ref(x_411);
 x_424 = lean_box(0);
}
lean_inc(x_405);
x_425 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_418, x_305, x_405);
if (lean_is_scalar(x_424)) {
 x_426 = lean_alloc_ctor(0, 6, 0);
} else {
 x_426 = x_424;
}
lean_ctor_set(x_426, 0, x_425);
lean_ctor_set(x_426, 1, x_419);
lean_ctor_set(x_426, 2, x_420);
lean_ctor_set(x_426, 3, x_421);
lean_ctor_set(x_426, 4, x_422);
lean_ctor_set(x_426, 5, x_423);
if (lean_is_scalar(x_417)) {
 x_427 = lean_alloc_ctor(0, 5, 0);
} else {
 x_427 = x_417;
}
lean_ctor_set(x_427, 0, x_413);
lean_ctor_set(x_427, 1, x_426);
lean_ctor_set(x_427, 2, x_414);
lean_ctor_set(x_427, 3, x_415);
lean_ctor_set(x_427, 4, x_416);
x_428 = lean_st_ref_set(x_3, x_427, x_412);
lean_dec(x_3);
x_429 = lean_ctor_get(x_428, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_430 = x_428;
} else {
 lean_dec_ref(x_428);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(0, 2, 0);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_405);
lean_ctor_set(x_431, 1, x_429);
return x_431;
}
else
{
lean_object* x_432; 
lean_dec(x_305);
lean_dec(x_3);
if (lean_is_scalar(x_407)) {
 x_432 = lean_alloc_ctor(0, 2, 0);
} else {
 x_432 = x_407;
}
lean_ctor_set(x_432, 0, x_405);
lean_ctor_set(x_432, 1, x_406);
return x_432;
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_305);
lean_dec(x_3);
x_433 = lean_ctor_get(x_404, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_404, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_435 = x_404;
} else {
 lean_dec_ref(x_404);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_435)) {
 x_436 = lean_alloc_ctor(1, 2, 0);
} else {
 x_436 = x_435;
}
lean_ctor_set(x_436, 0, x_433);
lean_ctor_set(x_436, 1, x_434);
return x_436;
}
}
else
{
lean_object* x_437; lean_object* x_438; 
lean_dec(x_305);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_437 = lean_ctor_get(x_401, 0);
lean_inc(x_437);
lean_dec(x_401);
x_438 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_398);
return x_438;
}
}
}
else
{
lean_object* x_439; uint8_t x_440; lean_object* x_441; 
x_439 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1;
x_440 = 0;
x_441 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_1, x_439, x_440, x_2, x_3, x_4, x_5, x_6);
return x_441;
}
}
case 9:
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_442 = lean_ctor_get(x_1, 0);
lean_inc(x_442);
lean_dec(x_1);
x_443 = l_Lean_Literal_type(x_442);
lean_dec(x_442);
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_6);
return x_444;
}
case 10:
{
lean_object* x_445; 
x_445 = lean_ctor_get(x_1, 1);
lean_inc(x_445);
lean_dec(x_1);
x_1 = x_445;
goto _start;
}
case 11:
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; 
x_447 = lean_ctor_get(x_1, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_1, 1);
lean_inc(x_448);
x_449 = lean_ctor_get(x_1, 2);
lean_inc(x_449);
x_450 = l_Lean_Expr_hasMVar(x_1);
if (x_450 == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; 
x_451 = l_Lean_Meta_mkExprConfigCacheKey(x_1, x_2, x_3, x_4, x_5, x_6);
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec(x_451);
x_454 = lean_st_ref_get(x_3, x_453);
x_455 = !lean_is_exclusive(x_454);
if (x_455 == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_456 = lean_ctor_get(x_454, 0);
x_457 = lean_ctor_get(x_454, 1);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec(x_456);
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
lean_dec(x_458);
x_460 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_459, x_452);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; 
lean_free_object(x_454);
lean_inc(x_3);
x_461 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(x_447, x_448, x_449, x_2, x_3, x_4, x_5, x_457);
if (lean_obj_tag(x_461) == 0)
{
uint8_t x_462; 
x_462 = !lean_is_exclusive(x_461);
if (x_462 == 0)
{
lean_object* x_463; lean_object* x_464; uint8_t x_465; 
x_463 = lean_ctor_get(x_461, 0);
x_464 = lean_ctor_get(x_461, 1);
x_465 = l_Lean_Expr_hasMVar(x_463);
if (x_465 == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; 
lean_free_object(x_461);
x_466 = lean_st_ref_take(x_3, x_464);
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_467, 1);
lean_inc(x_468);
x_469 = lean_ctor_get(x_466, 1);
lean_inc(x_469);
lean_dec(x_466);
x_470 = !lean_is_exclusive(x_467);
if (x_470 == 0)
{
lean_object* x_471; uint8_t x_472; 
x_471 = lean_ctor_get(x_467, 1);
lean_dec(x_471);
x_472 = !lean_is_exclusive(x_468);
if (x_472 == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; uint8_t x_476; 
x_473 = lean_ctor_get(x_468, 0);
lean_inc(x_463);
x_474 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_473, x_452, x_463);
lean_ctor_set(x_468, 0, x_474);
x_475 = lean_st_ref_set(x_3, x_467, x_469);
lean_dec(x_3);
x_476 = !lean_is_exclusive(x_475);
if (x_476 == 0)
{
lean_object* x_477; 
x_477 = lean_ctor_get(x_475, 0);
lean_dec(x_477);
lean_ctor_set(x_475, 0, x_463);
return x_475;
}
else
{
lean_object* x_478; lean_object* x_479; 
x_478 = lean_ctor_get(x_475, 1);
lean_inc(x_478);
lean_dec(x_475);
x_479 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_479, 0, x_463);
lean_ctor_set(x_479, 1, x_478);
return x_479;
}
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_480 = lean_ctor_get(x_468, 0);
x_481 = lean_ctor_get(x_468, 1);
x_482 = lean_ctor_get(x_468, 2);
x_483 = lean_ctor_get(x_468, 3);
x_484 = lean_ctor_get(x_468, 4);
x_485 = lean_ctor_get(x_468, 5);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_inc(x_482);
lean_inc(x_481);
lean_inc(x_480);
lean_dec(x_468);
lean_inc(x_463);
x_486 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_480, x_452, x_463);
x_487 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_481);
lean_ctor_set(x_487, 2, x_482);
lean_ctor_set(x_487, 3, x_483);
lean_ctor_set(x_487, 4, x_484);
lean_ctor_set(x_487, 5, x_485);
lean_ctor_set(x_467, 1, x_487);
x_488 = lean_st_ref_set(x_3, x_467, x_469);
lean_dec(x_3);
x_489 = lean_ctor_get(x_488, 1);
lean_inc(x_489);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 x_490 = x_488;
} else {
 lean_dec_ref(x_488);
 x_490 = lean_box(0);
}
if (lean_is_scalar(x_490)) {
 x_491 = lean_alloc_ctor(0, 2, 0);
} else {
 x_491 = x_490;
}
lean_ctor_set(x_491, 0, x_463);
lean_ctor_set(x_491, 1, x_489);
return x_491;
}
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_492 = lean_ctor_get(x_467, 0);
x_493 = lean_ctor_get(x_467, 2);
x_494 = lean_ctor_get(x_467, 3);
x_495 = lean_ctor_get(x_467, 4);
lean_inc(x_495);
lean_inc(x_494);
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_467);
x_496 = lean_ctor_get(x_468, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_468, 1);
lean_inc(x_497);
x_498 = lean_ctor_get(x_468, 2);
lean_inc(x_498);
x_499 = lean_ctor_get(x_468, 3);
lean_inc(x_499);
x_500 = lean_ctor_get(x_468, 4);
lean_inc(x_500);
x_501 = lean_ctor_get(x_468, 5);
lean_inc(x_501);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 lean_ctor_release(x_468, 2);
 lean_ctor_release(x_468, 3);
 lean_ctor_release(x_468, 4);
 lean_ctor_release(x_468, 5);
 x_502 = x_468;
} else {
 lean_dec_ref(x_468);
 x_502 = lean_box(0);
}
lean_inc(x_463);
x_503 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_496, x_452, x_463);
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
x_505 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_505, 0, x_492);
lean_ctor_set(x_505, 1, x_504);
lean_ctor_set(x_505, 2, x_493);
lean_ctor_set(x_505, 3, x_494);
lean_ctor_set(x_505, 4, x_495);
x_506 = lean_st_ref_set(x_3, x_505, x_469);
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
lean_ctor_set(x_509, 0, x_463);
lean_ctor_set(x_509, 1, x_507);
return x_509;
}
}
else
{
lean_dec(x_452);
lean_dec(x_3);
return x_461;
}
}
else
{
lean_object* x_510; lean_object* x_511; uint8_t x_512; 
x_510 = lean_ctor_get(x_461, 0);
x_511 = lean_ctor_get(x_461, 1);
lean_inc(x_511);
lean_inc(x_510);
lean_dec(x_461);
x_512 = l_Lean_Expr_hasMVar(x_510);
if (x_512 == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_513 = lean_st_ref_take(x_3, x_511);
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_514, 1);
lean_inc(x_515);
x_516 = lean_ctor_get(x_513, 1);
lean_inc(x_516);
lean_dec(x_513);
x_517 = lean_ctor_get(x_514, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_514, 2);
lean_inc(x_518);
x_519 = lean_ctor_get(x_514, 3);
lean_inc(x_519);
x_520 = lean_ctor_get(x_514, 4);
lean_inc(x_520);
if (lean_is_exclusive(x_514)) {
 lean_ctor_release(x_514, 0);
 lean_ctor_release(x_514, 1);
 lean_ctor_release(x_514, 2);
 lean_ctor_release(x_514, 3);
 lean_ctor_release(x_514, 4);
 x_521 = x_514;
} else {
 lean_dec_ref(x_514);
 x_521 = lean_box(0);
}
x_522 = lean_ctor_get(x_515, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_515, 1);
lean_inc(x_523);
x_524 = lean_ctor_get(x_515, 2);
lean_inc(x_524);
x_525 = lean_ctor_get(x_515, 3);
lean_inc(x_525);
x_526 = lean_ctor_get(x_515, 4);
lean_inc(x_526);
x_527 = lean_ctor_get(x_515, 5);
lean_inc(x_527);
if (lean_is_exclusive(x_515)) {
 lean_ctor_release(x_515, 0);
 lean_ctor_release(x_515, 1);
 lean_ctor_release(x_515, 2);
 lean_ctor_release(x_515, 3);
 lean_ctor_release(x_515, 4);
 lean_ctor_release(x_515, 5);
 x_528 = x_515;
} else {
 lean_dec_ref(x_515);
 x_528 = lean_box(0);
}
lean_inc(x_510);
x_529 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_522, x_452, x_510);
if (lean_is_scalar(x_528)) {
 x_530 = lean_alloc_ctor(0, 6, 0);
} else {
 x_530 = x_528;
}
lean_ctor_set(x_530, 0, x_529);
lean_ctor_set(x_530, 1, x_523);
lean_ctor_set(x_530, 2, x_524);
lean_ctor_set(x_530, 3, x_525);
lean_ctor_set(x_530, 4, x_526);
lean_ctor_set(x_530, 5, x_527);
if (lean_is_scalar(x_521)) {
 x_531 = lean_alloc_ctor(0, 5, 0);
} else {
 x_531 = x_521;
}
lean_ctor_set(x_531, 0, x_517);
lean_ctor_set(x_531, 1, x_530);
lean_ctor_set(x_531, 2, x_518);
lean_ctor_set(x_531, 3, x_519);
lean_ctor_set(x_531, 4, x_520);
x_532 = lean_st_ref_set(x_3, x_531, x_516);
lean_dec(x_3);
x_533 = lean_ctor_get(x_532, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_534 = x_532;
} else {
 lean_dec_ref(x_532);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(0, 2, 0);
} else {
 x_535 = x_534;
}
lean_ctor_set(x_535, 0, x_510);
lean_ctor_set(x_535, 1, x_533);
return x_535;
}
else
{
lean_object* x_536; 
lean_dec(x_452);
lean_dec(x_3);
x_536 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_536, 0, x_510);
lean_ctor_set(x_536, 1, x_511);
return x_536;
}
}
}
else
{
uint8_t x_537; 
lean_dec(x_452);
lean_dec(x_3);
x_537 = !lean_is_exclusive(x_461);
if (x_537 == 0)
{
return x_461;
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_538 = lean_ctor_get(x_461, 0);
x_539 = lean_ctor_get(x_461, 1);
lean_inc(x_539);
lean_inc(x_538);
lean_dec(x_461);
x_540 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_540, 0, x_538);
lean_ctor_set(x_540, 1, x_539);
return x_540;
}
}
}
else
{
lean_object* x_541; 
lean_dec(x_452);
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_541 = lean_ctor_get(x_460, 0);
lean_inc(x_541);
lean_dec(x_460);
lean_ctor_set(x_454, 0, x_541);
return x_454;
}
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_542 = lean_ctor_get(x_454, 0);
x_543 = lean_ctor_get(x_454, 1);
lean_inc(x_543);
lean_inc(x_542);
lean_dec(x_454);
x_544 = lean_ctor_get(x_542, 1);
lean_inc(x_544);
lean_dec(x_542);
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
lean_dec(x_544);
x_546 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_545, x_452);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; 
lean_inc(x_3);
x_547 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(x_447, x_448, x_449, x_2, x_3, x_4, x_5, x_543);
if (lean_obj_tag(x_547) == 0)
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; uint8_t x_551; 
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_547, 1);
lean_inc(x_549);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 lean_ctor_release(x_547, 1);
 x_550 = x_547;
} else {
 lean_dec_ref(x_547);
 x_550 = lean_box(0);
}
x_551 = l_Lean_Expr_hasMVar(x_548);
if (x_551 == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
lean_dec(x_550);
x_552 = lean_st_ref_take(x_3, x_549);
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_553, 1);
lean_inc(x_554);
x_555 = lean_ctor_get(x_552, 1);
lean_inc(x_555);
lean_dec(x_552);
x_556 = lean_ctor_get(x_553, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_553, 2);
lean_inc(x_557);
x_558 = lean_ctor_get(x_553, 3);
lean_inc(x_558);
x_559 = lean_ctor_get(x_553, 4);
lean_inc(x_559);
if (lean_is_exclusive(x_553)) {
 lean_ctor_release(x_553, 0);
 lean_ctor_release(x_553, 1);
 lean_ctor_release(x_553, 2);
 lean_ctor_release(x_553, 3);
 lean_ctor_release(x_553, 4);
 x_560 = x_553;
} else {
 lean_dec_ref(x_553);
 x_560 = lean_box(0);
}
x_561 = lean_ctor_get(x_554, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_554, 1);
lean_inc(x_562);
x_563 = lean_ctor_get(x_554, 2);
lean_inc(x_563);
x_564 = lean_ctor_get(x_554, 3);
lean_inc(x_564);
x_565 = lean_ctor_get(x_554, 4);
lean_inc(x_565);
x_566 = lean_ctor_get(x_554, 5);
lean_inc(x_566);
if (lean_is_exclusive(x_554)) {
 lean_ctor_release(x_554, 0);
 lean_ctor_release(x_554, 1);
 lean_ctor_release(x_554, 2);
 lean_ctor_release(x_554, 3);
 lean_ctor_release(x_554, 4);
 lean_ctor_release(x_554, 5);
 x_567 = x_554;
} else {
 lean_dec_ref(x_554);
 x_567 = lean_box(0);
}
lean_inc(x_548);
x_568 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_561, x_452, x_548);
if (lean_is_scalar(x_567)) {
 x_569 = lean_alloc_ctor(0, 6, 0);
} else {
 x_569 = x_567;
}
lean_ctor_set(x_569, 0, x_568);
lean_ctor_set(x_569, 1, x_562);
lean_ctor_set(x_569, 2, x_563);
lean_ctor_set(x_569, 3, x_564);
lean_ctor_set(x_569, 4, x_565);
lean_ctor_set(x_569, 5, x_566);
if (lean_is_scalar(x_560)) {
 x_570 = lean_alloc_ctor(0, 5, 0);
} else {
 x_570 = x_560;
}
lean_ctor_set(x_570, 0, x_556);
lean_ctor_set(x_570, 1, x_569);
lean_ctor_set(x_570, 2, x_557);
lean_ctor_set(x_570, 3, x_558);
lean_ctor_set(x_570, 4, x_559);
x_571 = lean_st_ref_set(x_3, x_570, x_555);
lean_dec(x_3);
x_572 = lean_ctor_get(x_571, 1);
lean_inc(x_572);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 lean_ctor_release(x_571, 1);
 x_573 = x_571;
} else {
 lean_dec_ref(x_571);
 x_573 = lean_box(0);
}
if (lean_is_scalar(x_573)) {
 x_574 = lean_alloc_ctor(0, 2, 0);
} else {
 x_574 = x_573;
}
lean_ctor_set(x_574, 0, x_548);
lean_ctor_set(x_574, 1, x_572);
return x_574;
}
else
{
lean_object* x_575; 
lean_dec(x_452);
lean_dec(x_3);
if (lean_is_scalar(x_550)) {
 x_575 = lean_alloc_ctor(0, 2, 0);
} else {
 x_575 = x_550;
}
lean_ctor_set(x_575, 0, x_548);
lean_ctor_set(x_575, 1, x_549);
return x_575;
}
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
lean_dec(x_452);
lean_dec(x_3);
x_576 = lean_ctor_get(x_547, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_547, 1);
lean_inc(x_577);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 lean_ctor_release(x_547, 1);
 x_578 = x_547;
} else {
 lean_dec_ref(x_547);
 x_578 = lean_box(0);
}
if (lean_is_scalar(x_578)) {
 x_579 = lean_alloc_ctor(1, 2, 0);
} else {
 x_579 = x_578;
}
lean_ctor_set(x_579, 0, x_576);
lean_ctor_set(x_579, 1, x_577);
return x_579;
}
}
else
{
lean_object* x_580; lean_object* x_581; 
lean_dec(x_452);
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_580 = lean_ctor_get(x_546, 0);
lean_inc(x_580);
lean_dec(x_546);
x_581 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_581, 0, x_580);
lean_ctor_set(x_581, 1, x_543);
return x_581;
}
}
}
else
{
lean_object* x_582; 
lean_dec(x_1);
x_582 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(x_447, x_448, x_449, x_2, x_3, x_4, x_5, x_6);
return x_582;
}
}
default: 
{
uint8_t x_583; 
x_583 = l_Lean_Expr_hasMVar(x_1);
if (x_583 == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; uint8_t x_588; 
lean_inc(x_1);
x_584 = l_Lean_Meta_mkExprConfigCacheKey(x_1, x_2, x_3, x_4, x_5, x_6);
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_584, 1);
lean_inc(x_586);
lean_dec(x_584);
x_587 = lean_st_ref_get(x_3, x_586);
x_588 = !lean_is_exclusive(x_587);
if (x_588 == 0)
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_589 = lean_ctor_get(x_587, 0);
x_590 = lean_ctor_get(x_587, 1);
x_591 = lean_ctor_get(x_589, 1);
lean_inc(x_591);
lean_dec(x_589);
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
lean_dec(x_591);
x_593 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_592, x_585);
if (lean_obj_tag(x_593) == 0)
{
lean_object* x_594; uint8_t x_595; lean_object* x_596; 
lean_free_object(x_587);
x_594 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1;
x_595 = 0;
lean_inc(x_3);
x_596 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_1, x_594, x_595, x_2, x_3, x_4, x_5, x_590);
if (lean_obj_tag(x_596) == 0)
{
uint8_t x_597; 
x_597 = !lean_is_exclusive(x_596);
if (x_597 == 0)
{
lean_object* x_598; lean_object* x_599; uint8_t x_600; 
x_598 = lean_ctor_get(x_596, 0);
x_599 = lean_ctor_get(x_596, 1);
x_600 = l_Lean_Expr_hasMVar(x_598);
if (x_600 == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; uint8_t x_605; 
lean_free_object(x_596);
x_601 = lean_st_ref_take(x_3, x_599);
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_602, 1);
lean_inc(x_603);
x_604 = lean_ctor_get(x_601, 1);
lean_inc(x_604);
lean_dec(x_601);
x_605 = !lean_is_exclusive(x_602);
if (x_605 == 0)
{
lean_object* x_606; uint8_t x_607; 
x_606 = lean_ctor_get(x_602, 1);
lean_dec(x_606);
x_607 = !lean_is_exclusive(x_603);
if (x_607 == 0)
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; uint8_t x_611; 
x_608 = lean_ctor_get(x_603, 0);
lean_inc(x_598);
x_609 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_608, x_585, x_598);
lean_ctor_set(x_603, 0, x_609);
x_610 = lean_st_ref_set(x_3, x_602, x_604);
lean_dec(x_3);
x_611 = !lean_is_exclusive(x_610);
if (x_611 == 0)
{
lean_object* x_612; 
x_612 = lean_ctor_get(x_610, 0);
lean_dec(x_612);
lean_ctor_set(x_610, 0, x_598);
return x_610;
}
else
{
lean_object* x_613; lean_object* x_614; 
x_613 = lean_ctor_get(x_610, 1);
lean_inc(x_613);
lean_dec(x_610);
x_614 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_614, 0, x_598);
lean_ctor_set(x_614, 1, x_613);
return x_614;
}
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_615 = lean_ctor_get(x_603, 0);
x_616 = lean_ctor_get(x_603, 1);
x_617 = lean_ctor_get(x_603, 2);
x_618 = lean_ctor_get(x_603, 3);
x_619 = lean_ctor_get(x_603, 4);
x_620 = lean_ctor_get(x_603, 5);
lean_inc(x_620);
lean_inc(x_619);
lean_inc(x_618);
lean_inc(x_617);
lean_inc(x_616);
lean_inc(x_615);
lean_dec(x_603);
lean_inc(x_598);
x_621 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_615, x_585, x_598);
x_622 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_616);
lean_ctor_set(x_622, 2, x_617);
lean_ctor_set(x_622, 3, x_618);
lean_ctor_set(x_622, 4, x_619);
lean_ctor_set(x_622, 5, x_620);
lean_ctor_set(x_602, 1, x_622);
x_623 = lean_st_ref_set(x_3, x_602, x_604);
lean_dec(x_3);
x_624 = lean_ctor_get(x_623, 1);
lean_inc(x_624);
if (lean_is_exclusive(x_623)) {
 lean_ctor_release(x_623, 0);
 lean_ctor_release(x_623, 1);
 x_625 = x_623;
} else {
 lean_dec_ref(x_623);
 x_625 = lean_box(0);
}
if (lean_is_scalar(x_625)) {
 x_626 = lean_alloc_ctor(0, 2, 0);
} else {
 x_626 = x_625;
}
lean_ctor_set(x_626, 0, x_598);
lean_ctor_set(x_626, 1, x_624);
return x_626;
}
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_627 = lean_ctor_get(x_602, 0);
x_628 = lean_ctor_get(x_602, 2);
x_629 = lean_ctor_get(x_602, 3);
x_630 = lean_ctor_get(x_602, 4);
lean_inc(x_630);
lean_inc(x_629);
lean_inc(x_628);
lean_inc(x_627);
lean_dec(x_602);
x_631 = lean_ctor_get(x_603, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_603, 1);
lean_inc(x_632);
x_633 = lean_ctor_get(x_603, 2);
lean_inc(x_633);
x_634 = lean_ctor_get(x_603, 3);
lean_inc(x_634);
x_635 = lean_ctor_get(x_603, 4);
lean_inc(x_635);
x_636 = lean_ctor_get(x_603, 5);
lean_inc(x_636);
if (lean_is_exclusive(x_603)) {
 lean_ctor_release(x_603, 0);
 lean_ctor_release(x_603, 1);
 lean_ctor_release(x_603, 2);
 lean_ctor_release(x_603, 3);
 lean_ctor_release(x_603, 4);
 lean_ctor_release(x_603, 5);
 x_637 = x_603;
} else {
 lean_dec_ref(x_603);
 x_637 = lean_box(0);
}
lean_inc(x_598);
x_638 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_631, x_585, x_598);
if (lean_is_scalar(x_637)) {
 x_639 = lean_alloc_ctor(0, 6, 0);
} else {
 x_639 = x_637;
}
lean_ctor_set(x_639, 0, x_638);
lean_ctor_set(x_639, 1, x_632);
lean_ctor_set(x_639, 2, x_633);
lean_ctor_set(x_639, 3, x_634);
lean_ctor_set(x_639, 4, x_635);
lean_ctor_set(x_639, 5, x_636);
x_640 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_640, 0, x_627);
lean_ctor_set(x_640, 1, x_639);
lean_ctor_set(x_640, 2, x_628);
lean_ctor_set(x_640, 3, x_629);
lean_ctor_set(x_640, 4, x_630);
x_641 = lean_st_ref_set(x_3, x_640, x_604);
lean_dec(x_3);
x_642 = lean_ctor_get(x_641, 1);
lean_inc(x_642);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_643 = x_641;
} else {
 lean_dec_ref(x_641);
 x_643 = lean_box(0);
}
if (lean_is_scalar(x_643)) {
 x_644 = lean_alloc_ctor(0, 2, 0);
} else {
 x_644 = x_643;
}
lean_ctor_set(x_644, 0, x_598);
lean_ctor_set(x_644, 1, x_642);
return x_644;
}
}
else
{
lean_dec(x_585);
lean_dec(x_3);
return x_596;
}
}
else
{
lean_object* x_645; lean_object* x_646; uint8_t x_647; 
x_645 = lean_ctor_get(x_596, 0);
x_646 = lean_ctor_get(x_596, 1);
lean_inc(x_646);
lean_inc(x_645);
lean_dec(x_596);
x_647 = l_Lean_Expr_hasMVar(x_645);
if (x_647 == 0)
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
x_648 = lean_st_ref_take(x_3, x_646);
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_649, 1);
lean_inc(x_650);
x_651 = lean_ctor_get(x_648, 1);
lean_inc(x_651);
lean_dec(x_648);
x_652 = lean_ctor_get(x_649, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_649, 2);
lean_inc(x_653);
x_654 = lean_ctor_get(x_649, 3);
lean_inc(x_654);
x_655 = lean_ctor_get(x_649, 4);
lean_inc(x_655);
if (lean_is_exclusive(x_649)) {
 lean_ctor_release(x_649, 0);
 lean_ctor_release(x_649, 1);
 lean_ctor_release(x_649, 2);
 lean_ctor_release(x_649, 3);
 lean_ctor_release(x_649, 4);
 x_656 = x_649;
} else {
 lean_dec_ref(x_649);
 x_656 = lean_box(0);
}
x_657 = lean_ctor_get(x_650, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_650, 1);
lean_inc(x_658);
x_659 = lean_ctor_get(x_650, 2);
lean_inc(x_659);
x_660 = lean_ctor_get(x_650, 3);
lean_inc(x_660);
x_661 = lean_ctor_get(x_650, 4);
lean_inc(x_661);
x_662 = lean_ctor_get(x_650, 5);
lean_inc(x_662);
if (lean_is_exclusive(x_650)) {
 lean_ctor_release(x_650, 0);
 lean_ctor_release(x_650, 1);
 lean_ctor_release(x_650, 2);
 lean_ctor_release(x_650, 3);
 lean_ctor_release(x_650, 4);
 lean_ctor_release(x_650, 5);
 x_663 = x_650;
} else {
 lean_dec_ref(x_650);
 x_663 = lean_box(0);
}
lean_inc(x_645);
x_664 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_657, x_585, x_645);
if (lean_is_scalar(x_663)) {
 x_665 = lean_alloc_ctor(0, 6, 0);
} else {
 x_665 = x_663;
}
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_658);
lean_ctor_set(x_665, 2, x_659);
lean_ctor_set(x_665, 3, x_660);
lean_ctor_set(x_665, 4, x_661);
lean_ctor_set(x_665, 5, x_662);
if (lean_is_scalar(x_656)) {
 x_666 = lean_alloc_ctor(0, 5, 0);
} else {
 x_666 = x_656;
}
lean_ctor_set(x_666, 0, x_652);
lean_ctor_set(x_666, 1, x_665);
lean_ctor_set(x_666, 2, x_653);
lean_ctor_set(x_666, 3, x_654);
lean_ctor_set(x_666, 4, x_655);
x_667 = lean_st_ref_set(x_3, x_666, x_651);
lean_dec(x_3);
x_668 = lean_ctor_get(x_667, 1);
lean_inc(x_668);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 lean_ctor_release(x_667, 1);
 x_669 = x_667;
} else {
 lean_dec_ref(x_667);
 x_669 = lean_box(0);
}
if (lean_is_scalar(x_669)) {
 x_670 = lean_alloc_ctor(0, 2, 0);
} else {
 x_670 = x_669;
}
lean_ctor_set(x_670, 0, x_645);
lean_ctor_set(x_670, 1, x_668);
return x_670;
}
else
{
lean_object* x_671; 
lean_dec(x_585);
lean_dec(x_3);
x_671 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_671, 0, x_645);
lean_ctor_set(x_671, 1, x_646);
return x_671;
}
}
}
else
{
uint8_t x_672; 
lean_dec(x_585);
lean_dec(x_3);
x_672 = !lean_is_exclusive(x_596);
if (x_672 == 0)
{
return x_596;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_673 = lean_ctor_get(x_596, 0);
x_674 = lean_ctor_get(x_596, 1);
lean_inc(x_674);
lean_inc(x_673);
lean_dec(x_596);
x_675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_675, 0, x_673);
lean_ctor_set(x_675, 1, x_674);
return x_675;
}
}
}
else
{
lean_object* x_676; 
lean_dec(x_585);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_676 = lean_ctor_get(x_593, 0);
lean_inc(x_676);
lean_dec(x_593);
lean_ctor_set(x_587, 0, x_676);
return x_587;
}
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; 
x_677 = lean_ctor_get(x_587, 0);
x_678 = lean_ctor_get(x_587, 1);
lean_inc(x_678);
lean_inc(x_677);
lean_dec(x_587);
x_679 = lean_ctor_get(x_677, 1);
lean_inc(x_679);
lean_dec(x_677);
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
lean_dec(x_679);
x_681 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_680, x_585);
if (lean_obj_tag(x_681) == 0)
{
lean_object* x_682; uint8_t x_683; lean_object* x_684; 
x_682 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1;
x_683 = 0;
lean_inc(x_3);
x_684 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_1, x_682, x_683, x_2, x_3, x_4, x_5, x_678);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; uint8_t x_688; 
x_685 = lean_ctor_get(x_684, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_684, 1);
lean_inc(x_686);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 x_687 = x_684;
} else {
 lean_dec_ref(x_684);
 x_687 = lean_box(0);
}
x_688 = l_Lean_Expr_hasMVar(x_685);
if (x_688 == 0)
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
lean_dec(x_687);
x_689 = lean_st_ref_take(x_3, x_686);
x_690 = lean_ctor_get(x_689, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_690, 1);
lean_inc(x_691);
x_692 = lean_ctor_get(x_689, 1);
lean_inc(x_692);
lean_dec(x_689);
x_693 = lean_ctor_get(x_690, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_690, 2);
lean_inc(x_694);
x_695 = lean_ctor_get(x_690, 3);
lean_inc(x_695);
x_696 = lean_ctor_get(x_690, 4);
lean_inc(x_696);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 lean_ctor_release(x_690, 2);
 lean_ctor_release(x_690, 3);
 lean_ctor_release(x_690, 4);
 x_697 = x_690;
} else {
 lean_dec_ref(x_690);
 x_697 = lean_box(0);
}
x_698 = lean_ctor_get(x_691, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_691, 1);
lean_inc(x_699);
x_700 = lean_ctor_get(x_691, 2);
lean_inc(x_700);
x_701 = lean_ctor_get(x_691, 3);
lean_inc(x_701);
x_702 = lean_ctor_get(x_691, 4);
lean_inc(x_702);
x_703 = lean_ctor_get(x_691, 5);
lean_inc(x_703);
if (lean_is_exclusive(x_691)) {
 lean_ctor_release(x_691, 0);
 lean_ctor_release(x_691, 1);
 lean_ctor_release(x_691, 2);
 lean_ctor_release(x_691, 3);
 lean_ctor_release(x_691, 4);
 lean_ctor_release(x_691, 5);
 x_704 = x_691;
} else {
 lean_dec_ref(x_691);
 x_704 = lean_box(0);
}
lean_inc(x_685);
x_705 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_698, x_585, x_685);
if (lean_is_scalar(x_704)) {
 x_706 = lean_alloc_ctor(0, 6, 0);
} else {
 x_706 = x_704;
}
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_699);
lean_ctor_set(x_706, 2, x_700);
lean_ctor_set(x_706, 3, x_701);
lean_ctor_set(x_706, 4, x_702);
lean_ctor_set(x_706, 5, x_703);
if (lean_is_scalar(x_697)) {
 x_707 = lean_alloc_ctor(0, 5, 0);
} else {
 x_707 = x_697;
}
lean_ctor_set(x_707, 0, x_693);
lean_ctor_set(x_707, 1, x_706);
lean_ctor_set(x_707, 2, x_694);
lean_ctor_set(x_707, 3, x_695);
lean_ctor_set(x_707, 4, x_696);
x_708 = lean_st_ref_set(x_3, x_707, x_692);
lean_dec(x_3);
x_709 = lean_ctor_get(x_708, 1);
lean_inc(x_709);
if (lean_is_exclusive(x_708)) {
 lean_ctor_release(x_708, 0);
 lean_ctor_release(x_708, 1);
 x_710 = x_708;
} else {
 lean_dec_ref(x_708);
 x_710 = lean_box(0);
}
if (lean_is_scalar(x_710)) {
 x_711 = lean_alloc_ctor(0, 2, 0);
} else {
 x_711 = x_710;
}
lean_ctor_set(x_711, 0, x_685);
lean_ctor_set(x_711, 1, x_709);
return x_711;
}
else
{
lean_object* x_712; 
lean_dec(x_585);
lean_dec(x_3);
if (lean_is_scalar(x_687)) {
 x_712 = lean_alloc_ctor(0, 2, 0);
} else {
 x_712 = x_687;
}
lean_ctor_set(x_712, 0, x_685);
lean_ctor_set(x_712, 1, x_686);
return x_712;
}
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
lean_dec(x_585);
lean_dec(x_3);
x_713 = lean_ctor_get(x_684, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_684, 1);
lean_inc(x_714);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 x_715 = x_684;
} else {
 lean_dec_ref(x_684);
 x_715 = lean_box(0);
}
if (lean_is_scalar(x_715)) {
 x_716 = lean_alloc_ctor(1, 2, 0);
} else {
 x_716 = x_715;
}
lean_ctor_set(x_716, 0, x_713);
lean_ctor_set(x_716, 1, x_714);
return x_716;
}
}
else
{
lean_object* x_717; lean_object* x_718; 
lean_dec(x_585);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_717 = lean_ctor_get(x_681, 0);
lean_inc(x_717);
lean_dec(x_681);
x_718 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_718, 0, x_717);
lean_ctor_set(x_718, 1, x_678);
return x_718;
}
}
}
else
{
lean_object* x_719; uint8_t x_720; lean_object* x_721; 
x_719 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1;
x_720 = 0;
x_721 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_1, x_719, x_720, x_2, x_3, x_4, x_5, x_6);
return x_721;
}
}
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__3;
x_2 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__5;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__6;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* lean_infer_type(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 5);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 6);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 7);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 8);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 9);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 10);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_4, sizeof(void*)*12);
x_19 = lean_ctor_get(x_4, 11);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_4, sizeof(void*)*12 + 1);
x_21 = lean_nat_dec_eq(x_10, x_11);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_23 = lean_ctor_get(x_4, 11);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 10);
lean_dec(x_24);
x_25 = lean_ctor_get(x_4, 9);
lean_dec(x_25);
x_26 = lean_ctor_get(x_4, 8);
lean_dec(x_26);
x_27 = lean_ctor_get(x_4, 7);
lean_dec(x_27);
x_28 = lean_ctor_get(x_4, 6);
lean_dec(x_28);
x_29 = lean_ctor_get(x_4, 5);
lean_dec(x_29);
x_30 = lean_ctor_get(x_4, 4);
lean_dec(x_30);
x_31 = lean_ctor_get(x_4, 3);
lean_dec(x_31);
x_32 = lean_ctor_get(x_4, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_4, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_4, 0);
lean_dec(x_34);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_10, x_35);
lean_dec(x_10);
lean_ctor_set(x_4, 3, x_36);
x_37 = !lean_is_exclusive(x_2);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_2, 0);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
uint64_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; 
x_40 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_41 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_42 = lean_ctor_get(x_2, 1);
x_43 = lean_ctor_get(x_2, 2);
x_44 = lean_ctor_get(x_2, 3);
x_45 = lean_ctor_get(x_2, 4);
x_46 = lean_ctor_get(x_2, 5);
x_47 = lean_ctor_get(x_2, 6);
x_48 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_49 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
x_50 = lean_ctor_get_uint8(x_38, 0);
x_51 = lean_ctor_get_uint8(x_38, 1);
x_52 = lean_ctor_get_uint8(x_38, 2);
x_53 = lean_ctor_get_uint8(x_38, 3);
x_54 = lean_ctor_get_uint8(x_38, 4);
x_55 = lean_ctor_get_uint8(x_38, 5);
x_56 = lean_ctor_get_uint8(x_38, 6);
x_57 = lean_ctor_get_uint8(x_38, 7);
x_58 = lean_ctor_get_uint8(x_38, 8);
x_59 = lean_ctor_get_uint8(x_38, 9);
x_60 = lean_ctor_get_uint8(x_38, 10);
x_61 = lean_ctor_get_uint8(x_38, 11);
x_62 = 1;
x_63 = l_Lean_Meta_TransparencyMode_lt(x_59, x_62);
x_64 = 2;
x_65 = lean_uint64_shift_right(x_40, x_64);
x_66 = lean_uint64_shift_left(x_65, x_64);
if (x_63 == 0)
{
uint64_t x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = l_Lean_Meta_TransparencyMode_toUInt64(x_59);
x_68 = lean_uint64_lor(x_66, x_67);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_68);
x_69 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get_uint8(x_70, 13);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_70);
lean_dec(x_2);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = 1;
x_74 = 2;
x_75 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_75, 0, x_50);
lean_ctor_set_uint8(x_75, 1, x_51);
lean_ctor_set_uint8(x_75, 2, x_52);
lean_ctor_set_uint8(x_75, 3, x_53);
lean_ctor_set_uint8(x_75, 4, x_54);
lean_ctor_set_uint8(x_75, 5, x_55);
lean_ctor_set_uint8(x_75, 6, x_56);
lean_ctor_set_uint8(x_75, 7, x_57);
lean_ctor_set_uint8(x_75, 8, x_58);
lean_ctor_set_uint8(x_75, 9, x_59);
lean_ctor_set_uint8(x_75, 10, x_60);
lean_ctor_set_uint8(x_75, 11, x_61);
lean_ctor_set_uint8(x_75, 12, x_73);
lean_ctor_set_uint8(x_75, 13, x_73);
lean_ctor_set_uint8(x_75, 14, x_74);
lean_ctor_set_uint8(x_75, 15, x_73);
lean_ctor_set_uint8(x_75, 16, x_73);
x_76 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_75);
x_77 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_42);
lean_ctor_set(x_77, 2, x_43);
lean_ctor_set(x_77, 3, x_44);
lean_ctor_set(x_77, 4, x_45);
lean_ctor_set(x_77, 5, x_46);
lean_ctor_set(x_77, 6, x_47);
lean_ctor_set_uint64(x_77, sizeof(void*)*7, x_76);
lean_ctor_set_uint8(x_77, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_77, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_77, sizeof(void*)*7 + 10, x_49);
x_78 = l_Lean_Meta_inferTypeImp_infer(x_1, x_77, x_3, x_4, x_5, x_72);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
return x_78;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_78);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_78);
if (x_83 == 0)
{
return x_78;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_78, 0);
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_78);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
x_87 = lean_ctor_get_uint8(x_70, 12);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; uint8_t x_90; lean_object* x_91; uint64_t x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_70);
lean_dec(x_2);
x_88 = lean_ctor_get(x_69, 1);
lean_inc(x_88);
lean_dec(x_69);
x_89 = 1;
x_90 = 2;
x_91 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_91, 0, x_50);
lean_ctor_set_uint8(x_91, 1, x_51);
lean_ctor_set_uint8(x_91, 2, x_52);
lean_ctor_set_uint8(x_91, 3, x_53);
lean_ctor_set_uint8(x_91, 4, x_54);
lean_ctor_set_uint8(x_91, 5, x_55);
lean_ctor_set_uint8(x_91, 6, x_56);
lean_ctor_set_uint8(x_91, 7, x_57);
lean_ctor_set_uint8(x_91, 8, x_58);
lean_ctor_set_uint8(x_91, 9, x_59);
lean_ctor_set_uint8(x_91, 10, x_60);
lean_ctor_set_uint8(x_91, 11, x_61);
lean_ctor_set_uint8(x_91, 12, x_89);
lean_ctor_set_uint8(x_91, 13, x_89);
lean_ctor_set_uint8(x_91, 14, x_90);
lean_ctor_set_uint8(x_91, 15, x_89);
lean_ctor_set_uint8(x_91, 16, x_89);
x_92 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_91);
x_93 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_42);
lean_ctor_set(x_93, 2, x_43);
lean_ctor_set(x_93, 3, x_44);
lean_ctor_set(x_93, 4, x_45);
lean_ctor_set(x_93, 5, x_46);
lean_ctor_set(x_93, 6, x_47);
lean_ctor_set_uint64(x_93, sizeof(void*)*7, x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_93, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_93, sizeof(void*)*7 + 10, x_49);
x_94 = l_Lean_Meta_inferTypeImp_infer(x_1, x_93, x_3, x_4, x_5, x_88);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
return x_94;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_94);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
else
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_94);
if (x_99 == 0)
{
return x_94;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_94, 0);
x_101 = lean_ctor_get(x_94, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_94);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
x_103 = lean_ctor_get_uint8(x_70, 15);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; uint8_t x_106; lean_object* x_107; uint64_t x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_70);
lean_dec(x_2);
x_104 = lean_ctor_get(x_69, 1);
lean_inc(x_104);
lean_dec(x_69);
x_105 = 1;
x_106 = 2;
x_107 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_107, 0, x_50);
lean_ctor_set_uint8(x_107, 1, x_51);
lean_ctor_set_uint8(x_107, 2, x_52);
lean_ctor_set_uint8(x_107, 3, x_53);
lean_ctor_set_uint8(x_107, 4, x_54);
lean_ctor_set_uint8(x_107, 5, x_55);
lean_ctor_set_uint8(x_107, 6, x_56);
lean_ctor_set_uint8(x_107, 7, x_57);
lean_ctor_set_uint8(x_107, 8, x_58);
lean_ctor_set_uint8(x_107, 9, x_59);
lean_ctor_set_uint8(x_107, 10, x_60);
lean_ctor_set_uint8(x_107, 11, x_61);
lean_ctor_set_uint8(x_107, 12, x_105);
lean_ctor_set_uint8(x_107, 13, x_105);
lean_ctor_set_uint8(x_107, 14, x_106);
lean_ctor_set_uint8(x_107, 15, x_105);
lean_ctor_set_uint8(x_107, 16, x_105);
x_108 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_107);
x_109 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_42);
lean_ctor_set(x_109, 2, x_43);
lean_ctor_set(x_109, 3, x_44);
lean_ctor_set(x_109, 4, x_45);
lean_ctor_set(x_109, 5, x_46);
lean_ctor_set(x_109, 6, x_47);
lean_ctor_set_uint64(x_109, sizeof(void*)*7, x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_109, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_109, sizeof(void*)*7 + 10, x_49);
x_110 = l_Lean_Meta_inferTypeImp_infer(x_1, x_109, x_3, x_4, x_5, x_104);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
return x_110;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_110, 0);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_110);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
else
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_110);
if (x_115 == 0)
{
return x_110;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_110, 0);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_110);
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
x_119 = lean_ctor_get_uint8(x_70, 16);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; uint8_t x_122; lean_object* x_123; uint64_t x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_70);
lean_dec(x_2);
x_120 = lean_ctor_get(x_69, 1);
lean_inc(x_120);
lean_dec(x_69);
x_121 = 1;
x_122 = 2;
x_123 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_123, 0, x_50);
lean_ctor_set_uint8(x_123, 1, x_51);
lean_ctor_set_uint8(x_123, 2, x_52);
lean_ctor_set_uint8(x_123, 3, x_53);
lean_ctor_set_uint8(x_123, 4, x_54);
lean_ctor_set_uint8(x_123, 5, x_55);
lean_ctor_set_uint8(x_123, 6, x_56);
lean_ctor_set_uint8(x_123, 7, x_57);
lean_ctor_set_uint8(x_123, 8, x_58);
lean_ctor_set_uint8(x_123, 9, x_59);
lean_ctor_set_uint8(x_123, 10, x_60);
lean_ctor_set_uint8(x_123, 11, x_61);
lean_ctor_set_uint8(x_123, 12, x_121);
lean_ctor_set_uint8(x_123, 13, x_121);
lean_ctor_set_uint8(x_123, 14, x_122);
lean_ctor_set_uint8(x_123, 15, x_121);
lean_ctor_set_uint8(x_123, 16, x_121);
x_124 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_123);
x_125 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_42);
lean_ctor_set(x_125, 2, x_43);
lean_ctor_set(x_125, 3, x_44);
lean_ctor_set(x_125, 4, x_45);
lean_ctor_set(x_125, 5, x_46);
lean_ctor_set(x_125, 6, x_47);
lean_ctor_set_uint64(x_125, sizeof(void*)*7, x_124);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_125, sizeof(void*)*7 + 10, x_49);
x_126 = l_Lean_Meta_inferTypeImp_infer(x_1, x_125, x_3, x_4, x_5, x_120);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
return x_126;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_126, 0);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_126);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
else
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_126);
if (x_131 == 0)
{
return x_126;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_126, 0);
x_133 = lean_ctor_get(x_126, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_126);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
lean_object* x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; 
x_135 = lean_ctor_get(x_69, 1);
lean_inc(x_135);
lean_dec(x_69);
x_136 = lean_ctor_get_uint8(x_70, 14);
lean_dec(x_70);
x_137 = 2;
x_138 = l_Lean_Meta_instDecidableEqProjReductionKind(x_136, x_137);
if (x_138 == 0)
{
uint8_t x_139; lean_object* x_140; uint64_t x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_2);
x_139 = 1;
x_140 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_140, 0, x_50);
lean_ctor_set_uint8(x_140, 1, x_51);
lean_ctor_set_uint8(x_140, 2, x_52);
lean_ctor_set_uint8(x_140, 3, x_53);
lean_ctor_set_uint8(x_140, 4, x_54);
lean_ctor_set_uint8(x_140, 5, x_55);
lean_ctor_set_uint8(x_140, 6, x_56);
lean_ctor_set_uint8(x_140, 7, x_57);
lean_ctor_set_uint8(x_140, 8, x_58);
lean_ctor_set_uint8(x_140, 9, x_59);
lean_ctor_set_uint8(x_140, 10, x_60);
lean_ctor_set_uint8(x_140, 11, x_61);
lean_ctor_set_uint8(x_140, 12, x_139);
lean_ctor_set_uint8(x_140, 13, x_139);
lean_ctor_set_uint8(x_140, 14, x_137);
lean_ctor_set_uint8(x_140, 15, x_139);
lean_ctor_set_uint8(x_140, 16, x_139);
x_141 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_140);
x_142 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_42);
lean_ctor_set(x_142, 2, x_43);
lean_ctor_set(x_142, 3, x_44);
lean_ctor_set(x_142, 4, x_45);
lean_ctor_set(x_142, 5, x_46);
lean_ctor_set(x_142, 6, x_47);
lean_ctor_set_uint64(x_142, sizeof(void*)*7, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_142, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_142, sizeof(void*)*7 + 10, x_49);
x_143 = l_Lean_Meta_inferTypeImp_infer(x_1, x_142, x_3, x_4, x_5, x_135);
if (lean_obj_tag(x_143) == 0)
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
return x_143;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_143, 0);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_143);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
else
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_143);
if (x_148 == 0)
{
return x_143;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_143, 0);
x_150 = lean_ctor_get(x_143, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_143);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
lean_object* x_152; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_152 = l_Lean_Meta_inferTypeImp_infer(x_1, x_2, x_3, x_4, x_5, x_135);
if (lean_obj_tag(x_152) == 0)
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
return x_152;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_152, 0);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_152);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
else
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_152);
if (x_157 == 0)
{
return x_152;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_152, 0);
x_159 = lean_ctor_get(x_152, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_152);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
}
}
}
}
else
{
uint64_t x_161; uint64_t x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
lean_ctor_set_uint8(x_38, 9, x_62);
x_161 = l_Lean_Meta_withInferTypeConfig___rarg___closed__1;
x_162 = lean_uint64_lor(x_66, x_161);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_162);
x_163 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get_uint8(x_164, 13);
if (x_165 == 0)
{
lean_object* x_166; uint8_t x_167; uint8_t x_168; lean_object* x_169; uint64_t x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_164);
lean_dec(x_2);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
x_167 = 1;
x_168 = 2;
x_169 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_169, 0, x_50);
lean_ctor_set_uint8(x_169, 1, x_51);
lean_ctor_set_uint8(x_169, 2, x_52);
lean_ctor_set_uint8(x_169, 3, x_53);
lean_ctor_set_uint8(x_169, 4, x_54);
lean_ctor_set_uint8(x_169, 5, x_55);
lean_ctor_set_uint8(x_169, 6, x_56);
lean_ctor_set_uint8(x_169, 7, x_57);
lean_ctor_set_uint8(x_169, 8, x_58);
lean_ctor_set_uint8(x_169, 9, x_62);
lean_ctor_set_uint8(x_169, 10, x_60);
lean_ctor_set_uint8(x_169, 11, x_61);
lean_ctor_set_uint8(x_169, 12, x_167);
lean_ctor_set_uint8(x_169, 13, x_167);
lean_ctor_set_uint8(x_169, 14, x_168);
lean_ctor_set_uint8(x_169, 15, x_167);
lean_ctor_set_uint8(x_169, 16, x_167);
x_170 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_169);
x_171 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_42);
lean_ctor_set(x_171, 2, x_43);
lean_ctor_set(x_171, 3, x_44);
lean_ctor_set(x_171, 4, x_45);
lean_ctor_set(x_171, 5, x_46);
lean_ctor_set(x_171, 6, x_47);
lean_ctor_set_uint64(x_171, sizeof(void*)*7, x_170);
lean_ctor_set_uint8(x_171, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_171, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_171, sizeof(void*)*7 + 10, x_49);
x_172 = l_Lean_Meta_inferTypeImp_infer(x_1, x_171, x_3, x_4, x_5, x_166);
if (lean_obj_tag(x_172) == 0)
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
return x_172;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_172, 0);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_172);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
else
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_172);
if (x_177 == 0)
{
return x_172;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_172, 0);
x_179 = lean_ctor_get(x_172, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_172);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
else
{
uint8_t x_181; 
x_181 = lean_ctor_get_uint8(x_164, 12);
if (x_181 == 0)
{
lean_object* x_182; uint8_t x_183; uint8_t x_184; lean_object* x_185; uint64_t x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_164);
lean_dec(x_2);
x_182 = lean_ctor_get(x_163, 1);
lean_inc(x_182);
lean_dec(x_163);
x_183 = 1;
x_184 = 2;
x_185 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_185, 0, x_50);
lean_ctor_set_uint8(x_185, 1, x_51);
lean_ctor_set_uint8(x_185, 2, x_52);
lean_ctor_set_uint8(x_185, 3, x_53);
lean_ctor_set_uint8(x_185, 4, x_54);
lean_ctor_set_uint8(x_185, 5, x_55);
lean_ctor_set_uint8(x_185, 6, x_56);
lean_ctor_set_uint8(x_185, 7, x_57);
lean_ctor_set_uint8(x_185, 8, x_58);
lean_ctor_set_uint8(x_185, 9, x_62);
lean_ctor_set_uint8(x_185, 10, x_60);
lean_ctor_set_uint8(x_185, 11, x_61);
lean_ctor_set_uint8(x_185, 12, x_183);
lean_ctor_set_uint8(x_185, 13, x_183);
lean_ctor_set_uint8(x_185, 14, x_184);
lean_ctor_set_uint8(x_185, 15, x_183);
lean_ctor_set_uint8(x_185, 16, x_183);
x_186 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_185);
x_187 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_42);
lean_ctor_set(x_187, 2, x_43);
lean_ctor_set(x_187, 3, x_44);
lean_ctor_set(x_187, 4, x_45);
lean_ctor_set(x_187, 5, x_46);
lean_ctor_set(x_187, 6, x_47);
lean_ctor_set_uint64(x_187, sizeof(void*)*7, x_186);
lean_ctor_set_uint8(x_187, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_187, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_187, sizeof(void*)*7 + 10, x_49);
x_188 = l_Lean_Meta_inferTypeImp_infer(x_1, x_187, x_3, x_4, x_5, x_182);
if (lean_obj_tag(x_188) == 0)
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
return x_188;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_188, 0);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_188);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
else
{
uint8_t x_193; 
x_193 = !lean_is_exclusive(x_188);
if (x_193 == 0)
{
return x_188;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_188, 0);
x_195 = lean_ctor_get(x_188, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_188);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
else
{
uint8_t x_197; 
x_197 = lean_ctor_get_uint8(x_164, 15);
if (x_197 == 0)
{
lean_object* x_198; uint8_t x_199; uint8_t x_200; lean_object* x_201; uint64_t x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_164);
lean_dec(x_2);
x_198 = lean_ctor_get(x_163, 1);
lean_inc(x_198);
lean_dec(x_163);
x_199 = 1;
x_200 = 2;
x_201 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_201, 0, x_50);
lean_ctor_set_uint8(x_201, 1, x_51);
lean_ctor_set_uint8(x_201, 2, x_52);
lean_ctor_set_uint8(x_201, 3, x_53);
lean_ctor_set_uint8(x_201, 4, x_54);
lean_ctor_set_uint8(x_201, 5, x_55);
lean_ctor_set_uint8(x_201, 6, x_56);
lean_ctor_set_uint8(x_201, 7, x_57);
lean_ctor_set_uint8(x_201, 8, x_58);
lean_ctor_set_uint8(x_201, 9, x_62);
lean_ctor_set_uint8(x_201, 10, x_60);
lean_ctor_set_uint8(x_201, 11, x_61);
lean_ctor_set_uint8(x_201, 12, x_199);
lean_ctor_set_uint8(x_201, 13, x_199);
lean_ctor_set_uint8(x_201, 14, x_200);
lean_ctor_set_uint8(x_201, 15, x_199);
lean_ctor_set_uint8(x_201, 16, x_199);
x_202 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_201);
x_203 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_42);
lean_ctor_set(x_203, 2, x_43);
lean_ctor_set(x_203, 3, x_44);
lean_ctor_set(x_203, 4, x_45);
lean_ctor_set(x_203, 5, x_46);
lean_ctor_set(x_203, 6, x_47);
lean_ctor_set_uint64(x_203, sizeof(void*)*7, x_202);
lean_ctor_set_uint8(x_203, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_203, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_203, sizeof(void*)*7 + 10, x_49);
x_204 = l_Lean_Meta_inferTypeImp_infer(x_1, x_203, x_3, x_4, x_5, x_198);
if (lean_obj_tag(x_204) == 0)
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_204);
if (x_205 == 0)
{
return x_204;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_204, 0);
x_207 = lean_ctor_get(x_204, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_204);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
else
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_204);
if (x_209 == 0)
{
return x_204;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_204, 0);
x_211 = lean_ctor_get(x_204, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_204);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
else
{
uint8_t x_213; 
x_213 = lean_ctor_get_uint8(x_164, 16);
if (x_213 == 0)
{
lean_object* x_214; uint8_t x_215; uint8_t x_216; lean_object* x_217; uint64_t x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_164);
lean_dec(x_2);
x_214 = lean_ctor_get(x_163, 1);
lean_inc(x_214);
lean_dec(x_163);
x_215 = 1;
x_216 = 2;
x_217 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_217, 0, x_50);
lean_ctor_set_uint8(x_217, 1, x_51);
lean_ctor_set_uint8(x_217, 2, x_52);
lean_ctor_set_uint8(x_217, 3, x_53);
lean_ctor_set_uint8(x_217, 4, x_54);
lean_ctor_set_uint8(x_217, 5, x_55);
lean_ctor_set_uint8(x_217, 6, x_56);
lean_ctor_set_uint8(x_217, 7, x_57);
lean_ctor_set_uint8(x_217, 8, x_58);
lean_ctor_set_uint8(x_217, 9, x_62);
lean_ctor_set_uint8(x_217, 10, x_60);
lean_ctor_set_uint8(x_217, 11, x_61);
lean_ctor_set_uint8(x_217, 12, x_215);
lean_ctor_set_uint8(x_217, 13, x_215);
lean_ctor_set_uint8(x_217, 14, x_216);
lean_ctor_set_uint8(x_217, 15, x_215);
lean_ctor_set_uint8(x_217, 16, x_215);
x_218 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_217);
x_219 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_42);
lean_ctor_set(x_219, 2, x_43);
lean_ctor_set(x_219, 3, x_44);
lean_ctor_set(x_219, 4, x_45);
lean_ctor_set(x_219, 5, x_46);
lean_ctor_set(x_219, 6, x_47);
lean_ctor_set_uint64(x_219, sizeof(void*)*7, x_218);
lean_ctor_set_uint8(x_219, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_219, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_219, sizeof(void*)*7 + 10, x_49);
x_220 = l_Lean_Meta_inferTypeImp_infer(x_1, x_219, x_3, x_4, x_5, x_214);
if (lean_obj_tag(x_220) == 0)
{
uint8_t x_221; 
x_221 = !lean_is_exclusive(x_220);
if (x_221 == 0)
{
return x_220;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_220, 0);
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_220);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
else
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_220);
if (x_225 == 0)
{
return x_220;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_220, 0);
x_227 = lean_ctor_get(x_220, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_220);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
else
{
lean_object* x_229; uint8_t x_230; uint8_t x_231; uint8_t x_232; 
x_229 = lean_ctor_get(x_163, 1);
lean_inc(x_229);
lean_dec(x_163);
x_230 = lean_ctor_get_uint8(x_164, 14);
lean_dec(x_164);
x_231 = 2;
x_232 = l_Lean_Meta_instDecidableEqProjReductionKind(x_230, x_231);
if (x_232 == 0)
{
uint8_t x_233; lean_object* x_234; uint64_t x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_2);
x_233 = 1;
x_234 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_234, 0, x_50);
lean_ctor_set_uint8(x_234, 1, x_51);
lean_ctor_set_uint8(x_234, 2, x_52);
lean_ctor_set_uint8(x_234, 3, x_53);
lean_ctor_set_uint8(x_234, 4, x_54);
lean_ctor_set_uint8(x_234, 5, x_55);
lean_ctor_set_uint8(x_234, 6, x_56);
lean_ctor_set_uint8(x_234, 7, x_57);
lean_ctor_set_uint8(x_234, 8, x_58);
lean_ctor_set_uint8(x_234, 9, x_62);
lean_ctor_set_uint8(x_234, 10, x_60);
lean_ctor_set_uint8(x_234, 11, x_61);
lean_ctor_set_uint8(x_234, 12, x_233);
lean_ctor_set_uint8(x_234, 13, x_233);
lean_ctor_set_uint8(x_234, 14, x_231);
lean_ctor_set_uint8(x_234, 15, x_233);
lean_ctor_set_uint8(x_234, 16, x_233);
x_235 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_234);
x_236 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_42);
lean_ctor_set(x_236, 2, x_43);
lean_ctor_set(x_236, 3, x_44);
lean_ctor_set(x_236, 4, x_45);
lean_ctor_set(x_236, 5, x_46);
lean_ctor_set(x_236, 6, x_47);
lean_ctor_set_uint64(x_236, sizeof(void*)*7, x_235);
lean_ctor_set_uint8(x_236, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_236, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_236, sizeof(void*)*7 + 10, x_49);
x_237 = l_Lean_Meta_inferTypeImp_infer(x_1, x_236, x_3, x_4, x_5, x_229);
if (lean_obj_tag(x_237) == 0)
{
uint8_t x_238; 
x_238 = !lean_is_exclusive(x_237);
if (x_238 == 0)
{
return x_237;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_237, 0);
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_237);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
else
{
uint8_t x_242; 
x_242 = !lean_is_exclusive(x_237);
if (x_242 == 0)
{
return x_237;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_237, 0);
x_244 = lean_ctor_get(x_237, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_237);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
else
{
lean_object* x_246; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_246 = l_Lean_Meta_inferTypeImp_infer(x_1, x_2, x_3, x_4, x_5, x_229);
if (lean_obj_tag(x_246) == 0)
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_246);
if (x_247 == 0)
{
return x_246;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_246, 0);
x_249 = lean_ctor_get(x_246, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_246);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
else
{
uint8_t x_251; 
x_251 = !lean_is_exclusive(x_246);
if (x_251 == 0)
{
return x_246;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_246, 0);
x_253 = lean_ctor_get(x_246, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_246);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
}
}
}
}
}
}
else
{
uint64_t x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; uint8_t x_264; uint8_t x_265; uint8_t x_266; uint8_t x_267; uint8_t x_268; uint8_t x_269; uint8_t x_270; uint8_t x_271; uint8_t x_272; uint8_t x_273; uint8_t x_274; uint8_t x_275; uint8_t x_276; uint8_t x_277; uint8_t x_278; uint8_t x_279; uint8_t x_280; uint8_t x_281; uint8_t x_282; uint8_t x_283; uint64_t x_284; uint64_t x_285; uint64_t x_286; 
x_255 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_256 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_257 = lean_ctor_get(x_2, 1);
x_258 = lean_ctor_get(x_2, 2);
x_259 = lean_ctor_get(x_2, 3);
x_260 = lean_ctor_get(x_2, 4);
x_261 = lean_ctor_get(x_2, 5);
x_262 = lean_ctor_get(x_2, 6);
x_263 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_264 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
x_265 = lean_ctor_get_uint8(x_38, 0);
x_266 = lean_ctor_get_uint8(x_38, 1);
x_267 = lean_ctor_get_uint8(x_38, 2);
x_268 = lean_ctor_get_uint8(x_38, 3);
x_269 = lean_ctor_get_uint8(x_38, 4);
x_270 = lean_ctor_get_uint8(x_38, 5);
x_271 = lean_ctor_get_uint8(x_38, 6);
x_272 = lean_ctor_get_uint8(x_38, 7);
x_273 = lean_ctor_get_uint8(x_38, 8);
x_274 = lean_ctor_get_uint8(x_38, 9);
x_275 = lean_ctor_get_uint8(x_38, 10);
x_276 = lean_ctor_get_uint8(x_38, 11);
x_277 = lean_ctor_get_uint8(x_38, 12);
x_278 = lean_ctor_get_uint8(x_38, 13);
x_279 = lean_ctor_get_uint8(x_38, 14);
x_280 = lean_ctor_get_uint8(x_38, 15);
x_281 = lean_ctor_get_uint8(x_38, 16);
lean_dec(x_38);
x_282 = 1;
x_283 = l_Lean_Meta_TransparencyMode_lt(x_274, x_282);
x_284 = 2;
x_285 = lean_uint64_shift_right(x_255, x_284);
x_286 = lean_uint64_shift_left(x_285, x_284);
if (x_283 == 0)
{
lean_object* x_287; uint64_t x_288; uint64_t x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_287 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_287, 0, x_265);
lean_ctor_set_uint8(x_287, 1, x_266);
lean_ctor_set_uint8(x_287, 2, x_267);
lean_ctor_set_uint8(x_287, 3, x_268);
lean_ctor_set_uint8(x_287, 4, x_269);
lean_ctor_set_uint8(x_287, 5, x_270);
lean_ctor_set_uint8(x_287, 6, x_271);
lean_ctor_set_uint8(x_287, 7, x_272);
lean_ctor_set_uint8(x_287, 8, x_273);
lean_ctor_set_uint8(x_287, 9, x_274);
lean_ctor_set_uint8(x_287, 10, x_275);
lean_ctor_set_uint8(x_287, 11, x_276);
lean_ctor_set_uint8(x_287, 12, x_277);
lean_ctor_set_uint8(x_287, 13, x_278);
lean_ctor_set_uint8(x_287, 14, x_279);
lean_ctor_set_uint8(x_287, 15, x_280);
lean_ctor_set_uint8(x_287, 16, x_281);
x_288 = l_Lean_Meta_TransparencyMode_toUInt64(x_274);
x_289 = lean_uint64_lor(x_286, x_288);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_ctor_set(x_2, 0, x_287);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_289);
x_290 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get_uint8(x_291, 13);
if (x_292 == 0)
{
lean_object* x_293; uint8_t x_294; uint8_t x_295; lean_object* x_296; uint64_t x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_291);
lean_dec(x_2);
x_293 = lean_ctor_get(x_290, 1);
lean_inc(x_293);
lean_dec(x_290);
x_294 = 1;
x_295 = 2;
x_296 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_296, 0, x_265);
lean_ctor_set_uint8(x_296, 1, x_266);
lean_ctor_set_uint8(x_296, 2, x_267);
lean_ctor_set_uint8(x_296, 3, x_268);
lean_ctor_set_uint8(x_296, 4, x_269);
lean_ctor_set_uint8(x_296, 5, x_270);
lean_ctor_set_uint8(x_296, 6, x_271);
lean_ctor_set_uint8(x_296, 7, x_272);
lean_ctor_set_uint8(x_296, 8, x_273);
lean_ctor_set_uint8(x_296, 9, x_274);
lean_ctor_set_uint8(x_296, 10, x_275);
lean_ctor_set_uint8(x_296, 11, x_276);
lean_ctor_set_uint8(x_296, 12, x_294);
lean_ctor_set_uint8(x_296, 13, x_294);
lean_ctor_set_uint8(x_296, 14, x_295);
lean_ctor_set_uint8(x_296, 15, x_294);
lean_ctor_set_uint8(x_296, 16, x_294);
x_297 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_296);
x_298 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_257);
lean_ctor_set(x_298, 2, x_258);
lean_ctor_set(x_298, 3, x_259);
lean_ctor_set(x_298, 4, x_260);
lean_ctor_set(x_298, 5, x_261);
lean_ctor_set(x_298, 6, x_262);
lean_ctor_set_uint64(x_298, sizeof(void*)*7, x_297);
lean_ctor_set_uint8(x_298, sizeof(void*)*7 + 8, x_256);
lean_ctor_set_uint8(x_298, sizeof(void*)*7 + 9, x_263);
lean_ctor_set_uint8(x_298, sizeof(void*)*7 + 10, x_264);
x_299 = l_Lean_Meta_inferTypeImp_infer(x_1, x_298, x_3, x_4, x_5, x_293);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_302 = x_299;
} else {
 lean_dec_ref(x_299);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_301);
return x_303;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_304 = lean_ctor_get(x_299, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_299, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_306 = x_299;
} else {
 lean_dec_ref(x_299);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 2, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_304);
lean_ctor_set(x_307, 1, x_305);
return x_307;
}
}
else
{
uint8_t x_308; 
x_308 = lean_ctor_get_uint8(x_291, 12);
if (x_308 == 0)
{
lean_object* x_309; uint8_t x_310; uint8_t x_311; lean_object* x_312; uint64_t x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_291);
lean_dec(x_2);
x_309 = lean_ctor_get(x_290, 1);
lean_inc(x_309);
lean_dec(x_290);
x_310 = 1;
x_311 = 2;
x_312 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_312, 0, x_265);
lean_ctor_set_uint8(x_312, 1, x_266);
lean_ctor_set_uint8(x_312, 2, x_267);
lean_ctor_set_uint8(x_312, 3, x_268);
lean_ctor_set_uint8(x_312, 4, x_269);
lean_ctor_set_uint8(x_312, 5, x_270);
lean_ctor_set_uint8(x_312, 6, x_271);
lean_ctor_set_uint8(x_312, 7, x_272);
lean_ctor_set_uint8(x_312, 8, x_273);
lean_ctor_set_uint8(x_312, 9, x_274);
lean_ctor_set_uint8(x_312, 10, x_275);
lean_ctor_set_uint8(x_312, 11, x_276);
lean_ctor_set_uint8(x_312, 12, x_310);
lean_ctor_set_uint8(x_312, 13, x_310);
lean_ctor_set_uint8(x_312, 14, x_311);
lean_ctor_set_uint8(x_312, 15, x_310);
lean_ctor_set_uint8(x_312, 16, x_310);
x_313 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_312);
x_314 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_257);
lean_ctor_set(x_314, 2, x_258);
lean_ctor_set(x_314, 3, x_259);
lean_ctor_set(x_314, 4, x_260);
lean_ctor_set(x_314, 5, x_261);
lean_ctor_set(x_314, 6, x_262);
lean_ctor_set_uint64(x_314, sizeof(void*)*7, x_313);
lean_ctor_set_uint8(x_314, sizeof(void*)*7 + 8, x_256);
lean_ctor_set_uint8(x_314, sizeof(void*)*7 + 9, x_263);
lean_ctor_set_uint8(x_314, sizeof(void*)*7 + 10, x_264);
x_315 = l_Lean_Meta_inferTypeImp_infer(x_1, x_314, x_3, x_4, x_5, x_309);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_318 = x_315;
} else {
 lean_dec_ref(x_315);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_316);
lean_ctor_set(x_319, 1, x_317);
return x_319;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_320 = lean_ctor_get(x_315, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_315, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_322 = x_315;
} else {
 lean_dec_ref(x_315);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
return x_323;
}
}
else
{
uint8_t x_324; 
x_324 = lean_ctor_get_uint8(x_291, 15);
if (x_324 == 0)
{
lean_object* x_325; uint8_t x_326; uint8_t x_327; lean_object* x_328; uint64_t x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_291);
lean_dec(x_2);
x_325 = lean_ctor_get(x_290, 1);
lean_inc(x_325);
lean_dec(x_290);
x_326 = 1;
x_327 = 2;
x_328 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_328, 0, x_265);
lean_ctor_set_uint8(x_328, 1, x_266);
lean_ctor_set_uint8(x_328, 2, x_267);
lean_ctor_set_uint8(x_328, 3, x_268);
lean_ctor_set_uint8(x_328, 4, x_269);
lean_ctor_set_uint8(x_328, 5, x_270);
lean_ctor_set_uint8(x_328, 6, x_271);
lean_ctor_set_uint8(x_328, 7, x_272);
lean_ctor_set_uint8(x_328, 8, x_273);
lean_ctor_set_uint8(x_328, 9, x_274);
lean_ctor_set_uint8(x_328, 10, x_275);
lean_ctor_set_uint8(x_328, 11, x_276);
lean_ctor_set_uint8(x_328, 12, x_326);
lean_ctor_set_uint8(x_328, 13, x_326);
lean_ctor_set_uint8(x_328, 14, x_327);
lean_ctor_set_uint8(x_328, 15, x_326);
lean_ctor_set_uint8(x_328, 16, x_326);
x_329 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_328);
x_330 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_257);
lean_ctor_set(x_330, 2, x_258);
lean_ctor_set(x_330, 3, x_259);
lean_ctor_set(x_330, 4, x_260);
lean_ctor_set(x_330, 5, x_261);
lean_ctor_set(x_330, 6, x_262);
lean_ctor_set_uint64(x_330, sizeof(void*)*7, x_329);
lean_ctor_set_uint8(x_330, sizeof(void*)*7 + 8, x_256);
lean_ctor_set_uint8(x_330, sizeof(void*)*7 + 9, x_263);
lean_ctor_set_uint8(x_330, sizeof(void*)*7 + 10, x_264);
x_331 = l_Lean_Meta_inferTypeImp_infer(x_1, x_330, x_3, x_4, x_5, x_325);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_334 = x_331;
} else {
 lean_dec_ref(x_331);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_332);
lean_ctor_set(x_335, 1, x_333);
return x_335;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_336 = lean_ctor_get(x_331, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_331, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_338 = x_331;
} else {
 lean_dec_ref(x_331);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(1, 2, 0);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_336);
lean_ctor_set(x_339, 1, x_337);
return x_339;
}
}
else
{
uint8_t x_340; 
x_340 = lean_ctor_get_uint8(x_291, 16);
if (x_340 == 0)
{
lean_object* x_341; uint8_t x_342; uint8_t x_343; lean_object* x_344; uint64_t x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_291);
lean_dec(x_2);
x_341 = lean_ctor_get(x_290, 1);
lean_inc(x_341);
lean_dec(x_290);
x_342 = 1;
x_343 = 2;
x_344 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_344, 0, x_265);
lean_ctor_set_uint8(x_344, 1, x_266);
lean_ctor_set_uint8(x_344, 2, x_267);
lean_ctor_set_uint8(x_344, 3, x_268);
lean_ctor_set_uint8(x_344, 4, x_269);
lean_ctor_set_uint8(x_344, 5, x_270);
lean_ctor_set_uint8(x_344, 6, x_271);
lean_ctor_set_uint8(x_344, 7, x_272);
lean_ctor_set_uint8(x_344, 8, x_273);
lean_ctor_set_uint8(x_344, 9, x_274);
lean_ctor_set_uint8(x_344, 10, x_275);
lean_ctor_set_uint8(x_344, 11, x_276);
lean_ctor_set_uint8(x_344, 12, x_342);
lean_ctor_set_uint8(x_344, 13, x_342);
lean_ctor_set_uint8(x_344, 14, x_343);
lean_ctor_set_uint8(x_344, 15, x_342);
lean_ctor_set_uint8(x_344, 16, x_342);
x_345 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_344);
x_346 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_257);
lean_ctor_set(x_346, 2, x_258);
lean_ctor_set(x_346, 3, x_259);
lean_ctor_set(x_346, 4, x_260);
lean_ctor_set(x_346, 5, x_261);
lean_ctor_set(x_346, 6, x_262);
lean_ctor_set_uint64(x_346, sizeof(void*)*7, x_345);
lean_ctor_set_uint8(x_346, sizeof(void*)*7 + 8, x_256);
lean_ctor_set_uint8(x_346, sizeof(void*)*7 + 9, x_263);
lean_ctor_set_uint8(x_346, sizeof(void*)*7 + 10, x_264);
x_347 = l_Lean_Meta_inferTypeImp_infer(x_1, x_346, x_3, x_4, x_5, x_341);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_347, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_350 = x_347;
} else {
 lean_dec_ref(x_347);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_348);
lean_ctor_set(x_351, 1, x_349);
return x_351;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_352 = lean_ctor_get(x_347, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_347, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_354 = x_347;
} else {
 lean_dec_ref(x_347);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(1, 2, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_352);
lean_ctor_set(x_355, 1, x_353);
return x_355;
}
}
else
{
lean_object* x_356; uint8_t x_357; uint8_t x_358; uint8_t x_359; 
x_356 = lean_ctor_get(x_290, 1);
lean_inc(x_356);
lean_dec(x_290);
x_357 = lean_ctor_get_uint8(x_291, 14);
lean_dec(x_291);
x_358 = 2;
x_359 = l_Lean_Meta_instDecidableEqProjReductionKind(x_357, x_358);
if (x_359 == 0)
{
uint8_t x_360; lean_object* x_361; uint64_t x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_2);
x_360 = 1;
x_361 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_361, 0, x_265);
lean_ctor_set_uint8(x_361, 1, x_266);
lean_ctor_set_uint8(x_361, 2, x_267);
lean_ctor_set_uint8(x_361, 3, x_268);
lean_ctor_set_uint8(x_361, 4, x_269);
lean_ctor_set_uint8(x_361, 5, x_270);
lean_ctor_set_uint8(x_361, 6, x_271);
lean_ctor_set_uint8(x_361, 7, x_272);
lean_ctor_set_uint8(x_361, 8, x_273);
lean_ctor_set_uint8(x_361, 9, x_274);
lean_ctor_set_uint8(x_361, 10, x_275);
lean_ctor_set_uint8(x_361, 11, x_276);
lean_ctor_set_uint8(x_361, 12, x_360);
lean_ctor_set_uint8(x_361, 13, x_360);
lean_ctor_set_uint8(x_361, 14, x_358);
lean_ctor_set_uint8(x_361, 15, x_360);
lean_ctor_set_uint8(x_361, 16, x_360);
x_362 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_361);
x_363 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_257);
lean_ctor_set(x_363, 2, x_258);
lean_ctor_set(x_363, 3, x_259);
lean_ctor_set(x_363, 4, x_260);
lean_ctor_set(x_363, 5, x_261);
lean_ctor_set(x_363, 6, x_262);
lean_ctor_set_uint64(x_363, sizeof(void*)*7, x_362);
lean_ctor_set_uint8(x_363, sizeof(void*)*7 + 8, x_256);
lean_ctor_set_uint8(x_363, sizeof(void*)*7 + 9, x_263);
lean_ctor_set_uint8(x_363, sizeof(void*)*7 + 10, x_264);
x_364 = l_Lean_Meta_inferTypeImp_infer(x_1, x_363, x_3, x_4, x_5, x_356);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_367 = x_364;
} else {
 lean_dec_ref(x_364);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_365);
lean_ctor_set(x_368, 1, x_366);
return x_368;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_369 = lean_ctor_get(x_364, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_364, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_371 = x_364;
} else {
 lean_dec_ref(x_364);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(1, 2, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_369);
lean_ctor_set(x_372, 1, x_370);
return x_372;
}
}
else
{
lean_object* x_373; 
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
x_373 = l_Lean_Meta_inferTypeImp_infer(x_1, x_2, x_3, x_4, x_5, x_356);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_376 = x_373;
} else {
 lean_dec_ref(x_373);
 x_376 = lean_box(0);
}
if (lean_is_scalar(x_376)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_376;
}
lean_ctor_set(x_377, 0, x_374);
lean_ctor_set(x_377, 1, x_375);
return x_377;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_378 = lean_ctor_get(x_373, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_373, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_380 = x_373;
} else {
 lean_dec_ref(x_373);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_378);
lean_ctor_set(x_381, 1, x_379);
return x_381;
}
}
}
}
}
}
}
else
{
lean_object* x_382; uint64_t x_383; uint64_t x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; 
x_382 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_382, 0, x_265);
lean_ctor_set_uint8(x_382, 1, x_266);
lean_ctor_set_uint8(x_382, 2, x_267);
lean_ctor_set_uint8(x_382, 3, x_268);
lean_ctor_set_uint8(x_382, 4, x_269);
lean_ctor_set_uint8(x_382, 5, x_270);
lean_ctor_set_uint8(x_382, 6, x_271);
lean_ctor_set_uint8(x_382, 7, x_272);
lean_ctor_set_uint8(x_382, 8, x_273);
lean_ctor_set_uint8(x_382, 9, x_282);
lean_ctor_set_uint8(x_382, 10, x_275);
lean_ctor_set_uint8(x_382, 11, x_276);
lean_ctor_set_uint8(x_382, 12, x_277);
lean_ctor_set_uint8(x_382, 13, x_278);
lean_ctor_set_uint8(x_382, 14, x_279);
lean_ctor_set_uint8(x_382, 15, x_280);
lean_ctor_set_uint8(x_382, 16, x_281);
x_383 = l_Lean_Meta_withInferTypeConfig___rarg___closed__1;
x_384 = lean_uint64_lor(x_286, x_383);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_ctor_set(x_2, 0, x_382);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_384);
x_385 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
x_387 = lean_ctor_get_uint8(x_386, 13);
if (x_387 == 0)
{
lean_object* x_388; uint8_t x_389; uint8_t x_390; lean_object* x_391; uint64_t x_392; lean_object* x_393; lean_object* x_394; 
lean_dec(x_386);
lean_dec(x_2);
x_388 = lean_ctor_get(x_385, 1);
lean_inc(x_388);
lean_dec(x_385);
x_389 = 1;
x_390 = 2;
x_391 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_391, 0, x_265);
lean_ctor_set_uint8(x_391, 1, x_266);
lean_ctor_set_uint8(x_391, 2, x_267);
lean_ctor_set_uint8(x_391, 3, x_268);
lean_ctor_set_uint8(x_391, 4, x_269);
lean_ctor_set_uint8(x_391, 5, x_270);
lean_ctor_set_uint8(x_391, 6, x_271);
lean_ctor_set_uint8(x_391, 7, x_272);
lean_ctor_set_uint8(x_391, 8, x_273);
lean_ctor_set_uint8(x_391, 9, x_282);
lean_ctor_set_uint8(x_391, 10, x_275);
lean_ctor_set_uint8(x_391, 11, x_276);
lean_ctor_set_uint8(x_391, 12, x_389);
lean_ctor_set_uint8(x_391, 13, x_389);
lean_ctor_set_uint8(x_391, 14, x_390);
lean_ctor_set_uint8(x_391, 15, x_389);
lean_ctor_set_uint8(x_391, 16, x_389);
x_392 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_391);
x_393 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_257);
lean_ctor_set(x_393, 2, x_258);
lean_ctor_set(x_393, 3, x_259);
lean_ctor_set(x_393, 4, x_260);
lean_ctor_set(x_393, 5, x_261);
lean_ctor_set(x_393, 6, x_262);
lean_ctor_set_uint64(x_393, sizeof(void*)*7, x_392);
lean_ctor_set_uint8(x_393, sizeof(void*)*7 + 8, x_256);
lean_ctor_set_uint8(x_393, sizeof(void*)*7 + 9, x_263);
lean_ctor_set_uint8(x_393, sizeof(void*)*7 + 10, x_264);
x_394 = l_Lean_Meta_inferTypeImp_infer(x_1, x_393, x_3, x_4, x_5, x_388);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_397 = x_394;
} else {
 lean_dec_ref(x_394);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_396);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_399 = lean_ctor_get(x_394, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_394, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_401 = x_394;
} else {
 lean_dec_ref(x_394);
 x_401 = lean_box(0);
}
if (lean_is_scalar(x_401)) {
 x_402 = lean_alloc_ctor(1, 2, 0);
} else {
 x_402 = x_401;
}
lean_ctor_set(x_402, 0, x_399);
lean_ctor_set(x_402, 1, x_400);
return x_402;
}
}
else
{
uint8_t x_403; 
x_403 = lean_ctor_get_uint8(x_386, 12);
if (x_403 == 0)
{
lean_object* x_404; uint8_t x_405; uint8_t x_406; lean_object* x_407; uint64_t x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_386);
lean_dec(x_2);
x_404 = lean_ctor_get(x_385, 1);
lean_inc(x_404);
lean_dec(x_385);
x_405 = 1;
x_406 = 2;
x_407 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_407, 0, x_265);
lean_ctor_set_uint8(x_407, 1, x_266);
lean_ctor_set_uint8(x_407, 2, x_267);
lean_ctor_set_uint8(x_407, 3, x_268);
lean_ctor_set_uint8(x_407, 4, x_269);
lean_ctor_set_uint8(x_407, 5, x_270);
lean_ctor_set_uint8(x_407, 6, x_271);
lean_ctor_set_uint8(x_407, 7, x_272);
lean_ctor_set_uint8(x_407, 8, x_273);
lean_ctor_set_uint8(x_407, 9, x_282);
lean_ctor_set_uint8(x_407, 10, x_275);
lean_ctor_set_uint8(x_407, 11, x_276);
lean_ctor_set_uint8(x_407, 12, x_405);
lean_ctor_set_uint8(x_407, 13, x_405);
lean_ctor_set_uint8(x_407, 14, x_406);
lean_ctor_set_uint8(x_407, 15, x_405);
lean_ctor_set_uint8(x_407, 16, x_405);
x_408 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_407);
x_409 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_257);
lean_ctor_set(x_409, 2, x_258);
lean_ctor_set(x_409, 3, x_259);
lean_ctor_set(x_409, 4, x_260);
lean_ctor_set(x_409, 5, x_261);
lean_ctor_set(x_409, 6, x_262);
lean_ctor_set_uint64(x_409, sizeof(void*)*7, x_408);
lean_ctor_set_uint8(x_409, sizeof(void*)*7 + 8, x_256);
lean_ctor_set_uint8(x_409, sizeof(void*)*7 + 9, x_263);
lean_ctor_set_uint8(x_409, sizeof(void*)*7 + 10, x_264);
x_410 = l_Lean_Meta_inferTypeImp_infer(x_1, x_409, x_3, x_4, x_5, x_404);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_413 = x_410;
} else {
 lean_dec_ref(x_410);
 x_413 = lean_box(0);
}
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(0, 2, 0);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_411);
lean_ctor_set(x_414, 1, x_412);
return x_414;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_415 = lean_ctor_get(x_410, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_410, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_417 = x_410;
} else {
 lean_dec_ref(x_410);
 x_417 = lean_box(0);
}
if (lean_is_scalar(x_417)) {
 x_418 = lean_alloc_ctor(1, 2, 0);
} else {
 x_418 = x_417;
}
lean_ctor_set(x_418, 0, x_415);
lean_ctor_set(x_418, 1, x_416);
return x_418;
}
}
else
{
uint8_t x_419; 
x_419 = lean_ctor_get_uint8(x_386, 15);
if (x_419 == 0)
{
lean_object* x_420; uint8_t x_421; uint8_t x_422; lean_object* x_423; uint64_t x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_386);
lean_dec(x_2);
x_420 = lean_ctor_get(x_385, 1);
lean_inc(x_420);
lean_dec(x_385);
x_421 = 1;
x_422 = 2;
x_423 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_423, 0, x_265);
lean_ctor_set_uint8(x_423, 1, x_266);
lean_ctor_set_uint8(x_423, 2, x_267);
lean_ctor_set_uint8(x_423, 3, x_268);
lean_ctor_set_uint8(x_423, 4, x_269);
lean_ctor_set_uint8(x_423, 5, x_270);
lean_ctor_set_uint8(x_423, 6, x_271);
lean_ctor_set_uint8(x_423, 7, x_272);
lean_ctor_set_uint8(x_423, 8, x_273);
lean_ctor_set_uint8(x_423, 9, x_282);
lean_ctor_set_uint8(x_423, 10, x_275);
lean_ctor_set_uint8(x_423, 11, x_276);
lean_ctor_set_uint8(x_423, 12, x_421);
lean_ctor_set_uint8(x_423, 13, x_421);
lean_ctor_set_uint8(x_423, 14, x_422);
lean_ctor_set_uint8(x_423, 15, x_421);
lean_ctor_set_uint8(x_423, 16, x_421);
x_424 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_423);
x_425 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_257);
lean_ctor_set(x_425, 2, x_258);
lean_ctor_set(x_425, 3, x_259);
lean_ctor_set(x_425, 4, x_260);
lean_ctor_set(x_425, 5, x_261);
lean_ctor_set(x_425, 6, x_262);
lean_ctor_set_uint64(x_425, sizeof(void*)*7, x_424);
lean_ctor_set_uint8(x_425, sizeof(void*)*7 + 8, x_256);
lean_ctor_set_uint8(x_425, sizeof(void*)*7 + 9, x_263);
lean_ctor_set_uint8(x_425, sizeof(void*)*7 + 10, x_264);
x_426 = l_Lean_Meta_inferTypeImp_infer(x_1, x_425, x_3, x_4, x_5, x_420);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 x_429 = x_426;
} else {
 lean_dec_ref(x_426);
 x_429 = lean_box(0);
}
if (lean_is_scalar(x_429)) {
 x_430 = lean_alloc_ctor(0, 2, 0);
} else {
 x_430 = x_429;
}
lean_ctor_set(x_430, 0, x_427);
lean_ctor_set(x_430, 1, x_428);
return x_430;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_431 = lean_ctor_get(x_426, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_426, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 x_433 = x_426;
} else {
 lean_dec_ref(x_426);
 x_433 = lean_box(0);
}
if (lean_is_scalar(x_433)) {
 x_434 = lean_alloc_ctor(1, 2, 0);
} else {
 x_434 = x_433;
}
lean_ctor_set(x_434, 0, x_431);
lean_ctor_set(x_434, 1, x_432);
return x_434;
}
}
else
{
uint8_t x_435; 
x_435 = lean_ctor_get_uint8(x_386, 16);
if (x_435 == 0)
{
lean_object* x_436; uint8_t x_437; uint8_t x_438; lean_object* x_439; uint64_t x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_386);
lean_dec(x_2);
x_436 = lean_ctor_get(x_385, 1);
lean_inc(x_436);
lean_dec(x_385);
x_437 = 1;
x_438 = 2;
x_439 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_439, 0, x_265);
lean_ctor_set_uint8(x_439, 1, x_266);
lean_ctor_set_uint8(x_439, 2, x_267);
lean_ctor_set_uint8(x_439, 3, x_268);
lean_ctor_set_uint8(x_439, 4, x_269);
lean_ctor_set_uint8(x_439, 5, x_270);
lean_ctor_set_uint8(x_439, 6, x_271);
lean_ctor_set_uint8(x_439, 7, x_272);
lean_ctor_set_uint8(x_439, 8, x_273);
lean_ctor_set_uint8(x_439, 9, x_282);
lean_ctor_set_uint8(x_439, 10, x_275);
lean_ctor_set_uint8(x_439, 11, x_276);
lean_ctor_set_uint8(x_439, 12, x_437);
lean_ctor_set_uint8(x_439, 13, x_437);
lean_ctor_set_uint8(x_439, 14, x_438);
lean_ctor_set_uint8(x_439, 15, x_437);
lean_ctor_set_uint8(x_439, 16, x_437);
x_440 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_439);
x_441 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_257);
lean_ctor_set(x_441, 2, x_258);
lean_ctor_set(x_441, 3, x_259);
lean_ctor_set(x_441, 4, x_260);
lean_ctor_set(x_441, 5, x_261);
lean_ctor_set(x_441, 6, x_262);
lean_ctor_set_uint64(x_441, sizeof(void*)*7, x_440);
lean_ctor_set_uint8(x_441, sizeof(void*)*7 + 8, x_256);
lean_ctor_set_uint8(x_441, sizeof(void*)*7 + 9, x_263);
lean_ctor_set_uint8(x_441, sizeof(void*)*7 + 10, x_264);
x_442 = l_Lean_Meta_inferTypeImp_infer(x_1, x_441, x_3, x_4, x_5, x_436);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_445 = x_442;
} else {
 lean_dec_ref(x_442);
 x_445 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_446 = lean_alloc_ctor(0, 2, 0);
} else {
 x_446 = x_445;
}
lean_ctor_set(x_446, 0, x_443);
lean_ctor_set(x_446, 1, x_444);
return x_446;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_447 = lean_ctor_get(x_442, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_442, 1);
lean_inc(x_448);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_449 = x_442;
} else {
 lean_dec_ref(x_442);
 x_449 = lean_box(0);
}
if (lean_is_scalar(x_449)) {
 x_450 = lean_alloc_ctor(1, 2, 0);
} else {
 x_450 = x_449;
}
lean_ctor_set(x_450, 0, x_447);
lean_ctor_set(x_450, 1, x_448);
return x_450;
}
}
else
{
lean_object* x_451; uint8_t x_452; uint8_t x_453; uint8_t x_454; 
x_451 = lean_ctor_get(x_385, 1);
lean_inc(x_451);
lean_dec(x_385);
x_452 = lean_ctor_get_uint8(x_386, 14);
lean_dec(x_386);
x_453 = 2;
x_454 = l_Lean_Meta_instDecidableEqProjReductionKind(x_452, x_453);
if (x_454 == 0)
{
uint8_t x_455; lean_object* x_456; uint64_t x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_2);
x_455 = 1;
x_456 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_456, 0, x_265);
lean_ctor_set_uint8(x_456, 1, x_266);
lean_ctor_set_uint8(x_456, 2, x_267);
lean_ctor_set_uint8(x_456, 3, x_268);
lean_ctor_set_uint8(x_456, 4, x_269);
lean_ctor_set_uint8(x_456, 5, x_270);
lean_ctor_set_uint8(x_456, 6, x_271);
lean_ctor_set_uint8(x_456, 7, x_272);
lean_ctor_set_uint8(x_456, 8, x_273);
lean_ctor_set_uint8(x_456, 9, x_282);
lean_ctor_set_uint8(x_456, 10, x_275);
lean_ctor_set_uint8(x_456, 11, x_276);
lean_ctor_set_uint8(x_456, 12, x_455);
lean_ctor_set_uint8(x_456, 13, x_455);
lean_ctor_set_uint8(x_456, 14, x_453);
lean_ctor_set_uint8(x_456, 15, x_455);
lean_ctor_set_uint8(x_456, 16, x_455);
x_457 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_456);
x_458 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_257);
lean_ctor_set(x_458, 2, x_258);
lean_ctor_set(x_458, 3, x_259);
lean_ctor_set(x_458, 4, x_260);
lean_ctor_set(x_458, 5, x_261);
lean_ctor_set(x_458, 6, x_262);
lean_ctor_set_uint64(x_458, sizeof(void*)*7, x_457);
lean_ctor_set_uint8(x_458, sizeof(void*)*7 + 8, x_256);
lean_ctor_set_uint8(x_458, sizeof(void*)*7 + 9, x_263);
lean_ctor_set_uint8(x_458, sizeof(void*)*7 + 10, x_264);
x_459 = l_Lean_Meta_inferTypeImp_infer(x_1, x_458, x_3, x_4, x_5, x_451);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 x_462 = x_459;
} else {
 lean_dec_ref(x_459);
 x_462 = lean_box(0);
}
if (lean_is_scalar(x_462)) {
 x_463 = lean_alloc_ctor(0, 2, 0);
} else {
 x_463 = x_462;
}
lean_ctor_set(x_463, 0, x_460);
lean_ctor_set(x_463, 1, x_461);
return x_463;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_464 = lean_ctor_get(x_459, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_459, 1);
lean_inc(x_465);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 x_466 = x_459;
} else {
 lean_dec_ref(x_459);
 x_466 = lean_box(0);
}
if (lean_is_scalar(x_466)) {
 x_467 = lean_alloc_ctor(1, 2, 0);
} else {
 x_467 = x_466;
}
lean_ctor_set(x_467, 0, x_464);
lean_ctor_set(x_467, 1, x_465);
return x_467;
}
}
else
{
lean_object* x_468; 
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
x_468 = l_Lean_Meta_inferTypeImp_infer(x_1, x_2, x_3, x_4, x_5, x_451);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_468, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 x_471 = x_468;
} else {
 lean_dec_ref(x_468);
 x_471 = lean_box(0);
}
if (lean_is_scalar(x_471)) {
 x_472 = lean_alloc_ctor(0, 2, 0);
} else {
 x_472 = x_471;
}
lean_ctor_set(x_472, 0, x_469);
lean_ctor_set(x_472, 1, x_470);
return x_472;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_473 = lean_ctor_get(x_468, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_468, 1);
lean_inc(x_474);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 x_475 = x_468;
} else {
 lean_dec_ref(x_468);
 x_475 = lean_box(0);
}
if (lean_is_scalar(x_475)) {
 x_476 = lean_alloc_ctor(1, 2, 0);
} else {
 x_476 = x_475;
}
lean_ctor_set(x_476, 0, x_473);
lean_ctor_set(x_476, 1, x_474);
return x_476;
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_477; uint64_t x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; uint8_t x_487; uint8_t x_488; uint8_t x_489; uint8_t x_490; uint8_t x_491; uint8_t x_492; uint8_t x_493; uint8_t x_494; uint8_t x_495; uint8_t x_496; uint8_t x_497; uint8_t x_498; uint8_t x_499; uint8_t x_500; uint8_t x_501; uint8_t x_502; uint8_t x_503; uint8_t x_504; lean_object* x_505; uint8_t x_506; uint8_t x_507; uint64_t x_508; uint64_t x_509; uint64_t x_510; 
x_477 = lean_ctor_get(x_2, 0);
x_478 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_479 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_480 = lean_ctor_get(x_2, 1);
x_481 = lean_ctor_get(x_2, 2);
x_482 = lean_ctor_get(x_2, 3);
x_483 = lean_ctor_get(x_2, 4);
x_484 = lean_ctor_get(x_2, 5);
x_485 = lean_ctor_get(x_2, 6);
x_486 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_487 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_inc(x_482);
lean_inc(x_481);
lean_inc(x_480);
lean_inc(x_477);
lean_dec(x_2);
x_488 = lean_ctor_get_uint8(x_477, 0);
x_489 = lean_ctor_get_uint8(x_477, 1);
x_490 = lean_ctor_get_uint8(x_477, 2);
x_491 = lean_ctor_get_uint8(x_477, 3);
x_492 = lean_ctor_get_uint8(x_477, 4);
x_493 = lean_ctor_get_uint8(x_477, 5);
x_494 = lean_ctor_get_uint8(x_477, 6);
x_495 = lean_ctor_get_uint8(x_477, 7);
x_496 = lean_ctor_get_uint8(x_477, 8);
x_497 = lean_ctor_get_uint8(x_477, 9);
x_498 = lean_ctor_get_uint8(x_477, 10);
x_499 = lean_ctor_get_uint8(x_477, 11);
x_500 = lean_ctor_get_uint8(x_477, 12);
x_501 = lean_ctor_get_uint8(x_477, 13);
x_502 = lean_ctor_get_uint8(x_477, 14);
x_503 = lean_ctor_get_uint8(x_477, 15);
x_504 = lean_ctor_get_uint8(x_477, 16);
if (lean_is_exclusive(x_477)) {
 x_505 = x_477;
} else {
 lean_dec_ref(x_477);
 x_505 = lean_box(0);
}
x_506 = 1;
x_507 = l_Lean_Meta_TransparencyMode_lt(x_497, x_506);
x_508 = 2;
x_509 = lean_uint64_shift_right(x_478, x_508);
x_510 = lean_uint64_shift_left(x_509, x_508);
if (x_507 == 0)
{
lean_object* x_511; uint64_t x_512; uint64_t x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_517; 
if (lean_is_scalar(x_505)) {
 x_511 = lean_alloc_ctor(0, 0, 17);
} else {
 x_511 = x_505;
}
lean_ctor_set_uint8(x_511, 0, x_488);
lean_ctor_set_uint8(x_511, 1, x_489);
lean_ctor_set_uint8(x_511, 2, x_490);
lean_ctor_set_uint8(x_511, 3, x_491);
lean_ctor_set_uint8(x_511, 4, x_492);
lean_ctor_set_uint8(x_511, 5, x_493);
lean_ctor_set_uint8(x_511, 6, x_494);
lean_ctor_set_uint8(x_511, 7, x_495);
lean_ctor_set_uint8(x_511, 8, x_496);
lean_ctor_set_uint8(x_511, 9, x_497);
lean_ctor_set_uint8(x_511, 10, x_498);
lean_ctor_set_uint8(x_511, 11, x_499);
lean_ctor_set_uint8(x_511, 12, x_500);
lean_ctor_set_uint8(x_511, 13, x_501);
lean_ctor_set_uint8(x_511, 14, x_502);
lean_ctor_set_uint8(x_511, 15, x_503);
lean_ctor_set_uint8(x_511, 16, x_504);
x_512 = l_Lean_Meta_TransparencyMode_toUInt64(x_497);
x_513 = lean_uint64_lor(x_510, x_512);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_inc(x_482);
lean_inc(x_481);
lean_inc(x_480);
x_514 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_514, 0, x_511);
lean_ctor_set(x_514, 1, x_480);
lean_ctor_set(x_514, 2, x_481);
lean_ctor_set(x_514, 3, x_482);
lean_ctor_set(x_514, 4, x_483);
lean_ctor_set(x_514, 5, x_484);
lean_ctor_set(x_514, 6, x_485);
lean_ctor_set_uint64(x_514, sizeof(void*)*7, x_513);
lean_ctor_set_uint8(x_514, sizeof(void*)*7 + 8, x_479);
lean_ctor_set_uint8(x_514, sizeof(void*)*7 + 9, x_486);
lean_ctor_set_uint8(x_514, sizeof(void*)*7 + 10, x_487);
x_515 = l_Lean_Meta_getConfig(x_514, x_3, x_4, x_5, x_6);
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
x_517 = lean_ctor_get_uint8(x_516, 13);
if (x_517 == 0)
{
lean_object* x_518; uint8_t x_519; uint8_t x_520; lean_object* x_521; uint64_t x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_516);
lean_dec(x_514);
x_518 = lean_ctor_get(x_515, 1);
lean_inc(x_518);
lean_dec(x_515);
x_519 = 1;
x_520 = 2;
x_521 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_521, 0, x_488);
lean_ctor_set_uint8(x_521, 1, x_489);
lean_ctor_set_uint8(x_521, 2, x_490);
lean_ctor_set_uint8(x_521, 3, x_491);
lean_ctor_set_uint8(x_521, 4, x_492);
lean_ctor_set_uint8(x_521, 5, x_493);
lean_ctor_set_uint8(x_521, 6, x_494);
lean_ctor_set_uint8(x_521, 7, x_495);
lean_ctor_set_uint8(x_521, 8, x_496);
lean_ctor_set_uint8(x_521, 9, x_497);
lean_ctor_set_uint8(x_521, 10, x_498);
lean_ctor_set_uint8(x_521, 11, x_499);
lean_ctor_set_uint8(x_521, 12, x_519);
lean_ctor_set_uint8(x_521, 13, x_519);
lean_ctor_set_uint8(x_521, 14, x_520);
lean_ctor_set_uint8(x_521, 15, x_519);
lean_ctor_set_uint8(x_521, 16, x_519);
x_522 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_521);
x_523 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_523, 0, x_521);
lean_ctor_set(x_523, 1, x_480);
lean_ctor_set(x_523, 2, x_481);
lean_ctor_set(x_523, 3, x_482);
lean_ctor_set(x_523, 4, x_483);
lean_ctor_set(x_523, 5, x_484);
lean_ctor_set(x_523, 6, x_485);
lean_ctor_set_uint64(x_523, sizeof(void*)*7, x_522);
lean_ctor_set_uint8(x_523, sizeof(void*)*7 + 8, x_479);
lean_ctor_set_uint8(x_523, sizeof(void*)*7 + 9, x_486);
lean_ctor_set_uint8(x_523, sizeof(void*)*7 + 10, x_487);
x_524 = l_Lean_Meta_inferTypeImp_infer(x_1, x_523, x_3, x_4, x_5, x_518);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_524, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 x_527 = x_524;
} else {
 lean_dec_ref(x_524);
 x_527 = lean_box(0);
}
if (lean_is_scalar(x_527)) {
 x_528 = lean_alloc_ctor(0, 2, 0);
} else {
 x_528 = x_527;
}
lean_ctor_set(x_528, 0, x_525);
lean_ctor_set(x_528, 1, x_526);
return x_528;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_529 = lean_ctor_get(x_524, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_524, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 x_531 = x_524;
} else {
 lean_dec_ref(x_524);
 x_531 = lean_box(0);
}
if (lean_is_scalar(x_531)) {
 x_532 = lean_alloc_ctor(1, 2, 0);
} else {
 x_532 = x_531;
}
lean_ctor_set(x_532, 0, x_529);
lean_ctor_set(x_532, 1, x_530);
return x_532;
}
}
else
{
uint8_t x_533; 
x_533 = lean_ctor_get_uint8(x_516, 12);
if (x_533 == 0)
{
lean_object* x_534; uint8_t x_535; uint8_t x_536; lean_object* x_537; uint64_t x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_516);
lean_dec(x_514);
x_534 = lean_ctor_get(x_515, 1);
lean_inc(x_534);
lean_dec(x_515);
x_535 = 1;
x_536 = 2;
x_537 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_537, 0, x_488);
lean_ctor_set_uint8(x_537, 1, x_489);
lean_ctor_set_uint8(x_537, 2, x_490);
lean_ctor_set_uint8(x_537, 3, x_491);
lean_ctor_set_uint8(x_537, 4, x_492);
lean_ctor_set_uint8(x_537, 5, x_493);
lean_ctor_set_uint8(x_537, 6, x_494);
lean_ctor_set_uint8(x_537, 7, x_495);
lean_ctor_set_uint8(x_537, 8, x_496);
lean_ctor_set_uint8(x_537, 9, x_497);
lean_ctor_set_uint8(x_537, 10, x_498);
lean_ctor_set_uint8(x_537, 11, x_499);
lean_ctor_set_uint8(x_537, 12, x_535);
lean_ctor_set_uint8(x_537, 13, x_535);
lean_ctor_set_uint8(x_537, 14, x_536);
lean_ctor_set_uint8(x_537, 15, x_535);
lean_ctor_set_uint8(x_537, 16, x_535);
x_538 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_537);
x_539 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_539, 0, x_537);
lean_ctor_set(x_539, 1, x_480);
lean_ctor_set(x_539, 2, x_481);
lean_ctor_set(x_539, 3, x_482);
lean_ctor_set(x_539, 4, x_483);
lean_ctor_set(x_539, 5, x_484);
lean_ctor_set(x_539, 6, x_485);
lean_ctor_set_uint64(x_539, sizeof(void*)*7, x_538);
lean_ctor_set_uint8(x_539, sizeof(void*)*7 + 8, x_479);
lean_ctor_set_uint8(x_539, sizeof(void*)*7 + 9, x_486);
lean_ctor_set_uint8(x_539, sizeof(void*)*7 + 10, x_487);
x_540 = l_Lean_Meta_inferTypeImp_infer(x_1, x_539, x_3, x_4, x_5, x_534);
if (lean_obj_tag(x_540) == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_540, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 x_543 = x_540;
} else {
 lean_dec_ref(x_540);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_541);
lean_ctor_set(x_544, 1, x_542);
return x_544;
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_545 = lean_ctor_get(x_540, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_540, 1);
lean_inc(x_546);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 x_547 = x_540;
} else {
 lean_dec_ref(x_540);
 x_547 = lean_box(0);
}
if (lean_is_scalar(x_547)) {
 x_548 = lean_alloc_ctor(1, 2, 0);
} else {
 x_548 = x_547;
}
lean_ctor_set(x_548, 0, x_545);
lean_ctor_set(x_548, 1, x_546);
return x_548;
}
}
else
{
uint8_t x_549; 
x_549 = lean_ctor_get_uint8(x_516, 15);
if (x_549 == 0)
{
lean_object* x_550; uint8_t x_551; uint8_t x_552; lean_object* x_553; uint64_t x_554; lean_object* x_555; lean_object* x_556; 
lean_dec(x_516);
lean_dec(x_514);
x_550 = lean_ctor_get(x_515, 1);
lean_inc(x_550);
lean_dec(x_515);
x_551 = 1;
x_552 = 2;
x_553 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_553, 0, x_488);
lean_ctor_set_uint8(x_553, 1, x_489);
lean_ctor_set_uint8(x_553, 2, x_490);
lean_ctor_set_uint8(x_553, 3, x_491);
lean_ctor_set_uint8(x_553, 4, x_492);
lean_ctor_set_uint8(x_553, 5, x_493);
lean_ctor_set_uint8(x_553, 6, x_494);
lean_ctor_set_uint8(x_553, 7, x_495);
lean_ctor_set_uint8(x_553, 8, x_496);
lean_ctor_set_uint8(x_553, 9, x_497);
lean_ctor_set_uint8(x_553, 10, x_498);
lean_ctor_set_uint8(x_553, 11, x_499);
lean_ctor_set_uint8(x_553, 12, x_551);
lean_ctor_set_uint8(x_553, 13, x_551);
lean_ctor_set_uint8(x_553, 14, x_552);
lean_ctor_set_uint8(x_553, 15, x_551);
lean_ctor_set_uint8(x_553, 16, x_551);
x_554 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_553);
x_555 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_555, 0, x_553);
lean_ctor_set(x_555, 1, x_480);
lean_ctor_set(x_555, 2, x_481);
lean_ctor_set(x_555, 3, x_482);
lean_ctor_set(x_555, 4, x_483);
lean_ctor_set(x_555, 5, x_484);
lean_ctor_set(x_555, 6, x_485);
lean_ctor_set_uint64(x_555, sizeof(void*)*7, x_554);
lean_ctor_set_uint8(x_555, sizeof(void*)*7 + 8, x_479);
lean_ctor_set_uint8(x_555, sizeof(void*)*7 + 9, x_486);
lean_ctor_set_uint8(x_555, sizeof(void*)*7 + 10, x_487);
x_556 = l_Lean_Meta_inferTypeImp_infer(x_1, x_555, x_3, x_4, x_5, x_550);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 x_559 = x_556;
} else {
 lean_dec_ref(x_556);
 x_559 = lean_box(0);
}
if (lean_is_scalar(x_559)) {
 x_560 = lean_alloc_ctor(0, 2, 0);
} else {
 x_560 = x_559;
}
lean_ctor_set(x_560, 0, x_557);
lean_ctor_set(x_560, 1, x_558);
return x_560;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_561 = lean_ctor_get(x_556, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_556, 1);
lean_inc(x_562);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 x_563 = x_556;
} else {
 lean_dec_ref(x_556);
 x_563 = lean_box(0);
}
if (lean_is_scalar(x_563)) {
 x_564 = lean_alloc_ctor(1, 2, 0);
} else {
 x_564 = x_563;
}
lean_ctor_set(x_564, 0, x_561);
lean_ctor_set(x_564, 1, x_562);
return x_564;
}
}
else
{
uint8_t x_565; 
x_565 = lean_ctor_get_uint8(x_516, 16);
if (x_565 == 0)
{
lean_object* x_566; uint8_t x_567; uint8_t x_568; lean_object* x_569; uint64_t x_570; lean_object* x_571; lean_object* x_572; 
lean_dec(x_516);
lean_dec(x_514);
x_566 = lean_ctor_get(x_515, 1);
lean_inc(x_566);
lean_dec(x_515);
x_567 = 1;
x_568 = 2;
x_569 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_569, 0, x_488);
lean_ctor_set_uint8(x_569, 1, x_489);
lean_ctor_set_uint8(x_569, 2, x_490);
lean_ctor_set_uint8(x_569, 3, x_491);
lean_ctor_set_uint8(x_569, 4, x_492);
lean_ctor_set_uint8(x_569, 5, x_493);
lean_ctor_set_uint8(x_569, 6, x_494);
lean_ctor_set_uint8(x_569, 7, x_495);
lean_ctor_set_uint8(x_569, 8, x_496);
lean_ctor_set_uint8(x_569, 9, x_497);
lean_ctor_set_uint8(x_569, 10, x_498);
lean_ctor_set_uint8(x_569, 11, x_499);
lean_ctor_set_uint8(x_569, 12, x_567);
lean_ctor_set_uint8(x_569, 13, x_567);
lean_ctor_set_uint8(x_569, 14, x_568);
lean_ctor_set_uint8(x_569, 15, x_567);
lean_ctor_set_uint8(x_569, 16, x_567);
x_570 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_569);
x_571 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_571, 0, x_569);
lean_ctor_set(x_571, 1, x_480);
lean_ctor_set(x_571, 2, x_481);
lean_ctor_set(x_571, 3, x_482);
lean_ctor_set(x_571, 4, x_483);
lean_ctor_set(x_571, 5, x_484);
lean_ctor_set(x_571, 6, x_485);
lean_ctor_set_uint64(x_571, sizeof(void*)*7, x_570);
lean_ctor_set_uint8(x_571, sizeof(void*)*7 + 8, x_479);
lean_ctor_set_uint8(x_571, sizeof(void*)*7 + 9, x_486);
lean_ctor_set_uint8(x_571, sizeof(void*)*7 + 10, x_487);
x_572 = l_Lean_Meta_inferTypeImp_infer(x_1, x_571, x_3, x_4, x_5, x_566);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_572, 1);
lean_inc(x_574);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_575 = x_572;
} else {
 lean_dec_ref(x_572);
 x_575 = lean_box(0);
}
if (lean_is_scalar(x_575)) {
 x_576 = lean_alloc_ctor(0, 2, 0);
} else {
 x_576 = x_575;
}
lean_ctor_set(x_576, 0, x_573);
lean_ctor_set(x_576, 1, x_574);
return x_576;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_577 = lean_ctor_get(x_572, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_572, 1);
lean_inc(x_578);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_579 = x_572;
} else {
 lean_dec_ref(x_572);
 x_579 = lean_box(0);
}
if (lean_is_scalar(x_579)) {
 x_580 = lean_alloc_ctor(1, 2, 0);
} else {
 x_580 = x_579;
}
lean_ctor_set(x_580, 0, x_577);
lean_ctor_set(x_580, 1, x_578);
return x_580;
}
}
else
{
lean_object* x_581; uint8_t x_582; uint8_t x_583; uint8_t x_584; 
x_581 = lean_ctor_get(x_515, 1);
lean_inc(x_581);
lean_dec(x_515);
x_582 = lean_ctor_get_uint8(x_516, 14);
lean_dec(x_516);
x_583 = 2;
x_584 = l_Lean_Meta_instDecidableEqProjReductionKind(x_582, x_583);
if (x_584 == 0)
{
uint8_t x_585; lean_object* x_586; uint64_t x_587; lean_object* x_588; lean_object* x_589; 
lean_dec(x_514);
x_585 = 1;
x_586 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_586, 0, x_488);
lean_ctor_set_uint8(x_586, 1, x_489);
lean_ctor_set_uint8(x_586, 2, x_490);
lean_ctor_set_uint8(x_586, 3, x_491);
lean_ctor_set_uint8(x_586, 4, x_492);
lean_ctor_set_uint8(x_586, 5, x_493);
lean_ctor_set_uint8(x_586, 6, x_494);
lean_ctor_set_uint8(x_586, 7, x_495);
lean_ctor_set_uint8(x_586, 8, x_496);
lean_ctor_set_uint8(x_586, 9, x_497);
lean_ctor_set_uint8(x_586, 10, x_498);
lean_ctor_set_uint8(x_586, 11, x_499);
lean_ctor_set_uint8(x_586, 12, x_585);
lean_ctor_set_uint8(x_586, 13, x_585);
lean_ctor_set_uint8(x_586, 14, x_583);
lean_ctor_set_uint8(x_586, 15, x_585);
lean_ctor_set_uint8(x_586, 16, x_585);
x_587 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_586);
x_588 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_588, 0, x_586);
lean_ctor_set(x_588, 1, x_480);
lean_ctor_set(x_588, 2, x_481);
lean_ctor_set(x_588, 3, x_482);
lean_ctor_set(x_588, 4, x_483);
lean_ctor_set(x_588, 5, x_484);
lean_ctor_set(x_588, 6, x_485);
lean_ctor_set_uint64(x_588, sizeof(void*)*7, x_587);
lean_ctor_set_uint8(x_588, sizeof(void*)*7 + 8, x_479);
lean_ctor_set_uint8(x_588, sizeof(void*)*7 + 9, x_486);
lean_ctor_set_uint8(x_588, sizeof(void*)*7 + 10, x_487);
x_589 = l_Lean_Meta_inferTypeImp_infer(x_1, x_588, x_3, x_4, x_5, x_581);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_589, 1);
lean_inc(x_591);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 lean_ctor_release(x_589, 1);
 x_592 = x_589;
} else {
 lean_dec_ref(x_589);
 x_592 = lean_box(0);
}
if (lean_is_scalar(x_592)) {
 x_593 = lean_alloc_ctor(0, 2, 0);
} else {
 x_593 = x_592;
}
lean_ctor_set(x_593, 0, x_590);
lean_ctor_set(x_593, 1, x_591);
return x_593;
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_594 = lean_ctor_get(x_589, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_589, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 lean_ctor_release(x_589, 1);
 x_596 = x_589;
} else {
 lean_dec_ref(x_589);
 x_596 = lean_box(0);
}
if (lean_is_scalar(x_596)) {
 x_597 = lean_alloc_ctor(1, 2, 0);
} else {
 x_597 = x_596;
}
lean_ctor_set(x_597, 0, x_594);
lean_ctor_set(x_597, 1, x_595);
return x_597;
}
}
else
{
lean_object* x_598; 
lean_dec(x_485);
lean_dec(x_484);
lean_dec(x_483);
lean_dec(x_482);
lean_dec(x_481);
lean_dec(x_480);
x_598 = l_Lean_Meta_inferTypeImp_infer(x_1, x_514, x_3, x_4, x_5, x_581);
if (lean_obj_tag(x_598) == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_598, 1);
lean_inc(x_600);
if (lean_is_exclusive(x_598)) {
 lean_ctor_release(x_598, 0);
 lean_ctor_release(x_598, 1);
 x_601 = x_598;
} else {
 lean_dec_ref(x_598);
 x_601 = lean_box(0);
}
if (lean_is_scalar(x_601)) {
 x_602 = lean_alloc_ctor(0, 2, 0);
} else {
 x_602 = x_601;
}
lean_ctor_set(x_602, 0, x_599);
lean_ctor_set(x_602, 1, x_600);
return x_602;
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_603 = lean_ctor_get(x_598, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_598, 1);
lean_inc(x_604);
if (lean_is_exclusive(x_598)) {
 lean_ctor_release(x_598, 0);
 lean_ctor_release(x_598, 1);
 x_605 = x_598;
} else {
 lean_dec_ref(x_598);
 x_605 = lean_box(0);
}
if (lean_is_scalar(x_605)) {
 x_606 = lean_alloc_ctor(1, 2, 0);
} else {
 x_606 = x_605;
}
lean_ctor_set(x_606, 0, x_603);
lean_ctor_set(x_606, 1, x_604);
return x_606;
}
}
}
}
}
}
}
else
{
lean_object* x_607; uint64_t x_608; uint64_t x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; uint8_t x_613; 
if (lean_is_scalar(x_505)) {
 x_607 = lean_alloc_ctor(0, 0, 17);
} else {
 x_607 = x_505;
}
lean_ctor_set_uint8(x_607, 0, x_488);
lean_ctor_set_uint8(x_607, 1, x_489);
lean_ctor_set_uint8(x_607, 2, x_490);
lean_ctor_set_uint8(x_607, 3, x_491);
lean_ctor_set_uint8(x_607, 4, x_492);
lean_ctor_set_uint8(x_607, 5, x_493);
lean_ctor_set_uint8(x_607, 6, x_494);
lean_ctor_set_uint8(x_607, 7, x_495);
lean_ctor_set_uint8(x_607, 8, x_496);
lean_ctor_set_uint8(x_607, 9, x_506);
lean_ctor_set_uint8(x_607, 10, x_498);
lean_ctor_set_uint8(x_607, 11, x_499);
lean_ctor_set_uint8(x_607, 12, x_500);
lean_ctor_set_uint8(x_607, 13, x_501);
lean_ctor_set_uint8(x_607, 14, x_502);
lean_ctor_set_uint8(x_607, 15, x_503);
lean_ctor_set_uint8(x_607, 16, x_504);
x_608 = l_Lean_Meta_withInferTypeConfig___rarg___closed__1;
x_609 = lean_uint64_lor(x_510, x_608);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_inc(x_482);
lean_inc(x_481);
lean_inc(x_480);
x_610 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_610, 0, x_607);
lean_ctor_set(x_610, 1, x_480);
lean_ctor_set(x_610, 2, x_481);
lean_ctor_set(x_610, 3, x_482);
lean_ctor_set(x_610, 4, x_483);
lean_ctor_set(x_610, 5, x_484);
lean_ctor_set(x_610, 6, x_485);
lean_ctor_set_uint64(x_610, sizeof(void*)*7, x_609);
lean_ctor_set_uint8(x_610, sizeof(void*)*7 + 8, x_479);
lean_ctor_set_uint8(x_610, sizeof(void*)*7 + 9, x_486);
lean_ctor_set_uint8(x_610, sizeof(void*)*7 + 10, x_487);
x_611 = l_Lean_Meta_getConfig(x_610, x_3, x_4, x_5, x_6);
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
x_613 = lean_ctor_get_uint8(x_612, 13);
if (x_613 == 0)
{
lean_object* x_614; uint8_t x_615; uint8_t x_616; lean_object* x_617; uint64_t x_618; lean_object* x_619; lean_object* x_620; 
lean_dec(x_612);
lean_dec(x_610);
x_614 = lean_ctor_get(x_611, 1);
lean_inc(x_614);
lean_dec(x_611);
x_615 = 1;
x_616 = 2;
x_617 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_617, 0, x_488);
lean_ctor_set_uint8(x_617, 1, x_489);
lean_ctor_set_uint8(x_617, 2, x_490);
lean_ctor_set_uint8(x_617, 3, x_491);
lean_ctor_set_uint8(x_617, 4, x_492);
lean_ctor_set_uint8(x_617, 5, x_493);
lean_ctor_set_uint8(x_617, 6, x_494);
lean_ctor_set_uint8(x_617, 7, x_495);
lean_ctor_set_uint8(x_617, 8, x_496);
lean_ctor_set_uint8(x_617, 9, x_506);
lean_ctor_set_uint8(x_617, 10, x_498);
lean_ctor_set_uint8(x_617, 11, x_499);
lean_ctor_set_uint8(x_617, 12, x_615);
lean_ctor_set_uint8(x_617, 13, x_615);
lean_ctor_set_uint8(x_617, 14, x_616);
lean_ctor_set_uint8(x_617, 15, x_615);
lean_ctor_set_uint8(x_617, 16, x_615);
x_618 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_617);
x_619 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_619, 0, x_617);
lean_ctor_set(x_619, 1, x_480);
lean_ctor_set(x_619, 2, x_481);
lean_ctor_set(x_619, 3, x_482);
lean_ctor_set(x_619, 4, x_483);
lean_ctor_set(x_619, 5, x_484);
lean_ctor_set(x_619, 6, x_485);
lean_ctor_set_uint64(x_619, sizeof(void*)*7, x_618);
lean_ctor_set_uint8(x_619, sizeof(void*)*7 + 8, x_479);
lean_ctor_set_uint8(x_619, sizeof(void*)*7 + 9, x_486);
lean_ctor_set_uint8(x_619, sizeof(void*)*7 + 10, x_487);
x_620 = l_Lean_Meta_inferTypeImp_infer(x_1, x_619, x_3, x_4, x_5, x_614);
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_620, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 lean_ctor_release(x_620, 1);
 x_623 = x_620;
} else {
 lean_dec_ref(x_620);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(0, 2, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_621);
lean_ctor_set(x_624, 1, x_622);
return x_624;
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_625 = lean_ctor_get(x_620, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_620, 1);
lean_inc(x_626);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 lean_ctor_release(x_620, 1);
 x_627 = x_620;
} else {
 lean_dec_ref(x_620);
 x_627 = lean_box(0);
}
if (lean_is_scalar(x_627)) {
 x_628 = lean_alloc_ctor(1, 2, 0);
} else {
 x_628 = x_627;
}
lean_ctor_set(x_628, 0, x_625);
lean_ctor_set(x_628, 1, x_626);
return x_628;
}
}
else
{
uint8_t x_629; 
x_629 = lean_ctor_get_uint8(x_612, 12);
if (x_629 == 0)
{
lean_object* x_630; uint8_t x_631; uint8_t x_632; lean_object* x_633; uint64_t x_634; lean_object* x_635; lean_object* x_636; 
lean_dec(x_612);
lean_dec(x_610);
x_630 = lean_ctor_get(x_611, 1);
lean_inc(x_630);
lean_dec(x_611);
x_631 = 1;
x_632 = 2;
x_633 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_633, 0, x_488);
lean_ctor_set_uint8(x_633, 1, x_489);
lean_ctor_set_uint8(x_633, 2, x_490);
lean_ctor_set_uint8(x_633, 3, x_491);
lean_ctor_set_uint8(x_633, 4, x_492);
lean_ctor_set_uint8(x_633, 5, x_493);
lean_ctor_set_uint8(x_633, 6, x_494);
lean_ctor_set_uint8(x_633, 7, x_495);
lean_ctor_set_uint8(x_633, 8, x_496);
lean_ctor_set_uint8(x_633, 9, x_506);
lean_ctor_set_uint8(x_633, 10, x_498);
lean_ctor_set_uint8(x_633, 11, x_499);
lean_ctor_set_uint8(x_633, 12, x_631);
lean_ctor_set_uint8(x_633, 13, x_631);
lean_ctor_set_uint8(x_633, 14, x_632);
lean_ctor_set_uint8(x_633, 15, x_631);
lean_ctor_set_uint8(x_633, 16, x_631);
x_634 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_633);
x_635 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_635, 0, x_633);
lean_ctor_set(x_635, 1, x_480);
lean_ctor_set(x_635, 2, x_481);
lean_ctor_set(x_635, 3, x_482);
lean_ctor_set(x_635, 4, x_483);
lean_ctor_set(x_635, 5, x_484);
lean_ctor_set(x_635, 6, x_485);
lean_ctor_set_uint64(x_635, sizeof(void*)*7, x_634);
lean_ctor_set_uint8(x_635, sizeof(void*)*7 + 8, x_479);
lean_ctor_set_uint8(x_635, sizeof(void*)*7 + 9, x_486);
lean_ctor_set_uint8(x_635, sizeof(void*)*7 + 10, x_487);
x_636 = l_Lean_Meta_inferTypeImp_infer(x_1, x_635, x_3, x_4, x_5, x_630);
if (lean_obj_tag(x_636) == 0)
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_637 = lean_ctor_get(x_636, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_636, 1);
lean_inc(x_638);
if (lean_is_exclusive(x_636)) {
 lean_ctor_release(x_636, 0);
 lean_ctor_release(x_636, 1);
 x_639 = x_636;
} else {
 lean_dec_ref(x_636);
 x_639 = lean_box(0);
}
if (lean_is_scalar(x_639)) {
 x_640 = lean_alloc_ctor(0, 2, 0);
} else {
 x_640 = x_639;
}
lean_ctor_set(x_640, 0, x_637);
lean_ctor_set(x_640, 1, x_638);
return x_640;
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_641 = lean_ctor_get(x_636, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_636, 1);
lean_inc(x_642);
if (lean_is_exclusive(x_636)) {
 lean_ctor_release(x_636, 0);
 lean_ctor_release(x_636, 1);
 x_643 = x_636;
} else {
 lean_dec_ref(x_636);
 x_643 = lean_box(0);
}
if (lean_is_scalar(x_643)) {
 x_644 = lean_alloc_ctor(1, 2, 0);
} else {
 x_644 = x_643;
}
lean_ctor_set(x_644, 0, x_641);
lean_ctor_set(x_644, 1, x_642);
return x_644;
}
}
else
{
uint8_t x_645; 
x_645 = lean_ctor_get_uint8(x_612, 15);
if (x_645 == 0)
{
lean_object* x_646; uint8_t x_647; uint8_t x_648; lean_object* x_649; uint64_t x_650; lean_object* x_651; lean_object* x_652; 
lean_dec(x_612);
lean_dec(x_610);
x_646 = lean_ctor_get(x_611, 1);
lean_inc(x_646);
lean_dec(x_611);
x_647 = 1;
x_648 = 2;
x_649 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_649, 0, x_488);
lean_ctor_set_uint8(x_649, 1, x_489);
lean_ctor_set_uint8(x_649, 2, x_490);
lean_ctor_set_uint8(x_649, 3, x_491);
lean_ctor_set_uint8(x_649, 4, x_492);
lean_ctor_set_uint8(x_649, 5, x_493);
lean_ctor_set_uint8(x_649, 6, x_494);
lean_ctor_set_uint8(x_649, 7, x_495);
lean_ctor_set_uint8(x_649, 8, x_496);
lean_ctor_set_uint8(x_649, 9, x_506);
lean_ctor_set_uint8(x_649, 10, x_498);
lean_ctor_set_uint8(x_649, 11, x_499);
lean_ctor_set_uint8(x_649, 12, x_647);
lean_ctor_set_uint8(x_649, 13, x_647);
lean_ctor_set_uint8(x_649, 14, x_648);
lean_ctor_set_uint8(x_649, 15, x_647);
lean_ctor_set_uint8(x_649, 16, x_647);
x_650 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_649);
x_651 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_651, 0, x_649);
lean_ctor_set(x_651, 1, x_480);
lean_ctor_set(x_651, 2, x_481);
lean_ctor_set(x_651, 3, x_482);
lean_ctor_set(x_651, 4, x_483);
lean_ctor_set(x_651, 5, x_484);
lean_ctor_set(x_651, 6, x_485);
lean_ctor_set_uint64(x_651, sizeof(void*)*7, x_650);
lean_ctor_set_uint8(x_651, sizeof(void*)*7 + 8, x_479);
lean_ctor_set_uint8(x_651, sizeof(void*)*7 + 9, x_486);
lean_ctor_set_uint8(x_651, sizeof(void*)*7 + 10, x_487);
x_652 = l_Lean_Meta_inferTypeImp_infer(x_1, x_651, x_3, x_4, x_5, x_646);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_652, 1);
lean_inc(x_654);
if (lean_is_exclusive(x_652)) {
 lean_ctor_release(x_652, 0);
 lean_ctor_release(x_652, 1);
 x_655 = x_652;
} else {
 lean_dec_ref(x_652);
 x_655 = lean_box(0);
}
if (lean_is_scalar(x_655)) {
 x_656 = lean_alloc_ctor(0, 2, 0);
} else {
 x_656 = x_655;
}
lean_ctor_set(x_656, 0, x_653);
lean_ctor_set(x_656, 1, x_654);
return x_656;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_657 = lean_ctor_get(x_652, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_652, 1);
lean_inc(x_658);
if (lean_is_exclusive(x_652)) {
 lean_ctor_release(x_652, 0);
 lean_ctor_release(x_652, 1);
 x_659 = x_652;
} else {
 lean_dec_ref(x_652);
 x_659 = lean_box(0);
}
if (lean_is_scalar(x_659)) {
 x_660 = lean_alloc_ctor(1, 2, 0);
} else {
 x_660 = x_659;
}
lean_ctor_set(x_660, 0, x_657);
lean_ctor_set(x_660, 1, x_658);
return x_660;
}
}
else
{
uint8_t x_661; 
x_661 = lean_ctor_get_uint8(x_612, 16);
if (x_661 == 0)
{
lean_object* x_662; uint8_t x_663; uint8_t x_664; lean_object* x_665; uint64_t x_666; lean_object* x_667; lean_object* x_668; 
lean_dec(x_612);
lean_dec(x_610);
x_662 = lean_ctor_get(x_611, 1);
lean_inc(x_662);
lean_dec(x_611);
x_663 = 1;
x_664 = 2;
x_665 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_665, 0, x_488);
lean_ctor_set_uint8(x_665, 1, x_489);
lean_ctor_set_uint8(x_665, 2, x_490);
lean_ctor_set_uint8(x_665, 3, x_491);
lean_ctor_set_uint8(x_665, 4, x_492);
lean_ctor_set_uint8(x_665, 5, x_493);
lean_ctor_set_uint8(x_665, 6, x_494);
lean_ctor_set_uint8(x_665, 7, x_495);
lean_ctor_set_uint8(x_665, 8, x_496);
lean_ctor_set_uint8(x_665, 9, x_506);
lean_ctor_set_uint8(x_665, 10, x_498);
lean_ctor_set_uint8(x_665, 11, x_499);
lean_ctor_set_uint8(x_665, 12, x_663);
lean_ctor_set_uint8(x_665, 13, x_663);
lean_ctor_set_uint8(x_665, 14, x_664);
lean_ctor_set_uint8(x_665, 15, x_663);
lean_ctor_set_uint8(x_665, 16, x_663);
x_666 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_665);
x_667 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_667, 0, x_665);
lean_ctor_set(x_667, 1, x_480);
lean_ctor_set(x_667, 2, x_481);
lean_ctor_set(x_667, 3, x_482);
lean_ctor_set(x_667, 4, x_483);
lean_ctor_set(x_667, 5, x_484);
lean_ctor_set(x_667, 6, x_485);
lean_ctor_set_uint64(x_667, sizeof(void*)*7, x_666);
lean_ctor_set_uint8(x_667, sizeof(void*)*7 + 8, x_479);
lean_ctor_set_uint8(x_667, sizeof(void*)*7 + 9, x_486);
lean_ctor_set_uint8(x_667, sizeof(void*)*7 + 10, x_487);
x_668 = l_Lean_Meta_inferTypeImp_infer(x_1, x_667, x_3, x_4, x_5, x_662);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_669 = lean_ctor_get(x_668, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_668, 1);
lean_inc(x_670);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 x_671 = x_668;
} else {
 lean_dec_ref(x_668);
 x_671 = lean_box(0);
}
if (lean_is_scalar(x_671)) {
 x_672 = lean_alloc_ctor(0, 2, 0);
} else {
 x_672 = x_671;
}
lean_ctor_set(x_672, 0, x_669);
lean_ctor_set(x_672, 1, x_670);
return x_672;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
x_673 = lean_ctor_get(x_668, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_668, 1);
lean_inc(x_674);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 x_675 = x_668;
} else {
 lean_dec_ref(x_668);
 x_675 = lean_box(0);
}
if (lean_is_scalar(x_675)) {
 x_676 = lean_alloc_ctor(1, 2, 0);
} else {
 x_676 = x_675;
}
lean_ctor_set(x_676, 0, x_673);
lean_ctor_set(x_676, 1, x_674);
return x_676;
}
}
else
{
lean_object* x_677; uint8_t x_678; uint8_t x_679; uint8_t x_680; 
x_677 = lean_ctor_get(x_611, 1);
lean_inc(x_677);
lean_dec(x_611);
x_678 = lean_ctor_get_uint8(x_612, 14);
lean_dec(x_612);
x_679 = 2;
x_680 = l_Lean_Meta_instDecidableEqProjReductionKind(x_678, x_679);
if (x_680 == 0)
{
uint8_t x_681; lean_object* x_682; uint64_t x_683; lean_object* x_684; lean_object* x_685; 
lean_dec(x_610);
x_681 = 1;
x_682 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_682, 0, x_488);
lean_ctor_set_uint8(x_682, 1, x_489);
lean_ctor_set_uint8(x_682, 2, x_490);
lean_ctor_set_uint8(x_682, 3, x_491);
lean_ctor_set_uint8(x_682, 4, x_492);
lean_ctor_set_uint8(x_682, 5, x_493);
lean_ctor_set_uint8(x_682, 6, x_494);
lean_ctor_set_uint8(x_682, 7, x_495);
lean_ctor_set_uint8(x_682, 8, x_496);
lean_ctor_set_uint8(x_682, 9, x_506);
lean_ctor_set_uint8(x_682, 10, x_498);
lean_ctor_set_uint8(x_682, 11, x_499);
lean_ctor_set_uint8(x_682, 12, x_681);
lean_ctor_set_uint8(x_682, 13, x_681);
lean_ctor_set_uint8(x_682, 14, x_679);
lean_ctor_set_uint8(x_682, 15, x_681);
lean_ctor_set_uint8(x_682, 16, x_681);
x_683 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_682);
x_684 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_684, 0, x_682);
lean_ctor_set(x_684, 1, x_480);
lean_ctor_set(x_684, 2, x_481);
lean_ctor_set(x_684, 3, x_482);
lean_ctor_set(x_684, 4, x_483);
lean_ctor_set(x_684, 5, x_484);
lean_ctor_set(x_684, 6, x_485);
lean_ctor_set_uint64(x_684, sizeof(void*)*7, x_683);
lean_ctor_set_uint8(x_684, sizeof(void*)*7 + 8, x_479);
lean_ctor_set_uint8(x_684, sizeof(void*)*7 + 9, x_486);
lean_ctor_set_uint8(x_684, sizeof(void*)*7 + 10, x_487);
x_685 = l_Lean_Meta_inferTypeImp_infer(x_1, x_684, x_3, x_4, x_5, x_677);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_686 = lean_ctor_get(x_685, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_685, 1);
lean_inc(x_687);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 x_688 = x_685;
} else {
 lean_dec_ref(x_685);
 x_688 = lean_box(0);
}
if (lean_is_scalar(x_688)) {
 x_689 = lean_alloc_ctor(0, 2, 0);
} else {
 x_689 = x_688;
}
lean_ctor_set(x_689, 0, x_686);
lean_ctor_set(x_689, 1, x_687);
return x_689;
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_690 = lean_ctor_get(x_685, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_685, 1);
lean_inc(x_691);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 x_692 = x_685;
} else {
 lean_dec_ref(x_685);
 x_692 = lean_box(0);
}
if (lean_is_scalar(x_692)) {
 x_693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_693 = x_692;
}
lean_ctor_set(x_693, 0, x_690);
lean_ctor_set(x_693, 1, x_691);
return x_693;
}
}
else
{
lean_object* x_694; 
lean_dec(x_485);
lean_dec(x_484);
lean_dec(x_483);
lean_dec(x_482);
lean_dec(x_481);
lean_dec(x_480);
x_694 = l_Lean_Meta_inferTypeImp_infer(x_1, x_610, x_3, x_4, x_5, x_677);
if (lean_obj_tag(x_694) == 0)
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_695 = lean_ctor_get(x_694, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_694, 1);
lean_inc(x_696);
if (lean_is_exclusive(x_694)) {
 lean_ctor_release(x_694, 0);
 lean_ctor_release(x_694, 1);
 x_697 = x_694;
} else {
 lean_dec_ref(x_694);
 x_697 = lean_box(0);
}
if (lean_is_scalar(x_697)) {
 x_698 = lean_alloc_ctor(0, 2, 0);
} else {
 x_698 = x_697;
}
lean_ctor_set(x_698, 0, x_695);
lean_ctor_set(x_698, 1, x_696);
return x_698;
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_699 = lean_ctor_get(x_694, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_694, 1);
lean_inc(x_700);
if (lean_is_exclusive(x_694)) {
 lean_ctor_release(x_694, 0);
 lean_ctor_release(x_694, 1);
 x_701 = x_694;
} else {
 lean_dec_ref(x_694);
 x_701 = lean_box(0);
}
if (lean_is_scalar(x_701)) {
 x_702 = lean_alloc_ctor(1, 2, 0);
} else {
 x_702 = x_701;
}
lean_ctor_set(x_702, 0, x_699);
lean_ctor_set(x_702, 1, x_700);
return x_702;
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; uint64_t x_707; uint8_t x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; uint8_t x_716; lean_object* x_717; uint8_t x_718; uint8_t x_719; uint8_t x_720; uint8_t x_721; uint8_t x_722; uint8_t x_723; uint8_t x_724; uint8_t x_725; uint8_t x_726; uint8_t x_727; uint8_t x_728; uint8_t x_729; uint8_t x_730; uint8_t x_731; uint8_t x_732; uint8_t x_733; uint8_t x_734; lean_object* x_735; uint8_t x_736; uint8_t x_737; uint64_t x_738; uint64_t x_739; uint64_t x_740; 
lean_dec(x_4);
x_703 = lean_unsigned_to_nat(1u);
x_704 = lean_nat_add(x_10, x_703);
lean_dec(x_10);
x_705 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_705, 0, x_7);
lean_ctor_set(x_705, 1, x_8);
lean_ctor_set(x_705, 2, x_9);
lean_ctor_set(x_705, 3, x_704);
lean_ctor_set(x_705, 4, x_11);
lean_ctor_set(x_705, 5, x_12);
lean_ctor_set(x_705, 6, x_13);
lean_ctor_set(x_705, 7, x_14);
lean_ctor_set(x_705, 8, x_15);
lean_ctor_set(x_705, 9, x_16);
lean_ctor_set(x_705, 10, x_17);
lean_ctor_set(x_705, 11, x_19);
lean_ctor_set_uint8(x_705, sizeof(void*)*12, x_18);
lean_ctor_set_uint8(x_705, sizeof(void*)*12 + 1, x_20);
x_706 = lean_ctor_get(x_2, 0);
lean_inc(x_706);
x_707 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_708 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_709 = lean_ctor_get(x_2, 1);
lean_inc(x_709);
x_710 = lean_ctor_get(x_2, 2);
lean_inc(x_710);
x_711 = lean_ctor_get(x_2, 3);
lean_inc(x_711);
x_712 = lean_ctor_get(x_2, 4);
lean_inc(x_712);
x_713 = lean_ctor_get(x_2, 5);
lean_inc(x_713);
x_714 = lean_ctor_get(x_2, 6);
lean_inc(x_714);
x_715 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_716 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_717 = x_2;
} else {
 lean_dec_ref(x_2);
 x_717 = lean_box(0);
}
x_718 = lean_ctor_get_uint8(x_706, 0);
x_719 = lean_ctor_get_uint8(x_706, 1);
x_720 = lean_ctor_get_uint8(x_706, 2);
x_721 = lean_ctor_get_uint8(x_706, 3);
x_722 = lean_ctor_get_uint8(x_706, 4);
x_723 = lean_ctor_get_uint8(x_706, 5);
x_724 = lean_ctor_get_uint8(x_706, 6);
x_725 = lean_ctor_get_uint8(x_706, 7);
x_726 = lean_ctor_get_uint8(x_706, 8);
x_727 = lean_ctor_get_uint8(x_706, 9);
x_728 = lean_ctor_get_uint8(x_706, 10);
x_729 = lean_ctor_get_uint8(x_706, 11);
x_730 = lean_ctor_get_uint8(x_706, 12);
x_731 = lean_ctor_get_uint8(x_706, 13);
x_732 = lean_ctor_get_uint8(x_706, 14);
x_733 = lean_ctor_get_uint8(x_706, 15);
x_734 = lean_ctor_get_uint8(x_706, 16);
if (lean_is_exclusive(x_706)) {
 x_735 = x_706;
} else {
 lean_dec_ref(x_706);
 x_735 = lean_box(0);
}
x_736 = 1;
x_737 = l_Lean_Meta_TransparencyMode_lt(x_727, x_736);
x_738 = 2;
x_739 = lean_uint64_shift_right(x_707, x_738);
x_740 = lean_uint64_shift_left(x_739, x_738);
if (x_737 == 0)
{
lean_object* x_741; uint64_t x_742; uint64_t x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; uint8_t x_747; 
if (lean_is_scalar(x_735)) {
 x_741 = lean_alloc_ctor(0, 0, 17);
} else {
 x_741 = x_735;
}
lean_ctor_set_uint8(x_741, 0, x_718);
lean_ctor_set_uint8(x_741, 1, x_719);
lean_ctor_set_uint8(x_741, 2, x_720);
lean_ctor_set_uint8(x_741, 3, x_721);
lean_ctor_set_uint8(x_741, 4, x_722);
lean_ctor_set_uint8(x_741, 5, x_723);
lean_ctor_set_uint8(x_741, 6, x_724);
lean_ctor_set_uint8(x_741, 7, x_725);
lean_ctor_set_uint8(x_741, 8, x_726);
lean_ctor_set_uint8(x_741, 9, x_727);
lean_ctor_set_uint8(x_741, 10, x_728);
lean_ctor_set_uint8(x_741, 11, x_729);
lean_ctor_set_uint8(x_741, 12, x_730);
lean_ctor_set_uint8(x_741, 13, x_731);
lean_ctor_set_uint8(x_741, 14, x_732);
lean_ctor_set_uint8(x_741, 15, x_733);
lean_ctor_set_uint8(x_741, 16, x_734);
x_742 = l_Lean_Meta_TransparencyMode_toUInt64(x_727);
x_743 = lean_uint64_lor(x_740, x_742);
lean_inc(x_714);
lean_inc(x_713);
lean_inc(x_712);
lean_inc(x_711);
lean_inc(x_710);
lean_inc(x_709);
if (lean_is_scalar(x_717)) {
 x_744 = lean_alloc_ctor(0, 7, 11);
} else {
 x_744 = x_717;
}
lean_ctor_set(x_744, 0, x_741);
lean_ctor_set(x_744, 1, x_709);
lean_ctor_set(x_744, 2, x_710);
lean_ctor_set(x_744, 3, x_711);
lean_ctor_set(x_744, 4, x_712);
lean_ctor_set(x_744, 5, x_713);
lean_ctor_set(x_744, 6, x_714);
lean_ctor_set_uint64(x_744, sizeof(void*)*7, x_743);
lean_ctor_set_uint8(x_744, sizeof(void*)*7 + 8, x_708);
lean_ctor_set_uint8(x_744, sizeof(void*)*7 + 9, x_715);
lean_ctor_set_uint8(x_744, sizeof(void*)*7 + 10, x_716);
x_745 = l_Lean_Meta_getConfig(x_744, x_3, x_705, x_5, x_6);
x_746 = lean_ctor_get(x_745, 0);
lean_inc(x_746);
x_747 = lean_ctor_get_uint8(x_746, 13);
if (x_747 == 0)
{
lean_object* x_748; uint8_t x_749; uint8_t x_750; lean_object* x_751; uint64_t x_752; lean_object* x_753; lean_object* x_754; 
lean_dec(x_746);
lean_dec(x_744);
x_748 = lean_ctor_get(x_745, 1);
lean_inc(x_748);
lean_dec(x_745);
x_749 = 1;
x_750 = 2;
x_751 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_751, 0, x_718);
lean_ctor_set_uint8(x_751, 1, x_719);
lean_ctor_set_uint8(x_751, 2, x_720);
lean_ctor_set_uint8(x_751, 3, x_721);
lean_ctor_set_uint8(x_751, 4, x_722);
lean_ctor_set_uint8(x_751, 5, x_723);
lean_ctor_set_uint8(x_751, 6, x_724);
lean_ctor_set_uint8(x_751, 7, x_725);
lean_ctor_set_uint8(x_751, 8, x_726);
lean_ctor_set_uint8(x_751, 9, x_727);
lean_ctor_set_uint8(x_751, 10, x_728);
lean_ctor_set_uint8(x_751, 11, x_729);
lean_ctor_set_uint8(x_751, 12, x_749);
lean_ctor_set_uint8(x_751, 13, x_749);
lean_ctor_set_uint8(x_751, 14, x_750);
lean_ctor_set_uint8(x_751, 15, x_749);
lean_ctor_set_uint8(x_751, 16, x_749);
x_752 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_751);
x_753 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_753, 0, x_751);
lean_ctor_set(x_753, 1, x_709);
lean_ctor_set(x_753, 2, x_710);
lean_ctor_set(x_753, 3, x_711);
lean_ctor_set(x_753, 4, x_712);
lean_ctor_set(x_753, 5, x_713);
lean_ctor_set(x_753, 6, x_714);
lean_ctor_set_uint64(x_753, sizeof(void*)*7, x_752);
lean_ctor_set_uint8(x_753, sizeof(void*)*7 + 8, x_708);
lean_ctor_set_uint8(x_753, sizeof(void*)*7 + 9, x_715);
lean_ctor_set_uint8(x_753, sizeof(void*)*7 + 10, x_716);
x_754 = l_Lean_Meta_inferTypeImp_infer(x_1, x_753, x_3, x_705, x_5, x_748);
if (lean_obj_tag(x_754) == 0)
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_755 = lean_ctor_get(x_754, 0);
lean_inc(x_755);
x_756 = lean_ctor_get(x_754, 1);
lean_inc(x_756);
if (lean_is_exclusive(x_754)) {
 lean_ctor_release(x_754, 0);
 lean_ctor_release(x_754, 1);
 x_757 = x_754;
} else {
 lean_dec_ref(x_754);
 x_757 = lean_box(0);
}
if (lean_is_scalar(x_757)) {
 x_758 = lean_alloc_ctor(0, 2, 0);
} else {
 x_758 = x_757;
}
lean_ctor_set(x_758, 0, x_755);
lean_ctor_set(x_758, 1, x_756);
return x_758;
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; 
x_759 = lean_ctor_get(x_754, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_754, 1);
lean_inc(x_760);
if (lean_is_exclusive(x_754)) {
 lean_ctor_release(x_754, 0);
 lean_ctor_release(x_754, 1);
 x_761 = x_754;
} else {
 lean_dec_ref(x_754);
 x_761 = lean_box(0);
}
if (lean_is_scalar(x_761)) {
 x_762 = lean_alloc_ctor(1, 2, 0);
} else {
 x_762 = x_761;
}
lean_ctor_set(x_762, 0, x_759);
lean_ctor_set(x_762, 1, x_760);
return x_762;
}
}
else
{
uint8_t x_763; 
x_763 = lean_ctor_get_uint8(x_746, 12);
if (x_763 == 0)
{
lean_object* x_764; uint8_t x_765; uint8_t x_766; lean_object* x_767; uint64_t x_768; lean_object* x_769; lean_object* x_770; 
lean_dec(x_746);
lean_dec(x_744);
x_764 = lean_ctor_get(x_745, 1);
lean_inc(x_764);
lean_dec(x_745);
x_765 = 1;
x_766 = 2;
x_767 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_767, 0, x_718);
lean_ctor_set_uint8(x_767, 1, x_719);
lean_ctor_set_uint8(x_767, 2, x_720);
lean_ctor_set_uint8(x_767, 3, x_721);
lean_ctor_set_uint8(x_767, 4, x_722);
lean_ctor_set_uint8(x_767, 5, x_723);
lean_ctor_set_uint8(x_767, 6, x_724);
lean_ctor_set_uint8(x_767, 7, x_725);
lean_ctor_set_uint8(x_767, 8, x_726);
lean_ctor_set_uint8(x_767, 9, x_727);
lean_ctor_set_uint8(x_767, 10, x_728);
lean_ctor_set_uint8(x_767, 11, x_729);
lean_ctor_set_uint8(x_767, 12, x_765);
lean_ctor_set_uint8(x_767, 13, x_765);
lean_ctor_set_uint8(x_767, 14, x_766);
lean_ctor_set_uint8(x_767, 15, x_765);
lean_ctor_set_uint8(x_767, 16, x_765);
x_768 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_767);
x_769 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_769, 0, x_767);
lean_ctor_set(x_769, 1, x_709);
lean_ctor_set(x_769, 2, x_710);
lean_ctor_set(x_769, 3, x_711);
lean_ctor_set(x_769, 4, x_712);
lean_ctor_set(x_769, 5, x_713);
lean_ctor_set(x_769, 6, x_714);
lean_ctor_set_uint64(x_769, sizeof(void*)*7, x_768);
lean_ctor_set_uint8(x_769, sizeof(void*)*7 + 8, x_708);
lean_ctor_set_uint8(x_769, sizeof(void*)*7 + 9, x_715);
lean_ctor_set_uint8(x_769, sizeof(void*)*7 + 10, x_716);
x_770 = l_Lean_Meta_inferTypeImp_infer(x_1, x_769, x_3, x_705, x_5, x_764);
if (lean_obj_tag(x_770) == 0)
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_771 = lean_ctor_get(x_770, 0);
lean_inc(x_771);
x_772 = lean_ctor_get(x_770, 1);
lean_inc(x_772);
if (lean_is_exclusive(x_770)) {
 lean_ctor_release(x_770, 0);
 lean_ctor_release(x_770, 1);
 x_773 = x_770;
} else {
 lean_dec_ref(x_770);
 x_773 = lean_box(0);
}
if (lean_is_scalar(x_773)) {
 x_774 = lean_alloc_ctor(0, 2, 0);
} else {
 x_774 = x_773;
}
lean_ctor_set(x_774, 0, x_771);
lean_ctor_set(x_774, 1, x_772);
return x_774;
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_775 = lean_ctor_get(x_770, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_770, 1);
lean_inc(x_776);
if (lean_is_exclusive(x_770)) {
 lean_ctor_release(x_770, 0);
 lean_ctor_release(x_770, 1);
 x_777 = x_770;
} else {
 lean_dec_ref(x_770);
 x_777 = lean_box(0);
}
if (lean_is_scalar(x_777)) {
 x_778 = lean_alloc_ctor(1, 2, 0);
} else {
 x_778 = x_777;
}
lean_ctor_set(x_778, 0, x_775);
lean_ctor_set(x_778, 1, x_776);
return x_778;
}
}
else
{
uint8_t x_779; 
x_779 = lean_ctor_get_uint8(x_746, 15);
if (x_779 == 0)
{
lean_object* x_780; uint8_t x_781; uint8_t x_782; lean_object* x_783; uint64_t x_784; lean_object* x_785; lean_object* x_786; 
lean_dec(x_746);
lean_dec(x_744);
x_780 = lean_ctor_get(x_745, 1);
lean_inc(x_780);
lean_dec(x_745);
x_781 = 1;
x_782 = 2;
x_783 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_783, 0, x_718);
lean_ctor_set_uint8(x_783, 1, x_719);
lean_ctor_set_uint8(x_783, 2, x_720);
lean_ctor_set_uint8(x_783, 3, x_721);
lean_ctor_set_uint8(x_783, 4, x_722);
lean_ctor_set_uint8(x_783, 5, x_723);
lean_ctor_set_uint8(x_783, 6, x_724);
lean_ctor_set_uint8(x_783, 7, x_725);
lean_ctor_set_uint8(x_783, 8, x_726);
lean_ctor_set_uint8(x_783, 9, x_727);
lean_ctor_set_uint8(x_783, 10, x_728);
lean_ctor_set_uint8(x_783, 11, x_729);
lean_ctor_set_uint8(x_783, 12, x_781);
lean_ctor_set_uint8(x_783, 13, x_781);
lean_ctor_set_uint8(x_783, 14, x_782);
lean_ctor_set_uint8(x_783, 15, x_781);
lean_ctor_set_uint8(x_783, 16, x_781);
x_784 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_783);
x_785 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_785, 0, x_783);
lean_ctor_set(x_785, 1, x_709);
lean_ctor_set(x_785, 2, x_710);
lean_ctor_set(x_785, 3, x_711);
lean_ctor_set(x_785, 4, x_712);
lean_ctor_set(x_785, 5, x_713);
lean_ctor_set(x_785, 6, x_714);
lean_ctor_set_uint64(x_785, sizeof(void*)*7, x_784);
lean_ctor_set_uint8(x_785, sizeof(void*)*7 + 8, x_708);
lean_ctor_set_uint8(x_785, sizeof(void*)*7 + 9, x_715);
lean_ctor_set_uint8(x_785, sizeof(void*)*7 + 10, x_716);
x_786 = l_Lean_Meta_inferTypeImp_infer(x_1, x_785, x_3, x_705, x_5, x_780);
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_787 = lean_ctor_get(x_786, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_786, 1);
lean_inc(x_788);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 x_789 = x_786;
} else {
 lean_dec_ref(x_786);
 x_789 = lean_box(0);
}
if (lean_is_scalar(x_789)) {
 x_790 = lean_alloc_ctor(0, 2, 0);
} else {
 x_790 = x_789;
}
lean_ctor_set(x_790, 0, x_787);
lean_ctor_set(x_790, 1, x_788);
return x_790;
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_791 = lean_ctor_get(x_786, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_786, 1);
lean_inc(x_792);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 x_793 = x_786;
} else {
 lean_dec_ref(x_786);
 x_793 = lean_box(0);
}
if (lean_is_scalar(x_793)) {
 x_794 = lean_alloc_ctor(1, 2, 0);
} else {
 x_794 = x_793;
}
lean_ctor_set(x_794, 0, x_791);
lean_ctor_set(x_794, 1, x_792);
return x_794;
}
}
else
{
uint8_t x_795; 
x_795 = lean_ctor_get_uint8(x_746, 16);
if (x_795 == 0)
{
lean_object* x_796; uint8_t x_797; uint8_t x_798; lean_object* x_799; uint64_t x_800; lean_object* x_801; lean_object* x_802; 
lean_dec(x_746);
lean_dec(x_744);
x_796 = lean_ctor_get(x_745, 1);
lean_inc(x_796);
lean_dec(x_745);
x_797 = 1;
x_798 = 2;
x_799 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_799, 0, x_718);
lean_ctor_set_uint8(x_799, 1, x_719);
lean_ctor_set_uint8(x_799, 2, x_720);
lean_ctor_set_uint8(x_799, 3, x_721);
lean_ctor_set_uint8(x_799, 4, x_722);
lean_ctor_set_uint8(x_799, 5, x_723);
lean_ctor_set_uint8(x_799, 6, x_724);
lean_ctor_set_uint8(x_799, 7, x_725);
lean_ctor_set_uint8(x_799, 8, x_726);
lean_ctor_set_uint8(x_799, 9, x_727);
lean_ctor_set_uint8(x_799, 10, x_728);
lean_ctor_set_uint8(x_799, 11, x_729);
lean_ctor_set_uint8(x_799, 12, x_797);
lean_ctor_set_uint8(x_799, 13, x_797);
lean_ctor_set_uint8(x_799, 14, x_798);
lean_ctor_set_uint8(x_799, 15, x_797);
lean_ctor_set_uint8(x_799, 16, x_797);
x_800 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_799);
x_801 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_801, 0, x_799);
lean_ctor_set(x_801, 1, x_709);
lean_ctor_set(x_801, 2, x_710);
lean_ctor_set(x_801, 3, x_711);
lean_ctor_set(x_801, 4, x_712);
lean_ctor_set(x_801, 5, x_713);
lean_ctor_set(x_801, 6, x_714);
lean_ctor_set_uint64(x_801, sizeof(void*)*7, x_800);
lean_ctor_set_uint8(x_801, sizeof(void*)*7 + 8, x_708);
lean_ctor_set_uint8(x_801, sizeof(void*)*7 + 9, x_715);
lean_ctor_set_uint8(x_801, sizeof(void*)*7 + 10, x_716);
x_802 = l_Lean_Meta_inferTypeImp_infer(x_1, x_801, x_3, x_705, x_5, x_796);
if (lean_obj_tag(x_802) == 0)
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
x_804 = lean_ctor_get(x_802, 1);
lean_inc(x_804);
if (lean_is_exclusive(x_802)) {
 lean_ctor_release(x_802, 0);
 lean_ctor_release(x_802, 1);
 x_805 = x_802;
} else {
 lean_dec_ref(x_802);
 x_805 = lean_box(0);
}
if (lean_is_scalar(x_805)) {
 x_806 = lean_alloc_ctor(0, 2, 0);
} else {
 x_806 = x_805;
}
lean_ctor_set(x_806, 0, x_803);
lean_ctor_set(x_806, 1, x_804);
return x_806;
}
else
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_807 = lean_ctor_get(x_802, 0);
lean_inc(x_807);
x_808 = lean_ctor_get(x_802, 1);
lean_inc(x_808);
if (lean_is_exclusive(x_802)) {
 lean_ctor_release(x_802, 0);
 lean_ctor_release(x_802, 1);
 x_809 = x_802;
} else {
 lean_dec_ref(x_802);
 x_809 = lean_box(0);
}
if (lean_is_scalar(x_809)) {
 x_810 = lean_alloc_ctor(1, 2, 0);
} else {
 x_810 = x_809;
}
lean_ctor_set(x_810, 0, x_807);
lean_ctor_set(x_810, 1, x_808);
return x_810;
}
}
else
{
lean_object* x_811; uint8_t x_812; uint8_t x_813; uint8_t x_814; 
x_811 = lean_ctor_get(x_745, 1);
lean_inc(x_811);
lean_dec(x_745);
x_812 = lean_ctor_get_uint8(x_746, 14);
lean_dec(x_746);
x_813 = 2;
x_814 = l_Lean_Meta_instDecidableEqProjReductionKind(x_812, x_813);
if (x_814 == 0)
{
uint8_t x_815; lean_object* x_816; uint64_t x_817; lean_object* x_818; lean_object* x_819; 
lean_dec(x_744);
x_815 = 1;
x_816 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_816, 0, x_718);
lean_ctor_set_uint8(x_816, 1, x_719);
lean_ctor_set_uint8(x_816, 2, x_720);
lean_ctor_set_uint8(x_816, 3, x_721);
lean_ctor_set_uint8(x_816, 4, x_722);
lean_ctor_set_uint8(x_816, 5, x_723);
lean_ctor_set_uint8(x_816, 6, x_724);
lean_ctor_set_uint8(x_816, 7, x_725);
lean_ctor_set_uint8(x_816, 8, x_726);
lean_ctor_set_uint8(x_816, 9, x_727);
lean_ctor_set_uint8(x_816, 10, x_728);
lean_ctor_set_uint8(x_816, 11, x_729);
lean_ctor_set_uint8(x_816, 12, x_815);
lean_ctor_set_uint8(x_816, 13, x_815);
lean_ctor_set_uint8(x_816, 14, x_813);
lean_ctor_set_uint8(x_816, 15, x_815);
lean_ctor_set_uint8(x_816, 16, x_815);
x_817 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_816);
x_818 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_818, 0, x_816);
lean_ctor_set(x_818, 1, x_709);
lean_ctor_set(x_818, 2, x_710);
lean_ctor_set(x_818, 3, x_711);
lean_ctor_set(x_818, 4, x_712);
lean_ctor_set(x_818, 5, x_713);
lean_ctor_set(x_818, 6, x_714);
lean_ctor_set_uint64(x_818, sizeof(void*)*7, x_817);
lean_ctor_set_uint8(x_818, sizeof(void*)*7 + 8, x_708);
lean_ctor_set_uint8(x_818, sizeof(void*)*7 + 9, x_715);
lean_ctor_set_uint8(x_818, sizeof(void*)*7 + 10, x_716);
x_819 = l_Lean_Meta_inferTypeImp_infer(x_1, x_818, x_3, x_705, x_5, x_811);
if (lean_obj_tag(x_819) == 0)
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_819, 1);
lean_inc(x_821);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 x_822 = x_819;
} else {
 lean_dec_ref(x_819);
 x_822 = lean_box(0);
}
if (lean_is_scalar(x_822)) {
 x_823 = lean_alloc_ctor(0, 2, 0);
} else {
 x_823 = x_822;
}
lean_ctor_set(x_823, 0, x_820);
lean_ctor_set(x_823, 1, x_821);
return x_823;
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_824 = lean_ctor_get(x_819, 0);
lean_inc(x_824);
x_825 = lean_ctor_get(x_819, 1);
lean_inc(x_825);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 x_826 = x_819;
} else {
 lean_dec_ref(x_819);
 x_826 = lean_box(0);
}
if (lean_is_scalar(x_826)) {
 x_827 = lean_alloc_ctor(1, 2, 0);
} else {
 x_827 = x_826;
}
lean_ctor_set(x_827, 0, x_824);
lean_ctor_set(x_827, 1, x_825);
return x_827;
}
}
else
{
lean_object* x_828; 
lean_dec(x_714);
lean_dec(x_713);
lean_dec(x_712);
lean_dec(x_711);
lean_dec(x_710);
lean_dec(x_709);
x_828 = l_Lean_Meta_inferTypeImp_infer(x_1, x_744, x_3, x_705, x_5, x_811);
if (lean_obj_tag(x_828) == 0)
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
x_829 = lean_ctor_get(x_828, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_828, 1);
lean_inc(x_830);
if (lean_is_exclusive(x_828)) {
 lean_ctor_release(x_828, 0);
 lean_ctor_release(x_828, 1);
 x_831 = x_828;
} else {
 lean_dec_ref(x_828);
 x_831 = lean_box(0);
}
if (lean_is_scalar(x_831)) {
 x_832 = lean_alloc_ctor(0, 2, 0);
} else {
 x_832 = x_831;
}
lean_ctor_set(x_832, 0, x_829);
lean_ctor_set(x_832, 1, x_830);
return x_832;
}
else
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; 
x_833 = lean_ctor_get(x_828, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_828, 1);
lean_inc(x_834);
if (lean_is_exclusive(x_828)) {
 lean_ctor_release(x_828, 0);
 lean_ctor_release(x_828, 1);
 x_835 = x_828;
} else {
 lean_dec_ref(x_828);
 x_835 = lean_box(0);
}
if (lean_is_scalar(x_835)) {
 x_836 = lean_alloc_ctor(1, 2, 0);
} else {
 x_836 = x_835;
}
lean_ctor_set(x_836, 0, x_833);
lean_ctor_set(x_836, 1, x_834);
return x_836;
}
}
}
}
}
}
}
else
{
lean_object* x_837; uint64_t x_838; uint64_t x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; uint8_t x_843; 
if (lean_is_scalar(x_735)) {
 x_837 = lean_alloc_ctor(0, 0, 17);
} else {
 x_837 = x_735;
}
lean_ctor_set_uint8(x_837, 0, x_718);
lean_ctor_set_uint8(x_837, 1, x_719);
lean_ctor_set_uint8(x_837, 2, x_720);
lean_ctor_set_uint8(x_837, 3, x_721);
lean_ctor_set_uint8(x_837, 4, x_722);
lean_ctor_set_uint8(x_837, 5, x_723);
lean_ctor_set_uint8(x_837, 6, x_724);
lean_ctor_set_uint8(x_837, 7, x_725);
lean_ctor_set_uint8(x_837, 8, x_726);
lean_ctor_set_uint8(x_837, 9, x_736);
lean_ctor_set_uint8(x_837, 10, x_728);
lean_ctor_set_uint8(x_837, 11, x_729);
lean_ctor_set_uint8(x_837, 12, x_730);
lean_ctor_set_uint8(x_837, 13, x_731);
lean_ctor_set_uint8(x_837, 14, x_732);
lean_ctor_set_uint8(x_837, 15, x_733);
lean_ctor_set_uint8(x_837, 16, x_734);
x_838 = l_Lean_Meta_withInferTypeConfig___rarg___closed__1;
x_839 = lean_uint64_lor(x_740, x_838);
lean_inc(x_714);
lean_inc(x_713);
lean_inc(x_712);
lean_inc(x_711);
lean_inc(x_710);
lean_inc(x_709);
if (lean_is_scalar(x_717)) {
 x_840 = lean_alloc_ctor(0, 7, 11);
} else {
 x_840 = x_717;
}
lean_ctor_set(x_840, 0, x_837);
lean_ctor_set(x_840, 1, x_709);
lean_ctor_set(x_840, 2, x_710);
lean_ctor_set(x_840, 3, x_711);
lean_ctor_set(x_840, 4, x_712);
lean_ctor_set(x_840, 5, x_713);
lean_ctor_set(x_840, 6, x_714);
lean_ctor_set_uint64(x_840, sizeof(void*)*7, x_839);
lean_ctor_set_uint8(x_840, sizeof(void*)*7 + 8, x_708);
lean_ctor_set_uint8(x_840, sizeof(void*)*7 + 9, x_715);
lean_ctor_set_uint8(x_840, sizeof(void*)*7 + 10, x_716);
x_841 = l_Lean_Meta_getConfig(x_840, x_3, x_705, x_5, x_6);
x_842 = lean_ctor_get(x_841, 0);
lean_inc(x_842);
x_843 = lean_ctor_get_uint8(x_842, 13);
if (x_843 == 0)
{
lean_object* x_844; uint8_t x_845; uint8_t x_846; lean_object* x_847; uint64_t x_848; lean_object* x_849; lean_object* x_850; 
lean_dec(x_842);
lean_dec(x_840);
x_844 = lean_ctor_get(x_841, 1);
lean_inc(x_844);
lean_dec(x_841);
x_845 = 1;
x_846 = 2;
x_847 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_847, 0, x_718);
lean_ctor_set_uint8(x_847, 1, x_719);
lean_ctor_set_uint8(x_847, 2, x_720);
lean_ctor_set_uint8(x_847, 3, x_721);
lean_ctor_set_uint8(x_847, 4, x_722);
lean_ctor_set_uint8(x_847, 5, x_723);
lean_ctor_set_uint8(x_847, 6, x_724);
lean_ctor_set_uint8(x_847, 7, x_725);
lean_ctor_set_uint8(x_847, 8, x_726);
lean_ctor_set_uint8(x_847, 9, x_736);
lean_ctor_set_uint8(x_847, 10, x_728);
lean_ctor_set_uint8(x_847, 11, x_729);
lean_ctor_set_uint8(x_847, 12, x_845);
lean_ctor_set_uint8(x_847, 13, x_845);
lean_ctor_set_uint8(x_847, 14, x_846);
lean_ctor_set_uint8(x_847, 15, x_845);
lean_ctor_set_uint8(x_847, 16, x_845);
x_848 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_847);
x_849 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_849, 0, x_847);
lean_ctor_set(x_849, 1, x_709);
lean_ctor_set(x_849, 2, x_710);
lean_ctor_set(x_849, 3, x_711);
lean_ctor_set(x_849, 4, x_712);
lean_ctor_set(x_849, 5, x_713);
lean_ctor_set(x_849, 6, x_714);
lean_ctor_set_uint64(x_849, sizeof(void*)*7, x_848);
lean_ctor_set_uint8(x_849, sizeof(void*)*7 + 8, x_708);
lean_ctor_set_uint8(x_849, sizeof(void*)*7 + 9, x_715);
lean_ctor_set_uint8(x_849, sizeof(void*)*7 + 10, x_716);
x_850 = l_Lean_Meta_inferTypeImp_infer(x_1, x_849, x_3, x_705, x_5, x_844);
if (lean_obj_tag(x_850) == 0)
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; 
x_851 = lean_ctor_get(x_850, 0);
lean_inc(x_851);
x_852 = lean_ctor_get(x_850, 1);
lean_inc(x_852);
if (lean_is_exclusive(x_850)) {
 lean_ctor_release(x_850, 0);
 lean_ctor_release(x_850, 1);
 x_853 = x_850;
} else {
 lean_dec_ref(x_850);
 x_853 = lean_box(0);
}
if (lean_is_scalar(x_853)) {
 x_854 = lean_alloc_ctor(0, 2, 0);
} else {
 x_854 = x_853;
}
lean_ctor_set(x_854, 0, x_851);
lean_ctor_set(x_854, 1, x_852);
return x_854;
}
else
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; 
x_855 = lean_ctor_get(x_850, 0);
lean_inc(x_855);
x_856 = lean_ctor_get(x_850, 1);
lean_inc(x_856);
if (lean_is_exclusive(x_850)) {
 lean_ctor_release(x_850, 0);
 lean_ctor_release(x_850, 1);
 x_857 = x_850;
} else {
 lean_dec_ref(x_850);
 x_857 = lean_box(0);
}
if (lean_is_scalar(x_857)) {
 x_858 = lean_alloc_ctor(1, 2, 0);
} else {
 x_858 = x_857;
}
lean_ctor_set(x_858, 0, x_855);
lean_ctor_set(x_858, 1, x_856);
return x_858;
}
}
else
{
uint8_t x_859; 
x_859 = lean_ctor_get_uint8(x_842, 12);
if (x_859 == 0)
{
lean_object* x_860; uint8_t x_861; uint8_t x_862; lean_object* x_863; uint64_t x_864; lean_object* x_865; lean_object* x_866; 
lean_dec(x_842);
lean_dec(x_840);
x_860 = lean_ctor_get(x_841, 1);
lean_inc(x_860);
lean_dec(x_841);
x_861 = 1;
x_862 = 2;
x_863 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_863, 0, x_718);
lean_ctor_set_uint8(x_863, 1, x_719);
lean_ctor_set_uint8(x_863, 2, x_720);
lean_ctor_set_uint8(x_863, 3, x_721);
lean_ctor_set_uint8(x_863, 4, x_722);
lean_ctor_set_uint8(x_863, 5, x_723);
lean_ctor_set_uint8(x_863, 6, x_724);
lean_ctor_set_uint8(x_863, 7, x_725);
lean_ctor_set_uint8(x_863, 8, x_726);
lean_ctor_set_uint8(x_863, 9, x_736);
lean_ctor_set_uint8(x_863, 10, x_728);
lean_ctor_set_uint8(x_863, 11, x_729);
lean_ctor_set_uint8(x_863, 12, x_861);
lean_ctor_set_uint8(x_863, 13, x_861);
lean_ctor_set_uint8(x_863, 14, x_862);
lean_ctor_set_uint8(x_863, 15, x_861);
lean_ctor_set_uint8(x_863, 16, x_861);
x_864 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_863);
x_865 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_865, 0, x_863);
lean_ctor_set(x_865, 1, x_709);
lean_ctor_set(x_865, 2, x_710);
lean_ctor_set(x_865, 3, x_711);
lean_ctor_set(x_865, 4, x_712);
lean_ctor_set(x_865, 5, x_713);
lean_ctor_set(x_865, 6, x_714);
lean_ctor_set_uint64(x_865, sizeof(void*)*7, x_864);
lean_ctor_set_uint8(x_865, sizeof(void*)*7 + 8, x_708);
lean_ctor_set_uint8(x_865, sizeof(void*)*7 + 9, x_715);
lean_ctor_set_uint8(x_865, sizeof(void*)*7 + 10, x_716);
x_866 = l_Lean_Meta_inferTypeImp_infer(x_1, x_865, x_3, x_705, x_5, x_860);
if (lean_obj_tag(x_866) == 0)
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; 
x_867 = lean_ctor_get(x_866, 0);
lean_inc(x_867);
x_868 = lean_ctor_get(x_866, 1);
lean_inc(x_868);
if (lean_is_exclusive(x_866)) {
 lean_ctor_release(x_866, 0);
 lean_ctor_release(x_866, 1);
 x_869 = x_866;
} else {
 lean_dec_ref(x_866);
 x_869 = lean_box(0);
}
if (lean_is_scalar(x_869)) {
 x_870 = lean_alloc_ctor(0, 2, 0);
} else {
 x_870 = x_869;
}
lean_ctor_set(x_870, 0, x_867);
lean_ctor_set(x_870, 1, x_868);
return x_870;
}
else
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; 
x_871 = lean_ctor_get(x_866, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_866, 1);
lean_inc(x_872);
if (lean_is_exclusive(x_866)) {
 lean_ctor_release(x_866, 0);
 lean_ctor_release(x_866, 1);
 x_873 = x_866;
} else {
 lean_dec_ref(x_866);
 x_873 = lean_box(0);
}
if (lean_is_scalar(x_873)) {
 x_874 = lean_alloc_ctor(1, 2, 0);
} else {
 x_874 = x_873;
}
lean_ctor_set(x_874, 0, x_871);
lean_ctor_set(x_874, 1, x_872);
return x_874;
}
}
else
{
uint8_t x_875; 
x_875 = lean_ctor_get_uint8(x_842, 15);
if (x_875 == 0)
{
lean_object* x_876; uint8_t x_877; uint8_t x_878; lean_object* x_879; uint64_t x_880; lean_object* x_881; lean_object* x_882; 
lean_dec(x_842);
lean_dec(x_840);
x_876 = lean_ctor_get(x_841, 1);
lean_inc(x_876);
lean_dec(x_841);
x_877 = 1;
x_878 = 2;
x_879 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_879, 0, x_718);
lean_ctor_set_uint8(x_879, 1, x_719);
lean_ctor_set_uint8(x_879, 2, x_720);
lean_ctor_set_uint8(x_879, 3, x_721);
lean_ctor_set_uint8(x_879, 4, x_722);
lean_ctor_set_uint8(x_879, 5, x_723);
lean_ctor_set_uint8(x_879, 6, x_724);
lean_ctor_set_uint8(x_879, 7, x_725);
lean_ctor_set_uint8(x_879, 8, x_726);
lean_ctor_set_uint8(x_879, 9, x_736);
lean_ctor_set_uint8(x_879, 10, x_728);
lean_ctor_set_uint8(x_879, 11, x_729);
lean_ctor_set_uint8(x_879, 12, x_877);
lean_ctor_set_uint8(x_879, 13, x_877);
lean_ctor_set_uint8(x_879, 14, x_878);
lean_ctor_set_uint8(x_879, 15, x_877);
lean_ctor_set_uint8(x_879, 16, x_877);
x_880 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_879);
x_881 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_881, 0, x_879);
lean_ctor_set(x_881, 1, x_709);
lean_ctor_set(x_881, 2, x_710);
lean_ctor_set(x_881, 3, x_711);
lean_ctor_set(x_881, 4, x_712);
lean_ctor_set(x_881, 5, x_713);
lean_ctor_set(x_881, 6, x_714);
lean_ctor_set_uint64(x_881, sizeof(void*)*7, x_880);
lean_ctor_set_uint8(x_881, sizeof(void*)*7 + 8, x_708);
lean_ctor_set_uint8(x_881, sizeof(void*)*7 + 9, x_715);
lean_ctor_set_uint8(x_881, sizeof(void*)*7 + 10, x_716);
x_882 = l_Lean_Meta_inferTypeImp_infer(x_1, x_881, x_3, x_705, x_5, x_876);
if (lean_obj_tag(x_882) == 0)
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; 
x_883 = lean_ctor_get(x_882, 0);
lean_inc(x_883);
x_884 = lean_ctor_get(x_882, 1);
lean_inc(x_884);
if (lean_is_exclusive(x_882)) {
 lean_ctor_release(x_882, 0);
 lean_ctor_release(x_882, 1);
 x_885 = x_882;
} else {
 lean_dec_ref(x_882);
 x_885 = lean_box(0);
}
if (lean_is_scalar(x_885)) {
 x_886 = lean_alloc_ctor(0, 2, 0);
} else {
 x_886 = x_885;
}
lean_ctor_set(x_886, 0, x_883);
lean_ctor_set(x_886, 1, x_884);
return x_886;
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
x_887 = lean_ctor_get(x_882, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_882, 1);
lean_inc(x_888);
if (lean_is_exclusive(x_882)) {
 lean_ctor_release(x_882, 0);
 lean_ctor_release(x_882, 1);
 x_889 = x_882;
} else {
 lean_dec_ref(x_882);
 x_889 = lean_box(0);
}
if (lean_is_scalar(x_889)) {
 x_890 = lean_alloc_ctor(1, 2, 0);
} else {
 x_890 = x_889;
}
lean_ctor_set(x_890, 0, x_887);
lean_ctor_set(x_890, 1, x_888);
return x_890;
}
}
else
{
uint8_t x_891; 
x_891 = lean_ctor_get_uint8(x_842, 16);
if (x_891 == 0)
{
lean_object* x_892; uint8_t x_893; uint8_t x_894; lean_object* x_895; uint64_t x_896; lean_object* x_897; lean_object* x_898; 
lean_dec(x_842);
lean_dec(x_840);
x_892 = lean_ctor_get(x_841, 1);
lean_inc(x_892);
lean_dec(x_841);
x_893 = 1;
x_894 = 2;
x_895 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_895, 0, x_718);
lean_ctor_set_uint8(x_895, 1, x_719);
lean_ctor_set_uint8(x_895, 2, x_720);
lean_ctor_set_uint8(x_895, 3, x_721);
lean_ctor_set_uint8(x_895, 4, x_722);
lean_ctor_set_uint8(x_895, 5, x_723);
lean_ctor_set_uint8(x_895, 6, x_724);
lean_ctor_set_uint8(x_895, 7, x_725);
lean_ctor_set_uint8(x_895, 8, x_726);
lean_ctor_set_uint8(x_895, 9, x_736);
lean_ctor_set_uint8(x_895, 10, x_728);
lean_ctor_set_uint8(x_895, 11, x_729);
lean_ctor_set_uint8(x_895, 12, x_893);
lean_ctor_set_uint8(x_895, 13, x_893);
lean_ctor_set_uint8(x_895, 14, x_894);
lean_ctor_set_uint8(x_895, 15, x_893);
lean_ctor_set_uint8(x_895, 16, x_893);
x_896 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_895);
x_897 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_897, 0, x_895);
lean_ctor_set(x_897, 1, x_709);
lean_ctor_set(x_897, 2, x_710);
lean_ctor_set(x_897, 3, x_711);
lean_ctor_set(x_897, 4, x_712);
lean_ctor_set(x_897, 5, x_713);
lean_ctor_set(x_897, 6, x_714);
lean_ctor_set_uint64(x_897, sizeof(void*)*7, x_896);
lean_ctor_set_uint8(x_897, sizeof(void*)*7 + 8, x_708);
lean_ctor_set_uint8(x_897, sizeof(void*)*7 + 9, x_715);
lean_ctor_set_uint8(x_897, sizeof(void*)*7 + 10, x_716);
x_898 = l_Lean_Meta_inferTypeImp_infer(x_1, x_897, x_3, x_705, x_5, x_892);
if (lean_obj_tag(x_898) == 0)
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; 
x_899 = lean_ctor_get(x_898, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_898, 1);
lean_inc(x_900);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 lean_ctor_release(x_898, 1);
 x_901 = x_898;
} else {
 lean_dec_ref(x_898);
 x_901 = lean_box(0);
}
if (lean_is_scalar(x_901)) {
 x_902 = lean_alloc_ctor(0, 2, 0);
} else {
 x_902 = x_901;
}
lean_ctor_set(x_902, 0, x_899);
lean_ctor_set(x_902, 1, x_900);
return x_902;
}
else
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; 
x_903 = lean_ctor_get(x_898, 0);
lean_inc(x_903);
x_904 = lean_ctor_get(x_898, 1);
lean_inc(x_904);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 lean_ctor_release(x_898, 1);
 x_905 = x_898;
} else {
 lean_dec_ref(x_898);
 x_905 = lean_box(0);
}
if (lean_is_scalar(x_905)) {
 x_906 = lean_alloc_ctor(1, 2, 0);
} else {
 x_906 = x_905;
}
lean_ctor_set(x_906, 0, x_903);
lean_ctor_set(x_906, 1, x_904);
return x_906;
}
}
else
{
lean_object* x_907; uint8_t x_908; uint8_t x_909; uint8_t x_910; 
x_907 = lean_ctor_get(x_841, 1);
lean_inc(x_907);
lean_dec(x_841);
x_908 = lean_ctor_get_uint8(x_842, 14);
lean_dec(x_842);
x_909 = 2;
x_910 = l_Lean_Meta_instDecidableEqProjReductionKind(x_908, x_909);
if (x_910 == 0)
{
uint8_t x_911; lean_object* x_912; uint64_t x_913; lean_object* x_914; lean_object* x_915; 
lean_dec(x_840);
x_911 = 1;
x_912 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_912, 0, x_718);
lean_ctor_set_uint8(x_912, 1, x_719);
lean_ctor_set_uint8(x_912, 2, x_720);
lean_ctor_set_uint8(x_912, 3, x_721);
lean_ctor_set_uint8(x_912, 4, x_722);
lean_ctor_set_uint8(x_912, 5, x_723);
lean_ctor_set_uint8(x_912, 6, x_724);
lean_ctor_set_uint8(x_912, 7, x_725);
lean_ctor_set_uint8(x_912, 8, x_726);
lean_ctor_set_uint8(x_912, 9, x_736);
lean_ctor_set_uint8(x_912, 10, x_728);
lean_ctor_set_uint8(x_912, 11, x_729);
lean_ctor_set_uint8(x_912, 12, x_911);
lean_ctor_set_uint8(x_912, 13, x_911);
lean_ctor_set_uint8(x_912, 14, x_909);
lean_ctor_set_uint8(x_912, 15, x_911);
lean_ctor_set_uint8(x_912, 16, x_911);
x_913 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_912);
x_914 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_914, 0, x_912);
lean_ctor_set(x_914, 1, x_709);
lean_ctor_set(x_914, 2, x_710);
lean_ctor_set(x_914, 3, x_711);
lean_ctor_set(x_914, 4, x_712);
lean_ctor_set(x_914, 5, x_713);
lean_ctor_set(x_914, 6, x_714);
lean_ctor_set_uint64(x_914, sizeof(void*)*7, x_913);
lean_ctor_set_uint8(x_914, sizeof(void*)*7 + 8, x_708);
lean_ctor_set_uint8(x_914, sizeof(void*)*7 + 9, x_715);
lean_ctor_set_uint8(x_914, sizeof(void*)*7 + 10, x_716);
x_915 = l_Lean_Meta_inferTypeImp_infer(x_1, x_914, x_3, x_705, x_5, x_907);
if (lean_obj_tag(x_915) == 0)
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; 
x_916 = lean_ctor_get(x_915, 0);
lean_inc(x_916);
x_917 = lean_ctor_get(x_915, 1);
lean_inc(x_917);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 lean_ctor_release(x_915, 1);
 x_918 = x_915;
} else {
 lean_dec_ref(x_915);
 x_918 = lean_box(0);
}
if (lean_is_scalar(x_918)) {
 x_919 = lean_alloc_ctor(0, 2, 0);
} else {
 x_919 = x_918;
}
lean_ctor_set(x_919, 0, x_916);
lean_ctor_set(x_919, 1, x_917);
return x_919;
}
else
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; 
x_920 = lean_ctor_get(x_915, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_915, 1);
lean_inc(x_921);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 lean_ctor_release(x_915, 1);
 x_922 = x_915;
} else {
 lean_dec_ref(x_915);
 x_922 = lean_box(0);
}
if (lean_is_scalar(x_922)) {
 x_923 = lean_alloc_ctor(1, 2, 0);
} else {
 x_923 = x_922;
}
lean_ctor_set(x_923, 0, x_920);
lean_ctor_set(x_923, 1, x_921);
return x_923;
}
}
else
{
lean_object* x_924; 
lean_dec(x_714);
lean_dec(x_713);
lean_dec(x_712);
lean_dec(x_711);
lean_dec(x_710);
lean_dec(x_709);
x_924 = l_Lean_Meta_inferTypeImp_infer(x_1, x_840, x_3, x_705, x_5, x_907);
if (lean_obj_tag(x_924) == 0)
{
lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; 
x_925 = lean_ctor_get(x_924, 0);
lean_inc(x_925);
x_926 = lean_ctor_get(x_924, 1);
lean_inc(x_926);
if (lean_is_exclusive(x_924)) {
 lean_ctor_release(x_924, 0);
 lean_ctor_release(x_924, 1);
 x_927 = x_924;
} else {
 lean_dec_ref(x_924);
 x_927 = lean_box(0);
}
if (lean_is_scalar(x_927)) {
 x_928 = lean_alloc_ctor(0, 2, 0);
} else {
 x_928 = x_927;
}
lean_ctor_set(x_928, 0, x_925);
lean_ctor_set(x_928, 1, x_926);
return x_928;
}
else
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; 
x_929 = lean_ctor_get(x_924, 0);
lean_inc(x_929);
x_930 = lean_ctor_get(x_924, 1);
lean_inc(x_930);
if (lean_is_exclusive(x_924)) {
 lean_ctor_release(x_924, 0);
 lean_ctor_release(x_924, 1);
 x_931 = x_924;
} else {
 lean_dec_ref(x_924);
 x_931 = lean_box(0);
}
if (lean_is_scalar(x_931)) {
 x_932 = lean_alloc_ctor(1, 2, 0);
} else {
 x_932 = x_931;
}
lean_ctor_set(x_932, 0, x_929);
lean_ctor_set(x_932, 1, x_930);
return x_932;
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_933; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_933 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1(x_12, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_933;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 2:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
x_1 = x_4;
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
uint8_t x_10; 
x_10 = 0;
return x_10;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_2, x_9);
lean_dec(x_2);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
x_11 = 2;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(x_8, x_3, x_4, x_5, x_6, x_7);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(x_16);
lean_dec(x_16);
x_18 = l_Bool_toLBool(x_17);
x_19 = lean_box(x_18);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(x_20);
lean_dec(x_20);
x_23 = l_Bool_toLBool(x_22);
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
}
case 7:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_1, 2);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_2, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_2, x_29);
lean_dec(x_2);
x_1 = x_26;
x_2 = x_30;
goto _start;
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_26);
lean_dec(x_2);
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_7);
return x_34;
}
}
case 8:
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
lean_dec(x_1);
x_1 = x_35;
goto _start;
}
case 10:
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_1 = x_37;
goto _start;
}
default: 
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_2);
lean_dec(x_1);
x_39 = 2;
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_7);
return x_41;
}
}
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
lean_inc(x_3);
x_9 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(x_10, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_3);
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
x_21 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(x_19, x_2, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_3);
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
x_31 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(x_29, x_2, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_3);
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
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_sub(x_2, x_43);
lean_dec(x_2);
x_1 = x_40;
x_2 = x_44;
goto _start;
}
else
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_40);
lean_dec(x_3);
lean_dec(x_2);
x_46 = 0;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_7);
return x_48;
}
}
case 8:
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_1, 3);
lean_inc(x_49);
lean_dec(x_1);
x_1 = x_49;
goto _start;
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
uint8_t x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = 2;
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_7);
return x_55;
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
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = 2;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_2);
x_11 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(x_12, x_14, x_2, x_3, x_4, x_5, x_13);
lean_dec(x_2);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
case 2:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(x_20, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(x_22, x_24, x_2, x_3, x_4, x_5, x_23);
lean_dec(x_2);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
case 4:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_30, x_31, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(x_33, x_35, x_2, x_3, x_4, x_5, x_34);
lean_dec(x_2);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
case 5:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_unsigned_to_nat(1u);
x_43 = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(x_41, x_42, x_2, x_3, x_4, x_5, x_6);
return x_43;
}
case 7:
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
lean_dec(x_1);
x_1 = x_44;
goto _start;
}
case 8:
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_1, 3);
lean_inc(x_46);
lean_dec(x_1);
x_1 = x_46;
goto _start;
}
case 10:
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
lean_dec(x_1);
x_1 = x_48;
goto _start;
}
case 11:
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_2);
lean_dec(x_1);
x_50 = 2;
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_6);
return x_52;
}
default: 
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
lean_dec(x_1);
x_53 = 0;
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_6);
return x_55;
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
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
case 1:
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 0);
lean_dec(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_dec(x_7);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
default: 
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_27 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_30 = l_Lean_Meta_whnfD(x_28, x_2, x_3, x_4, x_5, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 3)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(x_33, x_2, x_3, x_4, x_5, x_32);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(x_36);
lean_dec(x_36);
x_38 = lean_box(x_37);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(x_39);
lean_dec(x_39);
x_42 = lean_box(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_31);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_30);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_30, 0);
lean_dec(x_45);
x_46 = 0;
x_47 = lean_box(x_46);
lean_ctor_set(x_30, 0, x_47);
return x_30;
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_30, 1);
lean_inc(x_48);
lean_dec(x_30);
x_49 = 0;
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_30);
if (x_52 == 0)
{
return x_30;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_30, 0);
x_54 = lean_ctor_get(x_30, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_30);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_27);
if (x_56 == 0)
{
return x_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_27, 0);
x_58 = lean_ctor_get(x_27, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_27);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_7);
if (x_60 == 0)
{
return x_7;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_7, 0);
x_62 = lean_ctor_get(x_7, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_7);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_2, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_2, x_19);
lean_dec(x_2);
x_1 = x_16;
x_2 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_2);
x_22 = l_Lean_Meta_isPropQuick(x_1, x_3, x_4, x_5, x_6, x_7);
return x_22;
}
}
case 8:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_2, x_24);
if (x_25 == 0)
{
x_1 = x_23;
goto _start;
}
else
{
lean_dec(x_2);
x_1 = x_23;
x_2 = x_24;
goto _start;
}
}
case 10:
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_eq(x_2, x_29);
if (x_30 == 0)
{
x_1 = x_28;
goto _start;
}
else
{
lean_dec(x_2);
x_1 = x_28;
x_2 = x_29;
goto _start;
}
}
default: 
{
lean_object* x_33; 
x_33 = lean_box(0);
x_8 = x_33;
goto block_15;
}
}
block_15:
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_8);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_2, x_9);
lean_dec(x_2);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_1);
x_11 = 2;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Meta_isPropQuick(x_1, x_3, x_4, x_5, x_6, x_7);
return x_14;
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
x_9 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(x_8, x_3, x_4, x_5, x_6, x_7);
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
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_sub(x_2, x_43);
lean_dec(x_2);
x_1 = x_40;
x_2 = x_44;
goto _start;
}
else
{
lean_object* x_46; 
lean_dec(x_2);
x_46 = l_Lean_Meta_isProofQuick(x_40, x_3, x_4, x_5, x_6, x_7);
return x_46;
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
uint8_t x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = 2;
x_52 = lean_box(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_7);
return x_53;
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
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = 2;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_2);
x_11 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(x_12, x_14, x_2, x_3, x_4, x_5, x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
case 2:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(x_20, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(x_22, x_24, x_2, x_3, x_4, x_5, x_23);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
case 4:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_30, x_31, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(x_33, x_35, x_2, x_3, x_4, x_5, x_34);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
case 5:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_unsigned_to_nat(1u);
x_43 = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(x_41, x_42, x_2, x_3, x_4, x_5, x_6);
return x_43;
}
case 6:
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
lean_dec(x_1);
x_1 = x_44;
goto _start;
}
case 8:
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_1, 3);
lean_inc(x_46);
lean_dec(x_1);
x_1 = x_46;
goto _start;
}
case 10:
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
lean_dec(x_1);
x_1 = x_48;
goto _start;
}
case 11:
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_2);
lean_dec(x_1);
x_50 = 2;
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_6);
return x_52;
}
default: 
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
lean_dec(x_1);
x_53 = 0;
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_6);
return x_55;
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
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
case 1:
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 0);
lean_dec(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_dec(x_7);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
default: 
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_27 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_isProp(x_28, x_2, x_3, x_4, x_5, x_29);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_7);
if (x_35 == 0)
{
return x_7;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_7, 0);
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_7);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
lean_dec(x_2);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 2;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
}
case 7:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_1, 2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_2, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_2, x_19);
lean_dec(x_2);
x_1 = x_16;
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
}
case 8:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_1, 3);
x_1 = x_25;
goto _start;
}
case 10:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_1, 1);
x_1 = x_27;
goto _start;
}
default: 
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
x_29 = 2;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
}
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
lean_inc(x_3);
x_9 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(x_10, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_3);
lean_dec(x_10);
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
x_21 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(x_19, x_2, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_3);
lean_dec(x_19);
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
x_31 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(x_29, x_2, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_3);
lean_dec(x_29);
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
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_sub(x_2, x_43);
lean_dec(x_2);
x_1 = x_40;
x_2 = x_44;
goto _start;
}
else
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_40);
lean_dec(x_3);
lean_dec(x_2);
x_46 = 0;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_7);
return x_48;
}
}
case 8:
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_1, 3);
lean_inc(x_49);
lean_dec(x_1);
x_1 = x_49;
goto _start;
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
uint8_t x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = 2;
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_7);
return x_55;
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
lean_inc(x_2);
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(x_9, x_11, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_2);
lean_dec(x_9);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
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
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(x_19, x_21, x_2, x_3, x_4, x_5, x_20);
lean_dec(x_2);
lean_dec(x_19);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_2);
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
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = 1;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
return x_29;
}
case 4:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_30, x_31, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(x_33, x_35, x_2, x_3, x_4, x_5, x_34);
lean_dec(x_2);
lean_dec(x_33);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
case 5:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_unsigned_to_nat(1u);
x_43 = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(x_41, x_42, x_2, x_3, x_4, x_5, x_6);
return x_43;
}
case 6:
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
lean_dec(x_1);
x_44 = 0;
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_6);
return x_46;
}
case 7:
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
lean_dec(x_1);
x_47 = 1;
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_6);
return x_49;
}
case 8:
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_1, 3);
lean_inc(x_50);
lean_dec(x_1);
x_1 = x_50;
goto _start;
}
case 9:
{
uint8_t x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_2);
lean_dec(x_1);
x_52 = 0;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_6);
return x_54;
}
case 10:
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
lean_dec(x_1);
x_1 = x_55;
goto _start;
}
default: 
{
uint8_t x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_2);
lean_dec(x_1);
x_57 = 2;
x_58 = lean_box(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_6);
return x_59;
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
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
case 1:
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 0);
lean_dec(x_19);
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_dec(x_7);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
default: 
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_27 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_whnfD(x_28, x_2, x_3, x_4, x_5, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 3)
{
uint8_t x_32; 
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = 1;
x_35 = lean_box(x_34);
lean_ctor_set(x_30, 0, x_35);
return x_30;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = 1;
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
lean_dec(x_31);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_30, 0);
lean_dec(x_41);
x_42 = 0;
x_43 = lean_box(x_42);
lean_ctor_set(x_30, 0, x_43);
return x_30;
}
else
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_dec(x_30);
x_45 = 0;
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_30);
if (x_48 == 0)
{
return x_30;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_30, 0);
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_30);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_27);
if (x_52 == 0)
{
return x_27;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_27, 0);
x_54 = lean_ctor_get(x_27, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_27);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_7);
if (x_56 == 0)
{
return x_7;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_7, 0);
x_58 = lean_ctor_get(x_7, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_7);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
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
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_push(x_1, x_3);
x_10 = l_Lean_Meta_typeFormerTypeLevel_go(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_typeFormerTypeLevel_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
case 7:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_15 = lean_expr_instantiate_rev(x_12, x_2);
lean_dec(x_12);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_typeFormerTypeLevel_go___lambda__1), 8, 2);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_13);
x_17 = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___rarg(x_11, x_14, x_15, x_16, x_3, x_4, x_5, x_6, x_7);
return x_17;
}
default: 
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Meta_whnfD(x_18, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
switch (lean_obj_tag(x_20)) {
case 3:
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
case 7:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = l_Lean_Meta_typeFormerTypeLevel_go___closed__1;
x_1 = x_20;
x_2 = x_30;
x_7 = x_29;
goto _start;
}
default: 
{
uint8_t x_32; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_19, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_19, 0, x_34);
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_dec(x_19);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
return x_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
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
x_12 = l_Lean_Meta_typeFormerTypeLevel_go___closed__1;
lean_inc(x_3);
x_13 = l_Lean_Meta_typeFormerTypeLevel_go(x_1, x_12, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_3, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_17, 1);
lean_dec(x_20);
lean_ctor_set(x_17, 1, x_11);
x_21 = lean_st_ref_set(x_3, x_17, x_18);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 2);
x_28 = lean_ctor_get(x_17, 3);
x_29 = lean_ctor_get(x_17, 4);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_11);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set(x_30, 4, x_29);
x_31 = lean_st_ref_set(x_3, x_30, x_18);
lean_dec(x_3);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_14);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_13, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_dec(x_13);
x_37 = lean_st_ref_take(x_3, x_36);
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
lean_ctor_set(x_38, 1, x_11);
x_42 = lean_st_ref_set(x_3, x_38, x_39);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 0, x_35);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_38, 0);
x_48 = lean_ctor_get(x_38, 2);
x_49 = lean_ctor_get(x_38, 3);
x_50 = lean_ctor_get(x_38, 4);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_38);
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_11);
lean_ctor_set(x_51, 2, x_48);
lean_ctor_set(x_51, 3, x_49);
lean_ctor_set(x_51, 4, x_50);
x_52 = lean_st_ref_set(x_3, x_51, x_39);
lean_dec(x_3);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
 lean_ctor_set_tag(x_55, 1);
}
lean_ctor_set(x_55, 0, x_35);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_7);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_7);
lean_ctor_set(x_57, 1, x_6);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_7, 0);
lean_inc(x_58);
lean_dec(x_7);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_6);
return x_60;
}
}
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
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = 0;
x_12 = lean_box(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_dec(x_7);
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Meta_isPropFormerType___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
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
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_level_eq(x_6, x_7);
return x_8;
}
}
}
}
static lean_object* _init_l_Lean_Meta_isPropFormerType___closed__1() {
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
x_10 = l_Lean_Meta_isPropFormerType___closed__1;
x_11 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Meta_isPropFormerType___spec__1(x_9, x_10);
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
x_15 = l_Lean_Meta_isPropFormerType___closed__1;
x_16 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Meta_isPropFormerType___spec__1(x_13, x_15);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Meta_isPropFormerType___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Meta_isPropFormerType___spec__1(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_arrowDomainsN___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = lean_infer_type(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_13, x_2, x_15);
x_2 = x_18;
x_3 = x_19;
x_8 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_arrowDomainsN___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
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
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_Meta_arrowDomainsN___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at_Lean_Meta_arrowDomainsN___spec__3(x_2, x_1, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Meta_arrowDomainsN___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasFVar(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 0;
return x_4;
}
else
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Expr_fvar___override(x_5);
x_7 = l_Array_contains___at_Lean_Meta_arrowDomainsN___spec__2(x_1, x_6);
lean_dec(x_6);
return x_7;
}
case 5:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Meta_arrowDomainsN___spec__4(x_1, x_8);
if (x_10 == 0)
{
x_2 = x_9;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_9);
x_12 = 1;
return x_12;
}
}
case 6:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Meta_arrowDomainsN___spec__4(x_1, x_13);
if (x_15 == 0)
{
x_2 = x_14;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_14);
x_17 = 1;
return x_17;
}
}
case 7:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Meta_arrowDomainsN___spec__4(x_1, x_18);
if (x_20 == 0)
{
x_2 = x_19;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_19);
x_22 = 1;
return x_22;
}
}
case 8:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 3);
lean_inc(x_25);
lean_dec(x_2);
x_26 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Meta_arrowDomainsN___spec__4(x_1, x_23);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Meta_arrowDomainsN___spec__4(x_1, x_24);
if (x_27 == 0)
{
x_2 = x_25;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_25);
x_29 = 1;
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_25);
lean_dec(x_24);
x_30 = 1;
return x_30;
}
}
case 10:
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_dec(x_2);
x_2 = x_31;
goto _start;
}
case 11:
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_2, 2);
lean_inc(x_33);
lean_dec(x_2);
x_2 = x_33;
goto _start;
}
default: 
{
uint8_t x_35; 
lean_dec(x_2);
x_35 = 0;
return x_35;
}
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected dependent type ", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" in ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_8);
x_16 = lean_array_uget(x_5, x_7);
lean_inc(x_16);
x_17 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Meta_arrowDomainsN___spec__4(x_2, x_16);
if (x_17 == 0)
{
size_t x_18; size_t x_19; lean_object* x_20; 
lean_dec(x_16);
x_18 = 1;
x_19 = lean_usize_add(x_7, x_18);
x_20 = lean_box(0);
x_7 = x_19;
x_8 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_22 = l_Lean_MessageData_ofExpr(x_16);
x_23 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__2;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__4;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_MessageData_ofExpr(x_1);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_30, x_9, x_10, x_11, x_12, x_13);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_array_size(x_1);
x_10 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_arrowDomainsN___spec__1(x_9, x_10, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_array_size(x_12);
x_16 = lean_box(0);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5(x_2, x_1, x_12, x_14, x_12, x_15, x_10, x_16, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_12);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_12);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_arrowDomainsN___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" does not have ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_arrowDomainsN___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" parameters", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_arrowDomainsN___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_arrowDomainsN___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_12 = l_Lean_MessageData_ofExpr(x_1);
x_13 = l_Lean_Meta_arrowDomainsN___lambda__2___closed__2;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Meta_arrowDomainsN___lambda__2___closed__4;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_MessageData_ofFormat(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Meta_arrowDomainsN___lambda__2___closed__6;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_22, x_5, x_6, x_7, x_8, x_9);
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
lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
x_28 = lean_box(0);
x_29 = l_Lean_Meta_arrowDomainsN___lambda__1(x_3, x_1, x_28, x_5, x_6, x_7, x_8, x_9);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
lean_inc(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lambda__2___boxed), 9, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_1);
x_10 = 0;
x_11 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_2, x_8, x_9, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_arrowDomainsN___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_arrowDomainsN___spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_arrowDomainsN___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_arrowDomainsN___spec__3(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_Meta_arrowDomainsN___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_Meta_arrowDomainsN___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at_Lean_Meta_arrowDomainsN___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Meta_arrowDomainsN___spec__4(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_arrowDomainsN___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_arrowDomainsN___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8___closed__1 = _init_l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8___closed__1();
lean_mark_persistent(l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8___closed__1);
l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8___closed__2 = _init_l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8___closed__2();
lean_mark_persistent(l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8___closed__2);
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
l_Lean_Expr_instantiateBetaRevRange_visit___closed__8 = _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__8();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange_visit___closed__8);
l_Lean_Expr_instantiateBetaRevRange_visit___closed__9 = _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__9();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange_visit___closed__9);
l_Lean_Expr_instantiateBetaRevRange_visit___closed__10 = _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__10();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange_visit___closed__10);
l_Lean_Expr_instantiateBetaRevRange_visit___closed__11 = _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__11();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange_visit___closed__11);
l_Lean_Expr_instantiateBetaRevRange_visit___closed__12 = _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__12();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange_visit___closed__12);
l_Lean_Expr_instantiateBetaRevRange_visit___closed__13 = _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__13();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange_visit___closed__13);
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
l_Lean_Expr_instantiateBetaRevRange___closed__8 = _init_l_Lean_Expr_instantiateBetaRevRange___closed__8();
lean_mark_persistent(l_Lean_Expr_instantiateBetaRevRange___closed__8);
l_Lean_Meta_throwFunctionExpected___rarg___closed__1 = _init_l_Lean_Meta_throwFunctionExpected___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_throwFunctionExpected___rarg___closed__1);
l_Lean_Meta_throwFunctionExpected___rarg___closed__2 = _init_l_Lean_Meta_throwFunctionExpected___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_throwFunctionExpected___rarg___closed__2);
l_Lean_Meta_throwFunctionExpected___rarg___closed__3 = _init_l_Lean_Meta_throwFunctionExpected___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_throwFunctionExpected___rarg___closed__3);
l_Lean_Meta_throwFunctionExpected___rarg___closed__4 = _init_l_Lean_Meta_throwFunctionExpected___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_throwFunctionExpected___rarg___closed__4);
l_Lean_Meta_throwIncorrectNumberOfLevels___rarg___closed__1 = _init_l_Lean_Meta_throwIncorrectNumberOfLevels___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_throwIncorrectNumberOfLevels___rarg___closed__1);
l_Lean_Meta_throwIncorrectNumberOfLevels___rarg___closed__2 = _init_l_Lean_Meta_throwIncorrectNumberOfLevels___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_throwIncorrectNumberOfLevels___rarg___closed__2);
l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__1 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__1);
l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2);
l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__3 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__3();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__3);
l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4);
l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lambda__1___closed__1 = _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lambda__1___closed__1);
l_Lean_Meta_throwTypeExcepted___rarg___closed__1 = _init_l_Lean_Meta_throwTypeExcepted___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_throwTypeExcepted___rarg___closed__1);
l_Lean_Meta_throwTypeExcepted___rarg___closed__2 = _init_l_Lean_Meta_throwTypeExcepted___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_throwTypeExcepted___rarg___closed__2);
l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1 = _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1();
lean_mark_persistent(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1);
l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1 = _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1();
lean_mark_persistent(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1);
l_Lean_Meta_throwUnknownMVar___rarg___closed__1 = _init_l_Lean_Meta_throwUnknownMVar___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_throwUnknownMVar___rarg___closed__1);
l_Lean_Meta_throwUnknownMVar___rarg___closed__2 = _init_l_Lean_Meta_throwUnknownMVar___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_throwUnknownMVar___rarg___closed__2);
l_Lean_Meta_throwUnknownMVar___rarg___closed__3 = _init_l_Lean_Meta_throwUnknownMVar___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_throwUnknownMVar___rarg___closed__3);
l_Lean_Meta_throwUnknownMVar___rarg___closed__4 = _init_l_Lean_Meta_throwUnknownMVar___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_throwUnknownMVar___rarg___closed__4);
l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___closed__1();
l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___closed__2 = _init_l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___closed__2();
l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5___closed__1);
l_Lean_Meta_withInferTypeConfig___rarg___closed__1 = _init_l_Lean_Meta_withInferTypeConfig___rarg___closed__1();
l_Lean_Meta_inferTypeImp_infer___closed__1 = _init_l_Lean_Meta_inferTypeImp_infer___closed__1();
lean_mark_persistent(l_Lean_Meta_inferTypeImp_infer___closed__1);
l_Lean_Meta_inferTypeImp_infer___closed__2 = _init_l_Lean_Meta_inferTypeImp_infer___closed__2();
lean_mark_persistent(l_Lean_Meta_inferTypeImp_infer___closed__2);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__2);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__3);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__4);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__5);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__6);
l_Lean_Meta_typeFormerTypeLevel_go___closed__1 = _init_l_Lean_Meta_typeFormerTypeLevel_go___closed__1();
lean_mark_persistent(l_Lean_Meta_typeFormerTypeLevel_go___closed__1);
l_Lean_Meta_isPropFormerType___closed__1 = _init_l_Lean_Meta_isPropFormerType___closed__1();
lean_mark_persistent(l_Lean_Meta_isPropFormerType___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__4);
l_Lean_Meta_arrowDomainsN___lambda__2___closed__1 = _init_l_Lean_Meta_arrowDomainsN___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_arrowDomainsN___lambda__2___closed__1);
l_Lean_Meta_arrowDomainsN___lambda__2___closed__2 = _init_l_Lean_Meta_arrowDomainsN___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_arrowDomainsN___lambda__2___closed__2);
l_Lean_Meta_arrowDomainsN___lambda__2___closed__3 = _init_l_Lean_Meta_arrowDomainsN___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_arrowDomainsN___lambda__2___closed__3);
l_Lean_Meta_arrowDomainsN___lambda__2___closed__4 = _init_l_Lean_Meta_arrowDomainsN___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_arrowDomainsN___lambda__2___closed__4);
l_Lean_Meta_arrowDomainsN___lambda__2___closed__5 = _init_l_Lean_Meta_arrowDomainsN___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_arrowDomainsN___lambda__2___closed__5);
l_Lean_Meta_arrowDomainsN___lambda__2___closed__6 = _init_l_Lean_Meta_arrowDomainsN___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_arrowDomainsN___lambda__2___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
