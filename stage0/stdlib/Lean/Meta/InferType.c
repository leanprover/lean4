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
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownMVar___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
lean_dec(x_114);
x_138 = lean_nat_sub(x_113, x_5);
lean_dec(x_113);
x_139 = lean_nat_sub(x_2, x_138);
lean_dec(x_138);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_nat_sub(x_139, x_140);
lean_dec(x_139);
x_142 = l_Lean_instInhabitedExpr;
x_143 = lean_array_get(x_142, x_3, x_141);
lean_dec(x_141);
x_144 = lean_unsigned_to_nat(0u);
x_145 = lean_expr_lift_loose_bvars(x_143, x_144, x_5);
lean_dec(x_5);
lean_dec(x_143);
x_146 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_108);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_147 = lean_nat_add(x_91, x_140);
lean_dec(x_91);
lean_inc(x_145);
x_148 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_148, 0, x_9);
lean_ctor_set(x_148, 1, x_145);
lean_ctor_set(x_148, 2, x_108);
x_149 = lean_array_uset(x_92, x_107, x_148);
x_150 = lean_unsigned_to_nat(4u);
x_151 = lean_nat_mul(x_147, x_150);
x_152 = lean_unsigned_to_nat(3u);
x_153 = lean_nat_div(x_151, x_152);
lean_dec(x_151);
x_154 = lean_array_get_size(x_149);
x_155 = lean_nat_dec_le(x_153, x_154);
lean_dec(x_154);
lean_dec(x_153);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_149);
lean_ctor_set(x_6, 1, x_156);
lean_ctor_set(x_6, 0, x_147);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_145);
lean_ctor_set(x_157, 1, x_6);
return x_157;
}
else
{
lean_object* x_158; 
lean_ctor_set(x_6, 1, x_149);
lean_ctor_set(x_6, 0, x_147);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_145);
lean_ctor_set(x_158, 1, x_6);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_159 = lean_box(0);
x_160 = lean_array_uset(x_92, x_107, x_159);
lean_inc(x_145);
x_161 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_145, x_108);
x_162 = lean_array_uset(x_160, x_107, x_161);
lean_ctor_set(x_6, 1, x_162);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_145);
lean_ctor_set(x_163, 1, x_6);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
lean_dec(x_6);
x_164 = lean_ctor_get(x_4, 0);
lean_inc(x_164);
lean_dec(x_4);
x_165 = lean_nat_sub(x_2, x_1);
x_166 = lean_nat_add(x_5, x_165);
x_167 = lean_nat_dec_lt(x_164, x_166);
lean_dec(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
lean_dec(x_5);
x_168 = lean_nat_sub(x_164, x_165);
lean_dec(x_165);
lean_dec(x_164);
x_169 = l_Lean_Expr_bvar___override(x_168);
x_170 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_108);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_171 = lean_unsigned_to_nat(1u);
x_172 = lean_nat_add(x_91, x_171);
lean_dec(x_91);
lean_inc(x_169);
x_173 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_173, 0, x_9);
lean_ctor_set(x_173, 1, x_169);
lean_ctor_set(x_173, 2, x_108);
x_174 = lean_array_uset(x_92, x_107, x_173);
x_175 = lean_unsigned_to_nat(4u);
x_176 = lean_nat_mul(x_172, x_175);
x_177 = lean_unsigned_to_nat(3u);
x_178 = lean_nat_div(x_176, x_177);
lean_dec(x_176);
x_179 = lean_array_get_size(x_174);
x_180 = lean_nat_dec_le(x_178, x_179);
lean_dec(x_179);
lean_dec(x_178);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_174);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_172);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_169);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_172);
lean_ctor_set(x_184, 1, x_174);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_169);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_186 = lean_box(0);
x_187 = lean_array_uset(x_92, x_107, x_186);
lean_inc(x_169);
x_188 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_169, x_108);
x_189 = lean_array_uset(x_187, x_107, x_188);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_91);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_169);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
lean_dec(x_165);
x_192 = lean_nat_sub(x_164, x_5);
lean_dec(x_164);
x_193 = lean_nat_sub(x_2, x_192);
lean_dec(x_192);
x_194 = lean_unsigned_to_nat(1u);
x_195 = lean_nat_sub(x_193, x_194);
lean_dec(x_193);
x_196 = l_Lean_instInhabitedExpr;
x_197 = lean_array_get(x_196, x_3, x_195);
lean_dec(x_195);
x_198 = lean_unsigned_to_nat(0u);
x_199 = lean_expr_lift_loose_bvars(x_197, x_198, x_5);
lean_dec(x_5);
lean_dec(x_197);
x_200 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_108);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_201 = lean_nat_add(x_91, x_194);
lean_dec(x_91);
lean_inc(x_199);
x_202 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_202, 0, x_9);
lean_ctor_set(x_202, 1, x_199);
lean_ctor_set(x_202, 2, x_108);
x_203 = lean_array_uset(x_92, x_107, x_202);
x_204 = lean_unsigned_to_nat(4u);
x_205 = lean_nat_mul(x_201, x_204);
x_206 = lean_unsigned_to_nat(3u);
x_207 = lean_nat_div(x_205, x_206);
lean_dec(x_205);
x_208 = lean_array_get_size(x_203);
x_209 = lean_nat_dec_le(x_207, x_208);
lean_dec(x_208);
lean_dec(x_207);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_203);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_201);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_199);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_201);
lean_ctor_set(x_213, 1, x_203);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_199);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_215 = lean_box(0);
x_216 = lean_array_uset(x_92, x_107, x_215);
lean_inc(x_199);
x_217 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_199, x_108);
x_218 = lean_array_uset(x_216, x_107, x_217);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_91);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_199);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
}
case 1:
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_5);
lean_dec(x_4);
x_221 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__9;
x_222 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8(x_221, x_6);
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
lean_object* x_224; uint8_t x_225; 
x_224 = lean_ctor_get(x_222, 1);
x_225 = !lean_is_exclusive(x_224);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; size_t x_230; size_t x_231; size_t x_232; lean_object* x_233; uint8_t x_234; 
x_226 = lean_ctor_get(x_222, 0);
x_227 = lean_ctor_get(x_224, 0);
x_228 = lean_ctor_get(x_224, 1);
x_229 = lean_array_get_size(x_228);
x_230 = lean_usize_of_nat(x_229);
lean_dec(x_229);
x_231 = lean_usize_sub(x_230, x_105);
x_232 = lean_usize_land(x_103, x_231);
x_233 = lean_array_uget(x_228, x_232);
x_234 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_235 = lean_unsigned_to_nat(1u);
x_236 = lean_nat_add(x_227, x_235);
lean_dec(x_227);
lean_inc(x_226);
x_237 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_237, 0, x_9);
lean_ctor_set(x_237, 1, x_226);
lean_ctor_set(x_237, 2, x_233);
x_238 = lean_array_uset(x_228, x_232, x_237);
x_239 = lean_unsigned_to_nat(4u);
x_240 = lean_nat_mul(x_236, x_239);
x_241 = lean_unsigned_to_nat(3u);
x_242 = lean_nat_div(x_240, x_241);
lean_dec(x_240);
x_243 = lean_array_get_size(x_238);
x_244 = lean_nat_dec_le(x_242, x_243);
lean_dec(x_243);
lean_dec(x_242);
if (x_244 == 0)
{
lean_object* x_245; 
x_245 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_238);
lean_ctor_set(x_224, 1, x_245);
lean_ctor_set(x_224, 0, x_236);
return x_222;
}
else
{
lean_ctor_set(x_224, 1, x_238);
lean_ctor_set(x_224, 0, x_236);
return x_222;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_box(0);
x_247 = lean_array_uset(x_228, x_232, x_246);
lean_inc(x_226);
x_248 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_226, x_233);
x_249 = lean_array_uset(x_247, x_232, x_248);
lean_ctor_set(x_224, 1, x_249);
return x_222;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; size_t x_254; size_t x_255; size_t x_256; lean_object* x_257; uint8_t x_258; 
x_250 = lean_ctor_get(x_222, 0);
x_251 = lean_ctor_get(x_224, 0);
x_252 = lean_ctor_get(x_224, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_224);
x_253 = lean_array_get_size(x_252);
x_254 = lean_usize_of_nat(x_253);
lean_dec(x_253);
x_255 = lean_usize_sub(x_254, x_105);
x_256 = lean_usize_land(x_103, x_255);
x_257 = lean_array_uget(x_252, x_256);
x_258 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_259 = lean_unsigned_to_nat(1u);
x_260 = lean_nat_add(x_251, x_259);
lean_dec(x_251);
lean_inc(x_250);
x_261 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_261, 0, x_9);
lean_ctor_set(x_261, 1, x_250);
lean_ctor_set(x_261, 2, x_257);
x_262 = lean_array_uset(x_252, x_256, x_261);
x_263 = lean_unsigned_to_nat(4u);
x_264 = lean_nat_mul(x_260, x_263);
x_265 = lean_unsigned_to_nat(3u);
x_266 = lean_nat_div(x_264, x_265);
lean_dec(x_264);
x_267 = lean_array_get_size(x_262);
x_268 = lean_nat_dec_le(x_266, x_267);
lean_dec(x_267);
lean_dec(x_266);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; 
x_269 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_262);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_260);
lean_ctor_set(x_270, 1, x_269);
lean_ctor_set(x_222, 1, x_270);
return x_222;
}
else
{
lean_object* x_271; 
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_260);
lean_ctor_set(x_271, 1, x_262);
lean_ctor_set(x_222, 1, x_271);
return x_222;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_272 = lean_box(0);
x_273 = lean_array_uset(x_252, x_256, x_272);
lean_inc(x_250);
x_274 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_250, x_257);
x_275 = lean_array_uset(x_273, x_256, x_274);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_251);
lean_ctor_set(x_276, 1, x_275);
lean_ctor_set(x_222, 1, x_276);
return x_222;
}
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; size_t x_283; size_t x_284; size_t x_285; lean_object* x_286; uint8_t x_287; 
x_277 = lean_ctor_get(x_222, 1);
x_278 = lean_ctor_get(x_222, 0);
lean_inc(x_277);
lean_inc(x_278);
lean_dec(x_222);
x_279 = lean_ctor_get(x_277, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_277, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_281 = x_277;
} else {
 lean_dec_ref(x_277);
 x_281 = lean_box(0);
}
x_282 = lean_array_get_size(x_280);
x_283 = lean_usize_of_nat(x_282);
lean_dec(x_282);
x_284 = lean_usize_sub(x_283, x_105);
x_285 = lean_usize_land(x_103, x_284);
x_286 = lean_array_uget(x_280, x_285);
x_287 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_286);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_288 = lean_unsigned_to_nat(1u);
x_289 = lean_nat_add(x_279, x_288);
lean_dec(x_279);
lean_inc(x_278);
x_290 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_290, 0, x_9);
lean_ctor_set(x_290, 1, x_278);
lean_ctor_set(x_290, 2, x_286);
x_291 = lean_array_uset(x_280, x_285, x_290);
x_292 = lean_unsigned_to_nat(4u);
x_293 = lean_nat_mul(x_289, x_292);
x_294 = lean_unsigned_to_nat(3u);
x_295 = lean_nat_div(x_293, x_294);
lean_dec(x_293);
x_296 = lean_array_get_size(x_291);
x_297 = lean_nat_dec_le(x_295, x_296);
lean_dec(x_296);
lean_dec(x_295);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_291);
if (lean_is_scalar(x_281)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_281;
}
lean_ctor_set(x_299, 0, x_289);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_278);
lean_ctor_set(x_300, 1, x_299);
return x_300;
}
else
{
lean_object* x_301; lean_object* x_302; 
if (lean_is_scalar(x_281)) {
 x_301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_301 = x_281;
}
lean_ctor_set(x_301, 0, x_289);
lean_ctor_set(x_301, 1, x_291);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_278);
lean_ctor_set(x_302, 1, x_301);
return x_302;
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_303 = lean_box(0);
x_304 = lean_array_uset(x_280, x_285, x_303);
lean_inc(x_278);
x_305 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_278, x_286);
x_306 = lean_array_uset(x_304, x_285, x_305);
if (lean_is_scalar(x_281)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_281;
}
lean_ctor_set(x_307, 0, x_279);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_278);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
case 2:
{
lean_object* x_309; lean_object* x_310; uint8_t x_311; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_5);
lean_dec(x_4);
x_309 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__10;
x_310 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8(x_309, x_6);
x_311 = !lean_is_exclusive(x_310);
if (x_311 == 0)
{
lean_object* x_312; uint8_t x_313; 
x_312 = lean_ctor_get(x_310, 1);
x_313 = !lean_is_exclusive(x_312);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; size_t x_318; size_t x_319; size_t x_320; lean_object* x_321; uint8_t x_322; 
x_314 = lean_ctor_get(x_310, 0);
x_315 = lean_ctor_get(x_312, 0);
x_316 = lean_ctor_get(x_312, 1);
x_317 = lean_array_get_size(x_316);
x_318 = lean_usize_of_nat(x_317);
lean_dec(x_317);
x_319 = lean_usize_sub(x_318, x_105);
x_320 = lean_usize_land(x_103, x_319);
x_321 = lean_array_uget(x_316, x_320);
x_322 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_321);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; 
x_323 = lean_unsigned_to_nat(1u);
x_324 = lean_nat_add(x_315, x_323);
lean_dec(x_315);
lean_inc(x_314);
x_325 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_325, 0, x_9);
lean_ctor_set(x_325, 1, x_314);
lean_ctor_set(x_325, 2, x_321);
x_326 = lean_array_uset(x_316, x_320, x_325);
x_327 = lean_unsigned_to_nat(4u);
x_328 = lean_nat_mul(x_324, x_327);
x_329 = lean_unsigned_to_nat(3u);
x_330 = lean_nat_div(x_328, x_329);
lean_dec(x_328);
x_331 = lean_array_get_size(x_326);
x_332 = lean_nat_dec_le(x_330, x_331);
lean_dec(x_331);
lean_dec(x_330);
if (x_332 == 0)
{
lean_object* x_333; 
x_333 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_326);
lean_ctor_set(x_312, 1, x_333);
lean_ctor_set(x_312, 0, x_324);
return x_310;
}
else
{
lean_ctor_set(x_312, 1, x_326);
lean_ctor_set(x_312, 0, x_324);
return x_310;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_334 = lean_box(0);
x_335 = lean_array_uset(x_316, x_320, x_334);
lean_inc(x_314);
x_336 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_314, x_321);
x_337 = lean_array_uset(x_335, x_320, x_336);
lean_ctor_set(x_312, 1, x_337);
return x_310;
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; size_t x_342; size_t x_343; size_t x_344; lean_object* x_345; uint8_t x_346; 
x_338 = lean_ctor_get(x_310, 0);
x_339 = lean_ctor_get(x_312, 0);
x_340 = lean_ctor_get(x_312, 1);
lean_inc(x_340);
lean_inc(x_339);
lean_dec(x_312);
x_341 = lean_array_get_size(x_340);
x_342 = lean_usize_of_nat(x_341);
lean_dec(x_341);
x_343 = lean_usize_sub(x_342, x_105);
x_344 = lean_usize_land(x_103, x_343);
x_345 = lean_array_uget(x_340, x_344);
x_346 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_345);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; 
x_347 = lean_unsigned_to_nat(1u);
x_348 = lean_nat_add(x_339, x_347);
lean_dec(x_339);
lean_inc(x_338);
x_349 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_349, 0, x_9);
lean_ctor_set(x_349, 1, x_338);
lean_ctor_set(x_349, 2, x_345);
x_350 = lean_array_uset(x_340, x_344, x_349);
x_351 = lean_unsigned_to_nat(4u);
x_352 = lean_nat_mul(x_348, x_351);
x_353 = lean_unsigned_to_nat(3u);
x_354 = lean_nat_div(x_352, x_353);
lean_dec(x_352);
x_355 = lean_array_get_size(x_350);
x_356 = lean_nat_dec_le(x_354, x_355);
lean_dec(x_355);
lean_dec(x_354);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; 
x_357 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_350);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_348);
lean_ctor_set(x_358, 1, x_357);
lean_ctor_set(x_310, 1, x_358);
return x_310;
}
else
{
lean_object* x_359; 
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_348);
lean_ctor_set(x_359, 1, x_350);
lean_ctor_set(x_310, 1, x_359);
return x_310;
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_360 = lean_box(0);
x_361 = lean_array_uset(x_340, x_344, x_360);
lean_inc(x_338);
x_362 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_338, x_345);
x_363 = lean_array_uset(x_361, x_344, x_362);
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_339);
lean_ctor_set(x_364, 1, x_363);
lean_ctor_set(x_310, 1, x_364);
return x_310;
}
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; size_t x_371; size_t x_372; size_t x_373; lean_object* x_374; uint8_t x_375; 
x_365 = lean_ctor_get(x_310, 1);
x_366 = lean_ctor_get(x_310, 0);
lean_inc(x_365);
lean_inc(x_366);
lean_dec(x_310);
x_367 = lean_ctor_get(x_365, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_365, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_369 = x_365;
} else {
 lean_dec_ref(x_365);
 x_369 = lean_box(0);
}
x_370 = lean_array_get_size(x_368);
x_371 = lean_usize_of_nat(x_370);
lean_dec(x_370);
x_372 = lean_usize_sub(x_371, x_105);
x_373 = lean_usize_land(x_103, x_372);
x_374 = lean_array_uget(x_368, x_373);
x_375 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_374);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_376 = lean_unsigned_to_nat(1u);
x_377 = lean_nat_add(x_367, x_376);
lean_dec(x_367);
lean_inc(x_366);
x_378 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_378, 0, x_9);
lean_ctor_set(x_378, 1, x_366);
lean_ctor_set(x_378, 2, x_374);
x_379 = lean_array_uset(x_368, x_373, x_378);
x_380 = lean_unsigned_to_nat(4u);
x_381 = lean_nat_mul(x_377, x_380);
x_382 = lean_unsigned_to_nat(3u);
x_383 = lean_nat_div(x_381, x_382);
lean_dec(x_381);
x_384 = lean_array_get_size(x_379);
x_385 = lean_nat_dec_le(x_383, x_384);
lean_dec(x_384);
lean_dec(x_383);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_379);
if (lean_is_scalar(x_369)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_369;
}
lean_ctor_set(x_387, 0, x_377);
lean_ctor_set(x_387, 1, x_386);
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_366);
lean_ctor_set(x_388, 1, x_387);
return x_388;
}
else
{
lean_object* x_389; lean_object* x_390; 
if (lean_is_scalar(x_369)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_369;
}
lean_ctor_set(x_389, 0, x_377);
lean_ctor_set(x_389, 1, x_379);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_366);
lean_ctor_set(x_390, 1, x_389);
return x_390;
}
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_391 = lean_box(0);
x_392 = lean_array_uset(x_368, x_373, x_391);
lean_inc(x_366);
x_393 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_366, x_374);
x_394 = lean_array_uset(x_392, x_373, x_393);
if (lean_is_scalar(x_369)) {
 x_395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_395 = x_369;
}
lean_ctor_set(x_395, 0, x_367);
lean_ctor_set(x_395, 1, x_394);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_366);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
}
case 3:
{
lean_object* x_397; lean_object* x_398; uint8_t x_399; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_5);
lean_dec(x_4);
x_397 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__11;
x_398 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8(x_397, x_6);
x_399 = !lean_is_exclusive(x_398);
if (x_399 == 0)
{
lean_object* x_400; uint8_t x_401; 
x_400 = lean_ctor_get(x_398, 1);
x_401 = !lean_is_exclusive(x_400);
if (x_401 == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; size_t x_406; size_t x_407; size_t x_408; lean_object* x_409; uint8_t x_410; 
x_402 = lean_ctor_get(x_398, 0);
x_403 = lean_ctor_get(x_400, 0);
x_404 = lean_ctor_get(x_400, 1);
x_405 = lean_array_get_size(x_404);
x_406 = lean_usize_of_nat(x_405);
lean_dec(x_405);
x_407 = lean_usize_sub(x_406, x_105);
x_408 = lean_usize_land(x_103, x_407);
x_409 = lean_array_uget(x_404, x_408);
x_410 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_409);
if (x_410 == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; 
x_411 = lean_unsigned_to_nat(1u);
x_412 = lean_nat_add(x_403, x_411);
lean_dec(x_403);
lean_inc(x_402);
x_413 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_413, 0, x_9);
lean_ctor_set(x_413, 1, x_402);
lean_ctor_set(x_413, 2, x_409);
x_414 = lean_array_uset(x_404, x_408, x_413);
x_415 = lean_unsigned_to_nat(4u);
x_416 = lean_nat_mul(x_412, x_415);
x_417 = lean_unsigned_to_nat(3u);
x_418 = lean_nat_div(x_416, x_417);
lean_dec(x_416);
x_419 = lean_array_get_size(x_414);
x_420 = lean_nat_dec_le(x_418, x_419);
lean_dec(x_419);
lean_dec(x_418);
if (x_420 == 0)
{
lean_object* x_421; 
x_421 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_414);
lean_ctor_set(x_400, 1, x_421);
lean_ctor_set(x_400, 0, x_412);
return x_398;
}
else
{
lean_ctor_set(x_400, 1, x_414);
lean_ctor_set(x_400, 0, x_412);
return x_398;
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_422 = lean_box(0);
x_423 = lean_array_uset(x_404, x_408, x_422);
lean_inc(x_402);
x_424 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_402, x_409);
x_425 = lean_array_uset(x_423, x_408, x_424);
lean_ctor_set(x_400, 1, x_425);
return x_398;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; size_t x_430; size_t x_431; size_t x_432; lean_object* x_433; uint8_t x_434; 
x_426 = lean_ctor_get(x_398, 0);
x_427 = lean_ctor_get(x_400, 0);
x_428 = lean_ctor_get(x_400, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_400);
x_429 = lean_array_get_size(x_428);
x_430 = lean_usize_of_nat(x_429);
lean_dec(x_429);
x_431 = lean_usize_sub(x_430, x_105);
x_432 = lean_usize_land(x_103, x_431);
x_433 = lean_array_uget(x_428, x_432);
x_434 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_433);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; 
x_435 = lean_unsigned_to_nat(1u);
x_436 = lean_nat_add(x_427, x_435);
lean_dec(x_427);
lean_inc(x_426);
x_437 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_437, 0, x_9);
lean_ctor_set(x_437, 1, x_426);
lean_ctor_set(x_437, 2, x_433);
x_438 = lean_array_uset(x_428, x_432, x_437);
x_439 = lean_unsigned_to_nat(4u);
x_440 = lean_nat_mul(x_436, x_439);
x_441 = lean_unsigned_to_nat(3u);
x_442 = lean_nat_div(x_440, x_441);
lean_dec(x_440);
x_443 = lean_array_get_size(x_438);
x_444 = lean_nat_dec_le(x_442, x_443);
lean_dec(x_443);
lean_dec(x_442);
if (x_444 == 0)
{
lean_object* x_445; lean_object* x_446; 
x_445 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_438);
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_436);
lean_ctor_set(x_446, 1, x_445);
lean_ctor_set(x_398, 1, x_446);
return x_398;
}
else
{
lean_object* x_447; 
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_436);
lean_ctor_set(x_447, 1, x_438);
lean_ctor_set(x_398, 1, x_447);
return x_398;
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_448 = lean_box(0);
x_449 = lean_array_uset(x_428, x_432, x_448);
lean_inc(x_426);
x_450 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_426, x_433);
x_451 = lean_array_uset(x_449, x_432, x_450);
x_452 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_452, 0, x_427);
lean_ctor_set(x_452, 1, x_451);
lean_ctor_set(x_398, 1, x_452);
return x_398;
}
}
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; size_t x_459; size_t x_460; size_t x_461; lean_object* x_462; uint8_t x_463; 
x_453 = lean_ctor_get(x_398, 1);
x_454 = lean_ctor_get(x_398, 0);
lean_inc(x_453);
lean_inc(x_454);
lean_dec(x_398);
x_455 = lean_ctor_get(x_453, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_453, 1);
lean_inc(x_456);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_457 = x_453;
} else {
 lean_dec_ref(x_453);
 x_457 = lean_box(0);
}
x_458 = lean_array_get_size(x_456);
x_459 = lean_usize_of_nat(x_458);
lean_dec(x_458);
x_460 = lean_usize_sub(x_459, x_105);
x_461 = lean_usize_land(x_103, x_460);
x_462 = lean_array_uget(x_456, x_461);
x_463 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_462);
if (x_463 == 0)
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; uint8_t x_473; 
x_464 = lean_unsigned_to_nat(1u);
x_465 = lean_nat_add(x_455, x_464);
lean_dec(x_455);
lean_inc(x_454);
x_466 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_466, 0, x_9);
lean_ctor_set(x_466, 1, x_454);
lean_ctor_set(x_466, 2, x_462);
x_467 = lean_array_uset(x_456, x_461, x_466);
x_468 = lean_unsigned_to_nat(4u);
x_469 = lean_nat_mul(x_465, x_468);
x_470 = lean_unsigned_to_nat(3u);
x_471 = lean_nat_div(x_469, x_470);
lean_dec(x_469);
x_472 = lean_array_get_size(x_467);
x_473 = lean_nat_dec_le(x_471, x_472);
lean_dec(x_472);
lean_dec(x_471);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_474 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_467);
if (lean_is_scalar(x_457)) {
 x_475 = lean_alloc_ctor(0, 2, 0);
} else {
 x_475 = x_457;
}
lean_ctor_set(x_475, 0, x_465);
lean_ctor_set(x_475, 1, x_474);
x_476 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_476, 0, x_454);
lean_ctor_set(x_476, 1, x_475);
return x_476;
}
else
{
lean_object* x_477; lean_object* x_478; 
if (lean_is_scalar(x_457)) {
 x_477 = lean_alloc_ctor(0, 2, 0);
} else {
 x_477 = x_457;
}
lean_ctor_set(x_477, 0, x_465);
lean_ctor_set(x_477, 1, x_467);
x_478 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_478, 0, x_454);
lean_ctor_set(x_478, 1, x_477);
return x_478;
}
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_479 = lean_box(0);
x_480 = lean_array_uset(x_456, x_461, x_479);
lean_inc(x_454);
x_481 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_454, x_462);
x_482 = lean_array_uset(x_480, x_461, x_481);
if (lean_is_scalar(x_457)) {
 x_483 = lean_alloc_ctor(0, 2, 0);
} else {
 x_483 = x_457;
}
lean_ctor_set(x_483, 0, x_455);
lean_ctor_set(x_483, 1, x_482);
x_484 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_484, 0, x_454);
lean_ctor_set(x_484, 1, x_483);
return x_484;
}
}
}
case 4:
{
lean_object* x_485; lean_object* x_486; uint8_t x_487; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_5);
lean_dec(x_4);
x_485 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__12;
x_486 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8(x_485, x_6);
x_487 = !lean_is_exclusive(x_486);
if (x_487 == 0)
{
lean_object* x_488; uint8_t x_489; 
x_488 = lean_ctor_get(x_486, 1);
x_489 = !lean_is_exclusive(x_488);
if (x_489 == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; size_t x_494; size_t x_495; size_t x_496; lean_object* x_497; uint8_t x_498; 
x_490 = lean_ctor_get(x_486, 0);
x_491 = lean_ctor_get(x_488, 0);
x_492 = lean_ctor_get(x_488, 1);
x_493 = lean_array_get_size(x_492);
x_494 = lean_usize_of_nat(x_493);
lean_dec(x_493);
x_495 = lean_usize_sub(x_494, x_105);
x_496 = lean_usize_land(x_103, x_495);
x_497 = lean_array_uget(x_492, x_496);
x_498 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_497);
if (x_498 == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; uint8_t x_508; 
x_499 = lean_unsigned_to_nat(1u);
x_500 = lean_nat_add(x_491, x_499);
lean_dec(x_491);
lean_inc(x_490);
x_501 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_501, 0, x_9);
lean_ctor_set(x_501, 1, x_490);
lean_ctor_set(x_501, 2, x_497);
x_502 = lean_array_uset(x_492, x_496, x_501);
x_503 = lean_unsigned_to_nat(4u);
x_504 = lean_nat_mul(x_500, x_503);
x_505 = lean_unsigned_to_nat(3u);
x_506 = lean_nat_div(x_504, x_505);
lean_dec(x_504);
x_507 = lean_array_get_size(x_502);
x_508 = lean_nat_dec_le(x_506, x_507);
lean_dec(x_507);
lean_dec(x_506);
if (x_508 == 0)
{
lean_object* x_509; 
x_509 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_502);
lean_ctor_set(x_488, 1, x_509);
lean_ctor_set(x_488, 0, x_500);
return x_486;
}
else
{
lean_ctor_set(x_488, 1, x_502);
lean_ctor_set(x_488, 0, x_500);
return x_486;
}
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_510 = lean_box(0);
x_511 = lean_array_uset(x_492, x_496, x_510);
lean_inc(x_490);
x_512 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_490, x_497);
x_513 = lean_array_uset(x_511, x_496, x_512);
lean_ctor_set(x_488, 1, x_513);
return x_486;
}
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; size_t x_518; size_t x_519; size_t x_520; lean_object* x_521; uint8_t x_522; 
x_514 = lean_ctor_get(x_486, 0);
x_515 = lean_ctor_get(x_488, 0);
x_516 = lean_ctor_get(x_488, 1);
lean_inc(x_516);
lean_inc(x_515);
lean_dec(x_488);
x_517 = lean_array_get_size(x_516);
x_518 = lean_usize_of_nat(x_517);
lean_dec(x_517);
x_519 = lean_usize_sub(x_518, x_105);
x_520 = lean_usize_land(x_103, x_519);
x_521 = lean_array_uget(x_516, x_520);
x_522 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_521);
if (x_522 == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; uint8_t x_532; 
x_523 = lean_unsigned_to_nat(1u);
x_524 = lean_nat_add(x_515, x_523);
lean_dec(x_515);
lean_inc(x_514);
x_525 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_525, 0, x_9);
lean_ctor_set(x_525, 1, x_514);
lean_ctor_set(x_525, 2, x_521);
x_526 = lean_array_uset(x_516, x_520, x_525);
x_527 = lean_unsigned_to_nat(4u);
x_528 = lean_nat_mul(x_524, x_527);
x_529 = lean_unsigned_to_nat(3u);
x_530 = lean_nat_div(x_528, x_529);
lean_dec(x_528);
x_531 = lean_array_get_size(x_526);
x_532 = lean_nat_dec_le(x_530, x_531);
lean_dec(x_531);
lean_dec(x_530);
if (x_532 == 0)
{
lean_object* x_533; lean_object* x_534; 
x_533 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_526);
x_534 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_534, 0, x_524);
lean_ctor_set(x_534, 1, x_533);
lean_ctor_set(x_486, 1, x_534);
return x_486;
}
else
{
lean_object* x_535; 
x_535 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_535, 0, x_524);
lean_ctor_set(x_535, 1, x_526);
lean_ctor_set(x_486, 1, x_535);
return x_486;
}
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_536 = lean_box(0);
x_537 = lean_array_uset(x_516, x_520, x_536);
lean_inc(x_514);
x_538 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_514, x_521);
x_539 = lean_array_uset(x_537, x_520, x_538);
x_540 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_540, 0, x_515);
lean_ctor_set(x_540, 1, x_539);
lean_ctor_set(x_486, 1, x_540);
return x_486;
}
}
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; size_t x_547; size_t x_548; size_t x_549; lean_object* x_550; uint8_t x_551; 
x_541 = lean_ctor_get(x_486, 1);
x_542 = lean_ctor_get(x_486, 0);
lean_inc(x_541);
lean_inc(x_542);
lean_dec(x_486);
x_543 = lean_ctor_get(x_541, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_541, 1);
lean_inc(x_544);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 x_545 = x_541;
} else {
 lean_dec_ref(x_541);
 x_545 = lean_box(0);
}
x_546 = lean_array_get_size(x_544);
x_547 = lean_usize_of_nat(x_546);
lean_dec(x_546);
x_548 = lean_usize_sub(x_547, x_105);
x_549 = lean_usize_land(x_103, x_548);
x_550 = lean_array_uget(x_544, x_549);
x_551 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_550);
if (x_551 == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; uint8_t x_561; 
x_552 = lean_unsigned_to_nat(1u);
x_553 = lean_nat_add(x_543, x_552);
lean_dec(x_543);
lean_inc(x_542);
x_554 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_554, 0, x_9);
lean_ctor_set(x_554, 1, x_542);
lean_ctor_set(x_554, 2, x_550);
x_555 = lean_array_uset(x_544, x_549, x_554);
x_556 = lean_unsigned_to_nat(4u);
x_557 = lean_nat_mul(x_553, x_556);
x_558 = lean_unsigned_to_nat(3u);
x_559 = lean_nat_div(x_557, x_558);
lean_dec(x_557);
x_560 = lean_array_get_size(x_555);
x_561 = lean_nat_dec_le(x_559, x_560);
lean_dec(x_560);
lean_dec(x_559);
if (x_561 == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_562 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_555);
if (lean_is_scalar(x_545)) {
 x_563 = lean_alloc_ctor(0, 2, 0);
} else {
 x_563 = x_545;
}
lean_ctor_set(x_563, 0, x_553);
lean_ctor_set(x_563, 1, x_562);
x_564 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_564, 0, x_542);
lean_ctor_set(x_564, 1, x_563);
return x_564;
}
else
{
lean_object* x_565; lean_object* x_566; 
if (lean_is_scalar(x_545)) {
 x_565 = lean_alloc_ctor(0, 2, 0);
} else {
 x_565 = x_545;
}
lean_ctor_set(x_565, 0, x_553);
lean_ctor_set(x_565, 1, x_555);
x_566 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_566, 0, x_542);
lean_ctor_set(x_566, 1, x_565);
return x_566;
}
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_567 = lean_box(0);
x_568 = lean_array_uset(x_544, x_549, x_567);
lean_inc(x_542);
x_569 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_542, x_550);
x_570 = lean_array_uset(x_568, x_549, x_569);
if (lean_is_scalar(x_545)) {
 x_571 = lean_alloc_ctor(0, 2, 0);
} else {
 x_571 = x_545;
}
lean_ctor_set(x_571, 0, x_543);
lean_ctor_set(x_571, 1, x_570);
x_572 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_572, 0, x_542);
lean_ctor_set(x_572, 1, x_571);
return x_572;
}
}
}
case 5:
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; uint8_t x_579; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
x_573 = lean_unsigned_to_nat(0u);
x_574 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_4, x_573);
x_575 = lean_mk_empty_array_with_capacity(x_574);
lean_dec(x_574);
x_576 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__3;
x_577 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__5;
x_578 = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10(x_1, x_2, x_3, x_5, x_576, x_577, x_4, x_575, x_6);
x_579 = !lean_is_exclusive(x_578);
if (x_579 == 0)
{
lean_object* x_580; uint8_t x_581; 
x_580 = lean_ctor_get(x_578, 1);
x_581 = !lean_is_exclusive(x_580);
if (x_581 == 0)
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; size_t x_586; size_t x_587; size_t x_588; lean_object* x_589; uint8_t x_590; 
x_582 = lean_ctor_get(x_578, 0);
x_583 = lean_ctor_get(x_580, 0);
x_584 = lean_ctor_get(x_580, 1);
x_585 = lean_array_get_size(x_584);
x_586 = lean_usize_of_nat(x_585);
lean_dec(x_585);
x_587 = lean_usize_sub(x_586, x_105);
x_588 = lean_usize_land(x_103, x_587);
x_589 = lean_array_uget(x_584, x_588);
x_590 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_589);
if (x_590 == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; uint8_t x_600; 
x_591 = lean_unsigned_to_nat(1u);
x_592 = lean_nat_add(x_583, x_591);
lean_dec(x_583);
lean_inc(x_582);
x_593 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_593, 0, x_9);
lean_ctor_set(x_593, 1, x_582);
lean_ctor_set(x_593, 2, x_589);
x_594 = lean_array_uset(x_584, x_588, x_593);
x_595 = lean_unsigned_to_nat(4u);
x_596 = lean_nat_mul(x_592, x_595);
x_597 = lean_unsigned_to_nat(3u);
x_598 = lean_nat_div(x_596, x_597);
lean_dec(x_596);
x_599 = lean_array_get_size(x_594);
x_600 = lean_nat_dec_le(x_598, x_599);
lean_dec(x_599);
lean_dec(x_598);
if (x_600 == 0)
{
lean_object* x_601; 
x_601 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_594);
lean_ctor_set(x_580, 1, x_601);
lean_ctor_set(x_580, 0, x_592);
return x_578;
}
else
{
lean_ctor_set(x_580, 1, x_594);
lean_ctor_set(x_580, 0, x_592);
return x_578;
}
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_602 = lean_box(0);
x_603 = lean_array_uset(x_584, x_588, x_602);
lean_inc(x_582);
x_604 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_582, x_589);
x_605 = lean_array_uset(x_603, x_588, x_604);
lean_ctor_set(x_580, 1, x_605);
return x_578;
}
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; size_t x_610; size_t x_611; size_t x_612; lean_object* x_613; uint8_t x_614; 
x_606 = lean_ctor_get(x_578, 0);
x_607 = lean_ctor_get(x_580, 0);
x_608 = lean_ctor_get(x_580, 1);
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_580);
x_609 = lean_array_get_size(x_608);
x_610 = lean_usize_of_nat(x_609);
lean_dec(x_609);
x_611 = lean_usize_sub(x_610, x_105);
x_612 = lean_usize_land(x_103, x_611);
x_613 = lean_array_uget(x_608, x_612);
x_614 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_613);
if (x_614 == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; 
x_615 = lean_unsigned_to_nat(1u);
x_616 = lean_nat_add(x_607, x_615);
lean_dec(x_607);
lean_inc(x_606);
x_617 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_617, 0, x_9);
lean_ctor_set(x_617, 1, x_606);
lean_ctor_set(x_617, 2, x_613);
x_618 = lean_array_uset(x_608, x_612, x_617);
x_619 = lean_unsigned_to_nat(4u);
x_620 = lean_nat_mul(x_616, x_619);
x_621 = lean_unsigned_to_nat(3u);
x_622 = lean_nat_div(x_620, x_621);
lean_dec(x_620);
x_623 = lean_array_get_size(x_618);
x_624 = lean_nat_dec_le(x_622, x_623);
lean_dec(x_623);
lean_dec(x_622);
if (x_624 == 0)
{
lean_object* x_625; lean_object* x_626; 
x_625 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_618);
x_626 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_626, 0, x_616);
lean_ctor_set(x_626, 1, x_625);
lean_ctor_set(x_578, 1, x_626);
return x_578;
}
else
{
lean_object* x_627; 
x_627 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_627, 0, x_616);
lean_ctor_set(x_627, 1, x_618);
lean_ctor_set(x_578, 1, x_627);
return x_578;
}
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_628 = lean_box(0);
x_629 = lean_array_uset(x_608, x_612, x_628);
lean_inc(x_606);
x_630 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_606, x_613);
x_631 = lean_array_uset(x_629, x_612, x_630);
x_632 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_632, 0, x_607);
lean_ctor_set(x_632, 1, x_631);
lean_ctor_set(x_578, 1, x_632);
return x_578;
}
}
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; size_t x_639; size_t x_640; size_t x_641; lean_object* x_642; uint8_t x_643; 
x_633 = lean_ctor_get(x_578, 1);
x_634 = lean_ctor_get(x_578, 0);
lean_inc(x_633);
lean_inc(x_634);
lean_dec(x_578);
x_635 = lean_ctor_get(x_633, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_633, 1);
lean_inc(x_636);
if (lean_is_exclusive(x_633)) {
 lean_ctor_release(x_633, 0);
 lean_ctor_release(x_633, 1);
 x_637 = x_633;
} else {
 lean_dec_ref(x_633);
 x_637 = lean_box(0);
}
x_638 = lean_array_get_size(x_636);
x_639 = lean_usize_of_nat(x_638);
lean_dec(x_638);
x_640 = lean_usize_sub(x_639, x_105);
x_641 = lean_usize_land(x_103, x_640);
x_642 = lean_array_uget(x_636, x_641);
x_643 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_642);
if (x_643 == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; uint8_t x_653; 
x_644 = lean_unsigned_to_nat(1u);
x_645 = lean_nat_add(x_635, x_644);
lean_dec(x_635);
lean_inc(x_634);
x_646 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_646, 0, x_9);
lean_ctor_set(x_646, 1, x_634);
lean_ctor_set(x_646, 2, x_642);
x_647 = lean_array_uset(x_636, x_641, x_646);
x_648 = lean_unsigned_to_nat(4u);
x_649 = lean_nat_mul(x_645, x_648);
x_650 = lean_unsigned_to_nat(3u);
x_651 = lean_nat_div(x_649, x_650);
lean_dec(x_649);
x_652 = lean_array_get_size(x_647);
x_653 = lean_nat_dec_le(x_651, x_652);
lean_dec(x_652);
lean_dec(x_651);
if (x_653 == 0)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_654 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_647);
if (lean_is_scalar(x_637)) {
 x_655 = lean_alloc_ctor(0, 2, 0);
} else {
 x_655 = x_637;
}
lean_ctor_set(x_655, 0, x_645);
lean_ctor_set(x_655, 1, x_654);
x_656 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_656, 0, x_634);
lean_ctor_set(x_656, 1, x_655);
return x_656;
}
else
{
lean_object* x_657; lean_object* x_658; 
if (lean_is_scalar(x_637)) {
 x_657 = lean_alloc_ctor(0, 2, 0);
} else {
 x_657 = x_637;
}
lean_ctor_set(x_657, 0, x_645);
lean_ctor_set(x_657, 1, x_647);
x_658 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_658, 0, x_634);
lean_ctor_set(x_658, 1, x_657);
return x_658;
}
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_659 = lean_box(0);
x_660 = lean_array_uset(x_636, x_641, x_659);
lean_inc(x_634);
x_661 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_634, x_642);
x_662 = lean_array_uset(x_660, x_641, x_661);
if (lean_is_scalar(x_637)) {
 x_663 = lean_alloc_ctor(0, 2, 0);
} else {
 x_663 = x_637;
}
lean_ctor_set(x_663, 0, x_635);
lean_ctor_set(x_663, 1, x_662);
x_664 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_664, 0, x_634);
lean_ctor_set(x_664, 1, x_663);
return x_664;
}
}
}
case 6:
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; uint8_t x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; size_t x_678; size_t x_679; uint8_t x_680; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
x_665 = lean_ctor_get(x_4, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_4, 1);
lean_inc(x_666);
x_667 = lean_ctor_get(x_4, 2);
lean_inc(x_667);
x_668 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
lean_inc(x_5);
lean_inc(x_666);
x_669 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_666, x_5, x_6);
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_669, 1);
lean_inc(x_671);
lean_dec(x_669);
x_672 = lean_unsigned_to_nat(1u);
x_673 = lean_nat_add(x_5, x_672);
lean_inc(x_667);
x_674 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_667, x_673, x_671);
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
lean_dec(x_674);
lean_inc(x_667);
lean_inc(x_666);
lean_inc(x_665);
x_677 = l_Lean_Expr_lam___override(x_665, x_666, x_667, x_668);
x_678 = lean_ptr_addr(x_666);
lean_dec(x_666);
x_679 = lean_ptr_addr(x_670);
x_680 = lean_usize_dec_eq(x_678, x_679);
if (x_680 == 0)
{
lean_object* x_681; 
lean_dec(x_677);
lean_dec(x_667);
x_681 = l_Lean_Expr_lam___override(x_665, x_670, x_675, x_668);
x_10 = x_681;
x_11 = x_676;
goto block_90;
}
else
{
size_t x_682; size_t x_683; uint8_t x_684; 
x_682 = lean_ptr_addr(x_667);
lean_dec(x_667);
x_683 = lean_ptr_addr(x_675);
x_684 = lean_usize_dec_eq(x_682, x_683);
if (x_684 == 0)
{
lean_object* x_685; 
lean_dec(x_677);
x_685 = l_Lean_Expr_lam___override(x_665, x_670, x_675, x_668);
x_10 = x_685;
x_11 = x_676;
goto block_90;
}
else
{
uint8_t x_686; 
x_686 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_668, x_668);
if (x_686 == 0)
{
lean_object* x_687; 
lean_dec(x_677);
x_687 = l_Lean_Expr_lam___override(x_665, x_670, x_675, x_668);
x_10 = x_687;
x_11 = x_676;
goto block_90;
}
else
{
lean_dec(x_675);
lean_dec(x_670);
lean_dec(x_665);
x_10 = x_677;
x_11 = x_676;
goto block_90;
}
}
}
}
case 7:
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; uint8_t x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; size_t x_701; size_t x_702; uint8_t x_703; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
x_688 = lean_ctor_get(x_4, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_4, 1);
lean_inc(x_689);
x_690 = lean_ctor_get(x_4, 2);
lean_inc(x_690);
x_691 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
lean_inc(x_5);
lean_inc(x_689);
x_692 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_689, x_5, x_6);
x_693 = lean_ctor_get(x_692, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_692, 1);
lean_inc(x_694);
lean_dec(x_692);
x_695 = lean_unsigned_to_nat(1u);
x_696 = lean_nat_add(x_5, x_695);
lean_inc(x_690);
x_697 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_690, x_696, x_694);
x_698 = lean_ctor_get(x_697, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_697, 1);
lean_inc(x_699);
lean_dec(x_697);
lean_inc(x_690);
lean_inc(x_689);
lean_inc(x_688);
x_700 = l_Lean_Expr_forallE___override(x_688, x_689, x_690, x_691);
x_701 = lean_ptr_addr(x_689);
lean_dec(x_689);
x_702 = lean_ptr_addr(x_693);
x_703 = lean_usize_dec_eq(x_701, x_702);
if (x_703 == 0)
{
lean_object* x_704; 
lean_dec(x_700);
lean_dec(x_690);
x_704 = l_Lean_Expr_forallE___override(x_688, x_693, x_698, x_691);
x_10 = x_704;
x_11 = x_699;
goto block_90;
}
else
{
size_t x_705; size_t x_706; uint8_t x_707; 
x_705 = lean_ptr_addr(x_690);
lean_dec(x_690);
x_706 = lean_ptr_addr(x_698);
x_707 = lean_usize_dec_eq(x_705, x_706);
if (x_707 == 0)
{
lean_object* x_708; 
lean_dec(x_700);
x_708 = l_Lean_Expr_forallE___override(x_688, x_693, x_698, x_691);
x_10 = x_708;
x_11 = x_699;
goto block_90;
}
else
{
uint8_t x_709; 
x_709 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_691, x_691);
if (x_709 == 0)
{
lean_object* x_710; 
lean_dec(x_700);
x_710 = l_Lean_Expr_forallE___override(x_688, x_693, x_698, x_691);
x_10 = x_710;
x_11 = x_699;
goto block_90;
}
else
{
lean_dec(x_698);
lean_dec(x_693);
lean_dec(x_688);
x_10 = x_700;
x_11 = x_699;
goto block_90;
}
}
}
}
case 8:
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; uint8_t x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; size_t x_727; size_t x_728; uint8_t x_729; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
x_711 = lean_ctor_get(x_4, 0);
lean_inc(x_711);
x_712 = lean_ctor_get(x_4, 1);
lean_inc(x_712);
x_713 = lean_ctor_get(x_4, 2);
lean_inc(x_713);
x_714 = lean_ctor_get(x_4, 3);
lean_inc(x_714);
x_715 = lean_ctor_get_uint8(x_4, sizeof(void*)*4 + 8);
lean_inc(x_5);
lean_inc(x_712);
x_716 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_712, x_5, x_6);
x_717 = lean_ctor_get(x_716, 0);
lean_inc(x_717);
x_718 = lean_ctor_get(x_716, 1);
lean_inc(x_718);
lean_dec(x_716);
lean_inc(x_5);
lean_inc(x_713);
x_719 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_713, x_5, x_718);
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_719, 1);
lean_inc(x_721);
lean_dec(x_719);
x_722 = lean_unsigned_to_nat(1u);
x_723 = lean_nat_add(x_5, x_722);
lean_inc(x_714);
x_724 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_714, x_723, x_721);
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_724, 1);
lean_inc(x_726);
lean_dec(x_724);
x_727 = lean_ptr_addr(x_712);
lean_dec(x_712);
x_728 = lean_ptr_addr(x_717);
x_729 = lean_usize_dec_eq(x_727, x_728);
if (x_729 == 0)
{
lean_object* x_730; 
lean_dec(x_714);
lean_dec(x_713);
x_730 = l_Lean_Expr_letE___override(x_711, x_717, x_720, x_725, x_715);
x_10 = x_730;
x_11 = x_726;
goto block_90;
}
else
{
size_t x_731; size_t x_732; uint8_t x_733; 
x_731 = lean_ptr_addr(x_713);
lean_dec(x_713);
x_732 = lean_ptr_addr(x_720);
x_733 = lean_usize_dec_eq(x_731, x_732);
if (x_733 == 0)
{
lean_object* x_734; 
lean_dec(x_714);
x_734 = l_Lean_Expr_letE___override(x_711, x_717, x_720, x_725, x_715);
x_10 = x_734;
x_11 = x_726;
goto block_90;
}
else
{
size_t x_735; size_t x_736; uint8_t x_737; 
x_735 = lean_ptr_addr(x_714);
lean_dec(x_714);
x_736 = lean_ptr_addr(x_725);
x_737 = lean_usize_dec_eq(x_735, x_736);
if (x_737 == 0)
{
lean_object* x_738; 
x_738 = l_Lean_Expr_letE___override(x_711, x_717, x_720, x_725, x_715);
x_10 = x_738;
x_11 = x_726;
goto block_90;
}
else
{
lean_dec(x_725);
lean_dec(x_720);
lean_dec(x_717);
lean_dec(x_711);
lean_inc(x_4);
x_10 = x_4;
x_11 = x_726;
goto block_90;
}
}
}
}
case 9:
{
lean_object* x_739; lean_object* x_740; uint8_t x_741; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_5);
lean_dec(x_4);
x_739 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__13;
x_740 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8(x_739, x_6);
x_741 = !lean_is_exclusive(x_740);
if (x_741 == 0)
{
lean_object* x_742; uint8_t x_743; 
x_742 = lean_ctor_get(x_740, 1);
x_743 = !lean_is_exclusive(x_742);
if (x_743 == 0)
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; size_t x_748; size_t x_749; size_t x_750; lean_object* x_751; uint8_t x_752; 
x_744 = lean_ctor_get(x_740, 0);
x_745 = lean_ctor_get(x_742, 0);
x_746 = lean_ctor_get(x_742, 1);
x_747 = lean_array_get_size(x_746);
x_748 = lean_usize_of_nat(x_747);
lean_dec(x_747);
x_749 = lean_usize_sub(x_748, x_105);
x_750 = lean_usize_land(x_103, x_749);
x_751 = lean_array_uget(x_746, x_750);
x_752 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_751);
if (x_752 == 0)
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; uint8_t x_762; 
x_753 = lean_unsigned_to_nat(1u);
x_754 = lean_nat_add(x_745, x_753);
lean_dec(x_745);
lean_inc(x_744);
x_755 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_755, 0, x_9);
lean_ctor_set(x_755, 1, x_744);
lean_ctor_set(x_755, 2, x_751);
x_756 = lean_array_uset(x_746, x_750, x_755);
x_757 = lean_unsigned_to_nat(4u);
x_758 = lean_nat_mul(x_754, x_757);
x_759 = lean_unsigned_to_nat(3u);
x_760 = lean_nat_div(x_758, x_759);
lean_dec(x_758);
x_761 = lean_array_get_size(x_756);
x_762 = lean_nat_dec_le(x_760, x_761);
lean_dec(x_761);
lean_dec(x_760);
if (x_762 == 0)
{
lean_object* x_763; 
x_763 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_756);
lean_ctor_set(x_742, 1, x_763);
lean_ctor_set(x_742, 0, x_754);
return x_740;
}
else
{
lean_ctor_set(x_742, 1, x_756);
lean_ctor_set(x_742, 0, x_754);
return x_740;
}
}
else
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; 
x_764 = lean_box(0);
x_765 = lean_array_uset(x_746, x_750, x_764);
lean_inc(x_744);
x_766 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_744, x_751);
x_767 = lean_array_uset(x_765, x_750, x_766);
lean_ctor_set(x_742, 1, x_767);
return x_740;
}
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; size_t x_772; size_t x_773; size_t x_774; lean_object* x_775; uint8_t x_776; 
x_768 = lean_ctor_get(x_740, 0);
x_769 = lean_ctor_get(x_742, 0);
x_770 = lean_ctor_get(x_742, 1);
lean_inc(x_770);
lean_inc(x_769);
lean_dec(x_742);
x_771 = lean_array_get_size(x_770);
x_772 = lean_usize_of_nat(x_771);
lean_dec(x_771);
x_773 = lean_usize_sub(x_772, x_105);
x_774 = lean_usize_land(x_103, x_773);
x_775 = lean_array_uget(x_770, x_774);
x_776 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_775);
if (x_776 == 0)
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; uint8_t x_786; 
x_777 = lean_unsigned_to_nat(1u);
x_778 = lean_nat_add(x_769, x_777);
lean_dec(x_769);
lean_inc(x_768);
x_779 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_779, 0, x_9);
lean_ctor_set(x_779, 1, x_768);
lean_ctor_set(x_779, 2, x_775);
x_780 = lean_array_uset(x_770, x_774, x_779);
x_781 = lean_unsigned_to_nat(4u);
x_782 = lean_nat_mul(x_778, x_781);
x_783 = lean_unsigned_to_nat(3u);
x_784 = lean_nat_div(x_782, x_783);
lean_dec(x_782);
x_785 = lean_array_get_size(x_780);
x_786 = lean_nat_dec_le(x_784, x_785);
lean_dec(x_785);
lean_dec(x_784);
if (x_786 == 0)
{
lean_object* x_787; lean_object* x_788; 
x_787 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_780);
x_788 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_788, 0, x_778);
lean_ctor_set(x_788, 1, x_787);
lean_ctor_set(x_740, 1, x_788);
return x_740;
}
else
{
lean_object* x_789; 
x_789 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_789, 0, x_778);
lean_ctor_set(x_789, 1, x_780);
lean_ctor_set(x_740, 1, x_789);
return x_740;
}
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_790 = lean_box(0);
x_791 = lean_array_uset(x_770, x_774, x_790);
lean_inc(x_768);
x_792 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_768, x_775);
x_793 = lean_array_uset(x_791, x_774, x_792);
x_794 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_794, 0, x_769);
lean_ctor_set(x_794, 1, x_793);
lean_ctor_set(x_740, 1, x_794);
return x_740;
}
}
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; size_t x_801; size_t x_802; size_t x_803; lean_object* x_804; uint8_t x_805; 
x_795 = lean_ctor_get(x_740, 1);
x_796 = lean_ctor_get(x_740, 0);
lean_inc(x_795);
lean_inc(x_796);
lean_dec(x_740);
x_797 = lean_ctor_get(x_795, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_795, 1);
lean_inc(x_798);
if (lean_is_exclusive(x_795)) {
 lean_ctor_release(x_795, 0);
 lean_ctor_release(x_795, 1);
 x_799 = x_795;
} else {
 lean_dec_ref(x_795);
 x_799 = lean_box(0);
}
x_800 = lean_array_get_size(x_798);
x_801 = lean_usize_of_nat(x_800);
lean_dec(x_800);
x_802 = lean_usize_sub(x_801, x_105);
x_803 = lean_usize_land(x_103, x_802);
x_804 = lean_array_uget(x_798, x_803);
x_805 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_9, x_804);
if (x_805 == 0)
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; uint8_t x_815; 
x_806 = lean_unsigned_to_nat(1u);
x_807 = lean_nat_add(x_797, x_806);
lean_dec(x_797);
lean_inc(x_796);
x_808 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_808, 0, x_9);
lean_ctor_set(x_808, 1, x_796);
lean_ctor_set(x_808, 2, x_804);
x_809 = lean_array_uset(x_798, x_803, x_808);
x_810 = lean_unsigned_to_nat(4u);
x_811 = lean_nat_mul(x_807, x_810);
x_812 = lean_unsigned_to_nat(3u);
x_813 = lean_nat_div(x_811, x_812);
lean_dec(x_811);
x_814 = lean_array_get_size(x_809);
x_815 = lean_nat_dec_le(x_813, x_814);
lean_dec(x_814);
lean_dec(x_813);
if (x_815 == 0)
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; 
x_816 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_809);
if (lean_is_scalar(x_799)) {
 x_817 = lean_alloc_ctor(0, 2, 0);
} else {
 x_817 = x_799;
}
lean_ctor_set(x_817, 0, x_807);
lean_ctor_set(x_817, 1, x_816);
x_818 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_818, 0, x_796);
lean_ctor_set(x_818, 1, x_817);
return x_818;
}
else
{
lean_object* x_819; lean_object* x_820; 
if (lean_is_scalar(x_799)) {
 x_819 = lean_alloc_ctor(0, 2, 0);
} else {
 x_819 = x_799;
}
lean_ctor_set(x_819, 0, x_807);
lean_ctor_set(x_819, 1, x_809);
x_820 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_820, 0, x_796);
lean_ctor_set(x_820, 1, x_819);
return x_820;
}
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; 
x_821 = lean_box(0);
x_822 = lean_array_uset(x_798, x_803, x_821);
lean_inc(x_796);
x_823 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_9, x_796, x_804);
x_824 = lean_array_uset(x_822, x_803, x_823);
if (lean_is_scalar(x_799)) {
 x_825 = lean_alloc_ctor(0, 2, 0);
} else {
 x_825 = x_799;
}
lean_ctor_set(x_825, 0, x_797);
lean_ctor_set(x_825, 1, x_824);
x_826 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_826, 0, x_796);
lean_ctor_set(x_826, 1, x_825);
return x_826;
}
}
}
case 10:
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; size_t x_832; size_t x_833; uint8_t x_834; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
x_827 = lean_ctor_get(x_4, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_4, 1);
lean_inc(x_828);
lean_inc(x_5);
lean_inc(x_828);
x_829 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_828, x_5, x_6);
x_830 = lean_ctor_get(x_829, 0);
lean_inc(x_830);
x_831 = lean_ctor_get(x_829, 1);
lean_inc(x_831);
lean_dec(x_829);
x_832 = lean_ptr_addr(x_828);
lean_dec(x_828);
x_833 = lean_ptr_addr(x_830);
x_834 = lean_usize_dec_eq(x_832, x_833);
if (x_834 == 0)
{
lean_object* x_835; 
x_835 = l_Lean_Expr_mdata___override(x_827, x_830);
x_10 = x_835;
x_11 = x_831;
goto block_90;
}
else
{
lean_dec(x_830);
lean_dec(x_827);
lean_inc(x_4);
x_10 = x_4;
x_11 = x_831;
goto block_90;
}
}
default: 
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; size_t x_842; size_t x_843; uint8_t x_844; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
x_836 = lean_ctor_get(x_4, 0);
lean_inc(x_836);
x_837 = lean_ctor_get(x_4, 1);
lean_inc(x_837);
x_838 = lean_ctor_get(x_4, 2);
lean_inc(x_838);
lean_inc(x_5);
lean_inc(x_838);
x_839 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_838, x_5, x_6);
x_840 = lean_ctor_get(x_839, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_839, 1);
lean_inc(x_841);
lean_dec(x_839);
x_842 = lean_ptr_addr(x_838);
lean_dec(x_838);
x_843 = lean_ptr_addr(x_840);
x_844 = lean_usize_dec_eq(x_842, x_843);
if (x_844 == 0)
{
lean_object* x_845; 
x_845 = l_Lean_Expr_proj___override(x_836, x_837, x_840);
x_10 = x_845;
x_11 = x_841;
goto block_90;
}
else
{
lean_dec(x_840);
lean_dec(x_837);
lean_dec(x_836);
lean_inc(x_4);
x_10 = x_4;
x_11 = x_841;
goto block_90;
}
}
}
}
else
{
lean_object* x_846; lean_object* x_847; 
lean_dec(x_108);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_846 = lean_ctor_get(x_109, 0);
lean_inc(x_846);
lean_dec(x_109);
x_847 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_847, 0, x_846);
lean_ctor_set(x_847, 1, x_6);
return x_847;
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
lean_object* x_848; 
lean_dec(x_5);
x_848 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_848, 0, x_4);
lean_ctor_set(x_848, 1, x_6);
return x_848;
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
x_23 = l_Lean_Environment_find_x3f(x_22, x_16);
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
x_173 = l_Lean_Environment_find_x3f(x_172, x_16);
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
uint64_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; 
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
x_32 = lean_ctor_get_uint8(x_8, 17);
x_33 = 1;
x_34 = l_Lean_Meta_TransparencyMode_lt(x_29, x_33);
x_35 = 2;
x_36 = lean_uint64_shift_right(x_10, x_35);
x_37 = lean_uint64_shift_left(x_36, x_35);
if (x_34 == 0)
{
uint64_t x_38; uint64_t x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = l_Lean_Meta_TransparencyMode_toUInt64(x_29);
x_39 = lean_uint64_lor(x_37, x_38);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_39);
x_40 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get_uint8(x_41, 13);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_41);
lean_dec(x_2);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = 1;
x_45 = 2;
x_46 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_46, 0, x_20);
lean_ctor_set_uint8(x_46, 1, x_21);
lean_ctor_set_uint8(x_46, 2, x_22);
lean_ctor_set_uint8(x_46, 3, x_23);
lean_ctor_set_uint8(x_46, 4, x_24);
lean_ctor_set_uint8(x_46, 5, x_25);
lean_ctor_set_uint8(x_46, 6, x_26);
lean_ctor_set_uint8(x_46, 7, x_27);
lean_ctor_set_uint8(x_46, 8, x_28);
lean_ctor_set_uint8(x_46, 9, x_29);
lean_ctor_set_uint8(x_46, 10, x_30);
lean_ctor_set_uint8(x_46, 11, x_31);
lean_ctor_set_uint8(x_46, 12, x_44);
lean_ctor_set_uint8(x_46, 13, x_44);
lean_ctor_set_uint8(x_46, 14, x_45);
lean_ctor_set_uint8(x_46, 15, x_44);
lean_ctor_set_uint8(x_46, 16, x_44);
lean_ctor_set_uint8(x_46, 17, x_32);
x_47 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_46);
x_48 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_12);
lean_ctor_set(x_48, 2, x_13);
lean_ctor_set(x_48, 3, x_14);
lean_ctor_set(x_48, 4, x_15);
lean_ctor_set(x_48, 5, x_16);
lean_ctor_set(x_48, 6, x_17);
lean_ctor_set_uint64(x_48, sizeof(void*)*7, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_48, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_48, sizeof(void*)*7 + 10, x_19);
x_49 = lean_apply_5(x_1, x_48, x_3, x_4, x_5, x_43);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
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
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
x_58 = lean_ctor_get_uint8(x_41, 12);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_41);
lean_dec(x_2);
x_59 = lean_ctor_get(x_40, 1);
lean_inc(x_59);
lean_dec(x_40);
x_60 = 1;
x_61 = 2;
x_62 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_62, 0, x_20);
lean_ctor_set_uint8(x_62, 1, x_21);
lean_ctor_set_uint8(x_62, 2, x_22);
lean_ctor_set_uint8(x_62, 3, x_23);
lean_ctor_set_uint8(x_62, 4, x_24);
lean_ctor_set_uint8(x_62, 5, x_25);
lean_ctor_set_uint8(x_62, 6, x_26);
lean_ctor_set_uint8(x_62, 7, x_27);
lean_ctor_set_uint8(x_62, 8, x_28);
lean_ctor_set_uint8(x_62, 9, x_29);
lean_ctor_set_uint8(x_62, 10, x_30);
lean_ctor_set_uint8(x_62, 11, x_31);
lean_ctor_set_uint8(x_62, 12, x_60);
lean_ctor_set_uint8(x_62, 13, x_60);
lean_ctor_set_uint8(x_62, 14, x_61);
lean_ctor_set_uint8(x_62, 15, x_60);
lean_ctor_set_uint8(x_62, 16, x_60);
lean_ctor_set_uint8(x_62, 17, x_32);
x_63 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_62);
x_64 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_12);
lean_ctor_set(x_64, 2, x_13);
lean_ctor_set(x_64, 3, x_14);
lean_ctor_set(x_64, 4, x_15);
lean_ctor_set(x_64, 5, x_16);
lean_ctor_set(x_64, 6, x_17);
lean_ctor_set_uint64(x_64, sizeof(void*)*7, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_64, sizeof(void*)*7 + 10, x_19);
x_65 = lean_apply_5(x_1, x_64, x_3, x_4, x_5, x_59);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
return x_65;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_65);
if (x_70 == 0)
{
return x_65;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_65, 0);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_65);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
x_74 = lean_ctor_get_uint8(x_41, 15);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; uint64_t x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_41);
lean_dec(x_2);
x_75 = lean_ctor_get(x_40, 1);
lean_inc(x_75);
lean_dec(x_40);
x_76 = 1;
x_77 = 2;
x_78 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_78, 0, x_20);
lean_ctor_set_uint8(x_78, 1, x_21);
lean_ctor_set_uint8(x_78, 2, x_22);
lean_ctor_set_uint8(x_78, 3, x_23);
lean_ctor_set_uint8(x_78, 4, x_24);
lean_ctor_set_uint8(x_78, 5, x_25);
lean_ctor_set_uint8(x_78, 6, x_26);
lean_ctor_set_uint8(x_78, 7, x_27);
lean_ctor_set_uint8(x_78, 8, x_28);
lean_ctor_set_uint8(x_78, 9, x_29);
lean_ctor_set_uint8(x_78, 10, x_30);
lean_ctor_set_uint8(x_78, 11, x_31);
lean_ctor_set_uint8(x_78, 12, x_76);
lean_ctor_set_uint8(x_78, 13, x_76);
lean_ctor_set_uint8(x_78, 14, x_77);
lean_ctor_set_uint8(x_78, 15, x_76);
lean_ctor_set_uint8(x_78, 16, x_76);
lean_ctor_set_uint8(x_78, 17, x_32);
x_79 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_78);
x_80 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_12);
lean_ctor_set(x_80, 2, x_13);
lean_ctor_set(x_80, 3, x_14);
lean_ctor_set(x_80, 4, x_15);
lean_ctor_set(x_80, 5, x_16);
lean_ctor_set(x_80, 6, x_17);
lean_ctor_set_uint64(x_80, sizeof(void*)*7, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_80, sizeof(void*)*7 + 10, x_19);
x_81 = lean_apply_5(x_1, x_80, x_3, x_4, x_5, x_75);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
return x_81;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_81);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_81);
if (x_86 == 0)
{
return x_81;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_81, 0);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_81);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
x_90 = lean_ctor_get_uint8(x_41, 16);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; uint8_t x_93; lean_object* x_94; uint64_t x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_41);
lean_dec(x_2);
x_91 = lean_ctor_get(x_40, 1);
lean_inc(x_91);
lean_dec(x_40);
x_92 = 1;
x_93 = 2;
x_94 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_94, 0, x_20);
lean_ctor_set_uint8(x_94, 1, x_21);
lean_ctor_set_uint8(x_94, 2, x_22);
lean_ctor_set_uint8(x_94, 3, x_23);
lean_ctor_set_uint8(x_94, 4, x_24);
lean_ctor_set_uint8(x_94, 5, x_25);
lean_ctor_set_uint8(x_94, 6, x_26);
lean_ctor_set_uint8(x_94, 7, x_27);
lean_ctor_set_uint8(x_94, 8, x_28);
lean_ctor_set_uint8(x_94, 9, x_29);
lean_ctor_set_uint8(x_94, 10, x_30);
lean_ctor_set_uint8(x_94, 11, x_31);
lean_ctor_set_uint8(x_94, 12, x_92);
lean_ctor_set_uint8(x_94, 13, x_92);
lean_ctor_set_uint8(x_94, 14, x_93);
lean_ctor_set_uint8(x_94, 15, x_92);
lean_ctor_set_uint8(x_94, 16, x_92);
lean_ctor_set_uint8(x_94, 17, x_32);
x_95 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_94);
x_96 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_12);
lean_ctor_set(x_96, 2, x_13);
lean_ctor_set(x_96, 3, x_14);
lean_ctor_set(x_96, 4, x_15);
lean_ctor_set(x_96, 5, x_16);
lean_ctor_set(x_96, 6, x_17);
lean_ctor_set_uint64(x_96, sizeof(void*)*7, x_95);
lean_ctor_set_uint8(x_96, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_96, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_96, sizeof(void*)*7 + 10, x_19);
x_97 = lean_apply_5(x_1, x_96, x_3, x_4, x_5, x_91);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
return x_97;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_97);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_97);
if (x_102 == 0)
{
return x_97;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_97, 0);
x_104 = lean_ctor_get(x_97, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_97);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
lean_object* x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; 
x_106 = lean_ctor_get(x_40, 1);
lean_inc(x_106);
lean_dec(x_40);
x_107 = lean_ctor_get_uint8(x_41, 14);
lean_dec(x_41);
x_108 = 2;
x_109 = l_Lean_Meta_instDecidableEqProjReductionKind(x_107, x_108);
if (x_109 == 0)
{
uint8_t x_110; lean_object* x_111; uint64_t x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_2);
x_110 = 1;
x_111 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_111, 0, x_20);
lean_ctor_set_uint8(x_111, 1, x_21);
lean_ctor_set_uint8(x_111, 2, x_22);
lean_ctor_set_uint8(x_111, 3, x_23);
lean_ctor_set_uint8(x_111, 4, x_24);
lean_ctor_set_uint8(x_111, 5, x_25);
lean_ctor_set_uint8(x_111, 6, x_26);
lean_ctor_set_uint8(x_111, 7, x_27);
lean_ctor_set_uint8(x_111, 8, x_28);
lean_ctor_set_uint8(x_111, 9, x_29);
lean_ctor_set_uint8(x_111, 10, x_30);
lean_ctor_set_uint8(x_111, 11, x_31);
lean_ctor_set_uint8(x_111, 12, x_110);
lean_ctor_set_uint8(x_111, 13, x_110);
lean_ctor_set_uint8(x_111, 14, x_108);
lean_ctor_set_uint8(x_111, 15, x_110);
lean_ctor_set_uint8(x_111, 16, x_110);
lean_ctor_set_uint8(x_111, 17, x_32);
x_112 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_111);
x_113 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_12);
lean_ctor_set(x_113, 2, x_13);
lean_ctor_set(x_113, 3, x_14);
lean_ctor_set(x_113, 4, x_15);
lean_ctor_set(x_113, 5, x_16);
lean_ctor_set(x_113, 6, x_17);
lean_ctor_set_uint64(x_113, sizeof(void*)*7, x_112);
lean_ctor_set_uint8(x_113, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_113, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_113, sizeof(void*)*7 + 10, x_19);
x_114 = lean_apply_5(x_1, x_113, x_3, x_4, x_5, x_106);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
return x_114;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_114, 0);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_114);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
else
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_114);
if (x_119 == 0)
{
return x_114;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_114, 0);
x_121 = lean_ctor_get(x_114, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_114);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
lean_object* x_123; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_123 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_106);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
return x_123;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_123);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
else
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_123);
if (x_128 == 0)
{
return x_123;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_123, 0);
x_130 = lean_ctor_get(x_123, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_123);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
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
uint64_t x_132; uint64_t x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_ctor_set_uint8(x_8, 9, x_33);
x_132 = l_Lean_Meta_withInferTypeConfig___rarg___closed__1;
x_133 = lean_uint64_lor(x_37, x_132);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_133);
x_134 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get_uint8(x_135, 13);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; uint8_t x_139; lean_object* x_140; uint64_t x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_135);
lean_dec(x_2);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = 1;
x_139 = 2;
x_140 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_140, 0, x_20);
lean_ctor_set_uint8(x_140, 1, x_21);
lean_ctor_set_uint8(x_140, 2, x_22);
lean_ctor_set_uint8(x_140, 3, x_23);
lean_ctor_set_uint8(x_140, 4, x_24);
lean_ctor_set_uint8(x_140, 5, x_25);
lean_ctor_set_uint8(x_140, 6, x_26);
lean_ctor_set_uint8(x_140, 7, x_27);
lean_ctor_set_uint8(x_140, 8, x_28);
lean_ctor_set_uint8(x_140, 9, x_33);
lean_ctor_set_uint8(x_140, 10, x_30);
lean_ctor_set_uint8(x_140, 11, x_31);
lean_ctor_set_uint8(x_140, 12, x_138);
lean_ctor_set_uint8(x_140, 13, x_138);
lean_ctor_set_uint8(x_140, 14, x_139);
lean_ctor_set_uint8(x_140, 15, x_138);
lean_ctor_set_uint8(x_140, 16, x_138);
lean_ctor_set_uint8(x_140, 17, x_32);
x_141 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_140);
x_142 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_12);
lean_ctor_set(x_142, 2, x_13);
lean_ctor_set(x_142, 3, x_14);
lean_ctor_set(x_142, 4, x_15);
lean_ctor_set(x_142, 5, x_16);
lean_ctor_set(x_142, 6, x_17);
lean_ctor_set_uint64(x_142, sizeof(void*)*7, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_142, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_142, sizeof(void*)*7 + 10, x_19);
x_143 = lean_apply_5(x_1, x_142, x_3, x_4, x_5, x_137);
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
uint8_t x_152; 
x_152 = lean_ctor_get_uint8(x_135, 12);
if (x_152 == 0)
{
lean_object* x_153; uint8_t x_154; uint8_t x_155; lean_object* x_156; uint64_t x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_135);
lean_dec(x_2);
x_153 = lean_ctor_get(x_134, 1);
lean_inc(x_153);
lean_dec(x_134);
x_154 = 1;
x_155 = 2;
x_156 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_156, 0, x_20);
lean_ctor_set_uint8(x_156, 1, x_21);
lean_ctor_set_uint8(x_156, 2, x_22);
lean_ctor_set_uint8(x_156, 3, x_23);
lean_ctor_set_uint8(x_156, 4, x_24);
lean_ctor_set_uint8(x_156, 5, x_25);
lean_ctor_set_uint8(x_156, 6, x_26);
lean_ctor_set_uint8(x_156, 7, x_27);
lean_ctor_set_uint8(x_156, 8, x_28);
lean_ctor_set_uint8(x_156, 9, x_33);
lean_ctor_set_uint8(x_156, 10, x_30);
lean_ctor_set_uint8(x_156, 11, x_31);
lean_ctor_set_uint8(x_156, 12, x_154);
lean_ctor_set_uint8(x_156, 13, x_154);
lean_ctor_set_uint8(x_156, 14, x_155);
lean_ctor_set_uint8(x_156, 15, x_154);
lean_ctor_set_uint8(x_156, 16, x_154);
lean_ctor_set_uint8(x_156, 17, x_32);
x_157 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_156);
x_158 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_12);
lean_ctor_set(x_158, 2, x_13);
lean_ctor_set(x_158, 3, x_14);
lean_ctor_set(x_158, 4, x_15);
lean_ctor_set(x_158, 5, x_16);
lean_ctor_set(x_158, 6, x_17);
lean_ctor_set_uint64(x_158, sizeof(void*)*7, x_157);
lean_ctor_set_uint8(x_158, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_158, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_158, sizeof(void*)*7 + 10, x_19);
x_159 = lean_apply_5(x_1, x_158, x_3, x_4, x_5, x_153);
if (lean_obj_tag(x_159) == 0)
{
uint8_t x_160; 
x_160 = !lean_is_exclusive(x_159);
if (x_160 == 0)
{
return x_159;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_159, 0);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_159);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
else
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_159);
if (x_164 == 0)
{
return x_159;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_159, 0);
x_166 = lean_ctor_get(x_159, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_159);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
else
{
uint8_t x_168; 
x_168 = lean_ctor_get_uint8(x_135, 15);
if (x_168 == 0)
{
lean_object* x_169; uint8_t x_170; uint8_t x_171; lean_object* x_172; uint64_t x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_135);
lean_dec(x_2);
x_169 = lean_ctor_get(x_134, 1);
lean_inc(x_169);
lean_dec(x_134);
x_170 = 1;
x_171 = 2;
x_172 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_172, 0, x_20);
lean_ctor_set_uint8(x_172, 1, x_21);
lean_ctor_set_uint8(x_172, 2, x_22);
lean_ctor_set_uint8(x_172, 3, x_23);
lean_ctor_set_uint8(x_172, 4, x_24);
lean_ctor_set_uint8(x_172, 5, x_25);
lean_ctor_set_uint8(x_172, 6, x_26);
lean_ctor_set_uint8(x_172, 7, x_27);
lean_ctor_set_uint8(x_172, 8, x_28);
lean_ctor_set_uint8(x_172, 9, x_33);
lean_ctor_set_uint8(x_172, 10, x_30);
lean_ctor_set_uint8(x_172, 11, x_31);
lean_ctor_set_uint8(x_172, 12, x_170);
lean_ctor_set_uint8(x_172, 13, x_170);
lean_ctor_set_uint8(x_172, 14, x_171);
lean_ctor_set_uint8(x_172, 15, x_170);
lean_ctor_set_uint8(x_172, 16, x_170);
lean_ctor_set_uint8(x_172, 17, x_32);
x_173 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_172);
x_174 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_12);
lean_ctor_set(x_174, 2, x_13);
lean_ctor_set(x_174, 3, x_14);
lean_ctor_set(x_174, 4, x_15);
lean_ctor_set(x_174, 5, x_16);
lean_ctor_set(x_174, 6, x_17);
lean_ctor_set_uint64(x_174, sizeof(void*)*7, x_173);
lean_ctor_set_uint8(x_174, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_174, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_174, sizeof(void*)*7 + 10, x_19);
x_175 = lean_apply_5(x_1, x_174, x_3, x_4, x_5, x_169);
if (lean_obj_tag(x_175) == 0)
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
return x_175;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_175, 0);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_175);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
else
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_175);
if (x_180 == 0)
{
return x_175;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_175, 0);
x_182 = lean_ctor_get(x_175, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_175);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
uint8_t x_184; 
x_184 = lean_ctor_get_uint8(x_135, 16);
if (x_184 == 0)
{
lean_object* x_185; uint8_t x_186; uint8_t x_187; lean_object* x_188; uint64_t x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_135);
lean_dec(x_2);
x_185 = lean_ctor_get(x_134, 1);
lean_inc(x_185);
lean_dec(x_134);
x_186 = 1;
x_187 = 2;
x_188 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_188, 0, x_20);
lean_ctor_set_uint8(x_188, 1, x_21);
lean_ctor_set_uint8(x_188, 2, x_22);
lean_ctor_set_uint8(x_188, 3, x_23);
lean_ctor_set_uint8(x_188, 4, x_24);
lean_ctor_set_uint8(x_188, 5, x_25);
lean_ctor_set_uint8(x_188, 6, x_26);
lean_ctor_set_uint8(x_188, 7, x_27);
lean_ctor_set_uint8(x_188, 8, x_28);
lean_ctor_set_uint8(x_188, 9, x_33);
lean_ctor_set_uint8(x_188, 10, x_30);
lean_ctor_set_uint8(x_188, 11, x_31);
lean_ctor_set_uint8(x_188, 12, x_186);
lean_ctor_set_uint8(x_188, 13, x_186);
lean_ctor_set_uint8(x_188, 14, x_187);
lean_ctor_set_uint8(x_188, 15, x_186);
lean_ctor_set_uint8(x_188, 16, x_186);
lean_ctor_set_uint8(x_188, 17, x_32);
x_189 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_188);
x_190 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_12);
lean_ctor_set(x_190, 2, x_13);
lean_ctor_set(x_190, 3, x_14);
lean_ctor_set(x_190, 4, x_15);
lean_ctor_set(x_190, 5, x_16);
lean_ctor_set(x_190, 6, x_17);
lean_ctor_set_uint64(x_190, sizeof(void*)*7, x_189);
lean_ctor_set_uint8(x_190, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_190, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_190, sizeof(void*)*7 + 10, x_19);
x_191 = lean_apply_5(x_1, x_190, x_3, x_4, x_5, x_185);
if (lean_obj_tag(x_191) == 0)
{
uint8_t x_192; 
x_192 = !lean_is_exclusive(x_191);
if (x_192 == 0)
{
return x_191;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_191, 0);
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_191);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
else
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_191);
if (x_196 == 0)
{
return x_191;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_191, 0);
x_198 = lean_ctor_get(x_191, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_191);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
else
{
lean_object* x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; 
x_200 = lean_ctor_get(x_134, 1);
lean_inc(x_200);
lean_dec(x_134);
x_201 = lean_ctor_get_uint8(x_135, 14);
lean_dec(x_135);
x_202 = 2;
x_203 = l_Lean_Meta_instDecidableEqProjReductionKind(x_201, x_202);
if (x_203 == 0)
{
uint8_t x_204; lean_object* x_205; uint64_t x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_2);
x_204 = 1;
x_205 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_205, 0, x_20);
lean_ctor_set_uint8(x_205, 1, x_21);
lean_ctor_set_uint8(x_205, 2, x_22);
lean_ctor_set_uint8(x_205, 3, x_23);
lean_ctor_set_uint8(x_205, 4, x_24);
lean_ctor_set_uint8(x_205, 5, x_25);
lean_ctor_set_uint8(x_205, 6, x_26);
lean_ctor_set_uint8(x_205, 7, x_27);
lean_ctor_set_uint8(x_205, 8, x_28);
lean_ctor_set_uint8(x_205, 9, x_33);
lean_ctor_set_uint8(x_205, 10, x_30);
lean_ctor_set_uint8(x_205, 11, x_31);
lean_ctor_set_uint8(x_205, 12, x_204);
lean_ctor_set_uint8(x_205, 13, x_204);
lean_ctor_set_uint8(x_205, 14, x_202);
lean_ctor_set_uint8(x_205, 15, x_204);
lean_ctor_set_uint8(x_205, 16, x_204);
lean_ctor_set_uint8(x_205, 17, x_32);
x_206 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_205);
x_207 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_12);
lean_ctor_set(x_207, 2, x_13);
lean_ctor_set(x_207, 3, x_14);
lean_ctor_set(x_207, 4, x_15);
lean_ctor_set(x_207, 5, x_16);
lean_ctor_set(x_207, 6, x_17);
lean_ctor_set_uint64(x_207, sizeof(void*)*7, x_206);
lean_ctor_set_uint8(x_207, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_207, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_207, sizeof(void*)*7 + 10, x_19);
x_208 = lean_apply_5(x_1, x_207, x_3, x_4, x_5, x_200);
if (lean_obj_tag(x_208) == 0)
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_208);
if (x_209 == 0)
{
return x_208;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_208, 0);
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_208);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
else
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_208);
if (x_213 == 0)
{
return x_208;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_208, 0);
x_215 = lean_ctor_get(x_208, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_208);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
else
{
lean_object* x_217; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_217 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_200);
if (lean_obj_tag(x_217) == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
return x_217;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_217, 0);
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_217);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
else
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_217);
if (x_222 == 0)
{
return x_217;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_217, 0);
x_224 = lean_ctor_get(x_217, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_217);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
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
uint64_t x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; uint8_t x_235; uint8_t x_236; uint8_t x_237; uint8_t x_238; uint8_t x_239; uint8_t x_240; uint8_t x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; uint8_t x_245; uint8_t x_246; uint8_t x_247; uint8_t x_248; uint8_t x_249; uint8_t x_250; uint8_t x_251; uint8_t x_252; uint8_t x_253; uint8_t x_254; uint8_t x_255; uint64_t x_256; uint64_t x_257; uint64_t x_258; 
x_226 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_227 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_228 = lean_ctor_get(x_2, 1);
x_229 = lean_ctor_get(x_2, 2);
x_230 = lean_ctor_get(x_2, 3);
x_231 = lean_ctor_get(x_2, 4);
x_232 = lean_ctor_get(x_2, 5);
x_233 = lean_ctor_get(x_2, 6);
x_234 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_235 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
x_236 = lean_ctor_get_uint8(x_8, 0);
x_237 = lean_ctor_get_uint8(x_8, 1);
x_238 = lean_ctor_get_uint8(x_8, 2);
x_239 = lean_ctor_get_uint8(x_8, 3);
x_240 = lean_ctor_get_uint8(x_8, 4);
x_241 = lean_ctor_get_uint8(x_8, 5);
x_242 = lean_ctor_get_uint8(x_8, 6);
x_243 = lean_ctor_get_uint8(x_8, 7);
x_244 = lean_ctor_get_uint8(x_8, 8);
x_245 = lean_ctor_get_uint8(x_8, 9);
x_246 = lean_ctor_get_uint8(x_8, 10);
x_247 = lean_ctor_get_uint8(x_8, 11);
x_248 = lean_ctor_get_uint8(x_8, 12);
x_249 = lean_ctor_get_uint8(x_8, 13);
x_250 = lean_ctor_get_uint8(x_8, 14);
x_251 = lean_ctor_get_uint8(x_8, 15);
x_252 = lean_ctor_get_uint8(x_8, 16);
x_253 = lean_ctor_get_uint8(x_8, 17);
lean_dec(x_8);
x_254 = 1;
x_255 = l_Lean_Meta_TransparencyMode_lt(x_245, x_254);
x_256 = 2;
x_257 = lean_uint64_shift_right(x_226, x_256);
x_258 = lean_uint64_shift_left(x_257, x_256);
if (x_255 == 0)
{
lean_object* x_259; uint64_t x_260; uint64_t x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_259 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_259, 0, x_236);
lean_ctor_set_uint8(x_259, 1, x_237);
lean_ctor_set_uint8(x_259, 2, x_238);
lean_ctor_set_uint8(x_259, 3, x_239);
lean_ctor_set_uint8(x_259, 4, x_240);
lean_ctor_set_uint8(x_259, 5, x_241);
lean_ctor_set_uint8(x_259, 6, x_242);
lean_ctor_set_uint8(x_259, 7, x_243);
lean_ctor_set_uint8(x_259, 8, x_244);
lean_ctor_set_uint8(x_259, 9, x_245);
lean_ctor_set_uint8(x_259, 10, x_246);
lean_ctor_set_uint8(x_259, 11, x_247);
lean_ctor_set_uint8(x_259, 12, x_248);
lean_ctor_set_uint8(x_259, 13, x_249);
lean_ctor_set_uint8(x_259, 14, x_250);
lean_ctor_set_uint8(x_259, 15, x_251);
lean_ctor_set_uint8(x_259, 16, x_252);
lean_ctor_set_uint8(x_259, 17, x_253);
x_260 = l_Lean_Meta_TransparencyMode_toUInt64(x_245);
x_261 = lean_uint64_lor(x_258, x_260);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_ctor_set(x_2, 0, x_259);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_261);
x_262 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get_uint8(x_263, 13);
if (x_264 == 0)
{
lean_object* x_265; uint8_t x_266; uint8_t x_267; lean_object* x_268; uint64_t x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_263);
lean_dec(x_2);
x_265 = lean_ctor_get(x_262, 1);
lean_inc(x_265);
lean_dec(x_262);
x_266 = 1;
x_267 = 2;
x_268 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_268, 0, x_236);
lean_ctor_set_uint8(x_268, 1, x_237);
lean_ctor_set_uint8(x_268, 2, x_238);
lean_ctor_set_uint8(x_268, 3, x_239);
lean_ctor_set_uint8(x_268, 4, x_240);
lean_ctor_set_uint8(x_268, 5, x_241);
lean_ctor_set_uint8(x_268, 6, x_242);
lean_ctor_set_uint8(x_268, 7, x_243);
lean_ctor_set_uint8(x_268, 8, x_244);
lean_ctor_set_uint8(x_268, 9, x_245);
lean_ctor_set_uint8(x_268, 10, x_246);
lean_ctor_set_uint8(x_268, 11, x_247);
lean_ctor_set_uint8(x_268, 12, x_266);
lean_ctor_set_uint8(x_268, 13, x_266);
lean_ctor_set_uint8(x_268, 14, x_267);
lean_ctor_set_uint8(x_268, 15, x_266);
lean_ctor_set_uint8(x_268, 16, x_266);
lean_ctor_set_uint8(x_268, 17, x_253);
x_269 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_268);
x_270 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_228);
lean_ctor_set(x_270, 2, x_229);
lean_ctor_set(x_270, 3, x_230);
lean_ctor_set(x_270, 4, x_231);
lean_ctor_set(x_270, 5, x_232);
lean_ctor_set(x_270, 6, x_233);
lean_ctor_set_uint64(x_270, sizeof(void*)*7, x_269);
lean_ctor_set_uint8(x_270, sizeof(void*)*7 + 8, x_227);
lean_ctor_set_uint8(x_270, sizeof(void*)*7 + 9, x_234);
lean_ctor_set_uint8(x_270, sizeof(void*)*7 + 10, x_235);
x_271 = lean_apply_5(x_1, x_270, x_3, x_4, x_5, x_265);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
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
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_271, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_271, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_278 = x_271;
} else {
 lean_dec_ref(x_271);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
}
else
{
uint8_t x_280; 
x_280 = lean_ctor_get_uint8(x_263, 12);
if (x_280 == 0)
{
lean_object* x_281; uint8_t x_282; uint8_t x_283; lean_object* x_284; uint64_t x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_263);
lean_dec(x_2);
x_281 = lean_ctor_get(x_262, 1);
lean_inc(x_281);
lean_dec(x_262);
x_282 = 1;
x_283 = 2;
x_284 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_284, 0, x_236);
lean_ctor_set_uint8(x_284, 1, x_237);
lean_ctor_set_uint8(x_284, 2, x_238);
lean_ctor_set_uint8(x_284, 3, x_239);
lean_ctor_set_uint8(x_284, 4, x_240);
lean_ctor_set_uint8(x_284, 5, x_241);
lean_ctor_set_uint8(x_284, 6, x_242);
lean_ctor_set_uint8(x_284, 7, x_243);
lean_ctor_set_uint8(x_284, 8, x_244);
lean_ctor_set_uint8(x_284, 9, x_245);
lean_ctor_set_uint8(x_284, 10, x_246);
lean_ctor_set_uint8(x_284, 11, x_247);
lean_ctor_set_uint8(x_284, 12, x_282);
lean_ctor_set_uint8(x_284, 13, x_282);
lean_ctor_set_uint8(x_284, 14, x_283);
lean_ctor_set_uint8(x_284, 15, x_282);
lean_ctor_set_uint8(x_284, 16, x_282);
lean_ctor_set_uint8(x_284, 17, x_253);
x_285 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_284);
x_286 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_228);
lean_ctor_set(x_286, 2, x_229);
lean_ctor_set(x_286, 3, x_230);
lean_ctor_set(x_286, 4, x_231);
lean_ctor_set(x_286, 5, x_232);
lean_ctor_set(x_286, 6, x_233);
lean_ctor_set_uint64(x_286, sizeof(void*)*7, x_285);
lean_ctor_set_uint8(x_286, sizeof(void*)*7 + 8, x_227);
lean_ctor_set_uint8(x_286, sizeof(void*)*7 + 9, x_234);
lean_ctor_set_uint8(x_286, sizeof(void*)*7 + 10, x_235);
x_287 = lean_apply_5(x_1, x_286, x_3, x_4, x_5, x_281);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_290 = x_287;
} else {
 lean_dec_ref(x_287);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_289);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_287, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_287, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_294 = x_287;
} else {
 lean_dec_ref(x_287);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(1, 2, 0);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_292);
lean_ctor_set(x_295, 1, x_293);
return x_295;
}
}
else
{
uint8_t x_296; 
x_296 = lean_ctor_get_uint8(x_263, 15);
if (x_296 == 0)
{
lean_object* x_297; uint8_t x_298; uint8_t x_299; lean_object* x_300; uint64_t x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_263);
lean_dec(x_2);
x_297 = lean_ctor_get(x_262, 1);
lean_inc(x_297);
lean_dec(x_262);
x_298 = 1;
x_299 = 2;
x_300 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_300, 0, x_236);
lean_ctor_set_uint8(x_300, 1, x_237);
lean_ctor_set_uint8(x_300, 2, x_238);
lean_ctor_set_uint8(x_300, 3, x_239);
lean_ctor_set_uint8(x_300, 4, x_240);
lean_ctor_set_uint8(x_300, 5, x_241);
lean_ctor_set_uint8(x_300, 6, x_242);
lean_ctor_set_uint8(x_300, 7, x_243);
lean_ctor_set_uint8(x_300, 8, x_244);
lean_ctor_set_uint8(x_300, 9, x_245);
lean_ctor_set_uint8(x_300, 10, x_246);
lean_ctor_set_uint8(x_300, 11, x_247);
lean_ctor_set_uint8(x_300, 12, x_298);
lean_ctor_set_uint8(x_300, 13, x_298);
lean_ctor_set_uint8(x_300, 14, x_299);
lean_ctor_set_uint8(x_300, 15, x_298);
lean_ctor_set_uint8(x_300, 16, x_298);
lean_ctor_set_uint8(x_300, 17, x_253);
x_301 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_300);
x_302 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_228);
lean_ctor_set(x_302, 2, x_229);
lean_ctor_set(x_302, 3, x_230);
lean_ctor_set(x_302, 4, x_231);
lean_ctor_set(x_302, 5, x_232);
lean_ctor_set(x_302, 6, x_233);
lean_ctor_set_uint64(x_302, sizeof(void*)*7, x_301);
lean_ctor_set_uint8(x_302, sizeof(void*)*7 + 8, x_227);
lean_ctor_set_uint8(x_302, sizeof(void*)*7 + 9, x_234);
lean_ctor_set_uint8(x_302, sizeof(void*)*7 + 10, x_235);
x_303 = lean_apply_5(x_1, x_302, x_3, x_4, x_5, x_297);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_306 = x_303;
} else {
 lean_dec_ref(x_303);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_304);
lean_ctor_set(x_307, 1, x_305);
return x_307;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_308 = lean_ctor_get(x_303, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_303, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_310 = x_303;
} else {
 lean_dec_ref(x_303);
 x_310 = lean_box(0);
}
if (lean_is_scalar(x_310)) {
 x_311 = lean_alloc_ctor(1, 2, 0);
} else {
 x_311 = x_310;
}
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_309);
return x_311;
}
}
else
{
uint8_t x_312; 
x_312 = lean_ctor_get_uint8(x_263, 16);
if (x_312 == 0)
{
lean_object* x_313; uint8_t x_314; uint8_t x_315; lean_object* x_316; uint64_t x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_263);
lean_dec(x_2);
x_313 = lean_ctor_get(x_262, 1);
lean_inc(x_313);
lean_dec(x_262);
x_314 = 1;
x_315 = 2;
x_316 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_316, 0, x_236);
lean_ctor_set_uint8(x_316, 1, x_237);
lean_ctor_set_uint8(x_316, 2, x_238);
lean_ctor_set_uint8(x_316, 3, x_239);
lean_ctor_set_uint8(x_316, 4, x_240);
lean_ctor_set_uint8(x_316, 5, x_241);
lean_ctor_set_uint8(x_316, 6, x_242);
lean_ctor_set_uint8(x_316, 7, x_243);
lean_ctor_set_uint8(x_316, 8, x_244);
lean_ctor_set_uint8(x_316, 9, x_245);
lean_ctor_set_uint8(x_316, 10, x_246);
lean_ctor_set_uint8(x_316, 11, x_247);
lean_ctor_set_uint8(x_316, 12, x_314);
lean_ctor_set_uint8(x_316, 13, x_314);
lean_ctor_set_uint8(x_316, 14, x_315);
lean_ctor_set_uint8(x_316, 15, x_314);
lean_ctor_set_uint8(x_316, 16, x_314);
lean_ctor_set_uint8(x_316, 17, x_253);
x_317 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_316);
x_318 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_228);
lean_ctor_set(x_318, 2, x_229);
lean_ctor_set(x_318, 3, x_230);
lean_ctor_set(x_318, 4, x_231);
lean_ctor_set(x_318, 5, x_232);
lean_ctor_set(x_318, 6, x_233);
lean_ctor_set_uint64(x_318, sizeof(void*)*7, x_317);
lean_ctor_set_uint8(x_318, sizeof(void*)*7 + 8, x_227);
lean_ctor_set_uint8(x_318, sizeof(void*)*7 + 9, x_234);
lean_ctor_set_uint8(x_318, sizeof(void*)*7 + 10, x_235);
x_319 = lean_apply_5(x_1, x_318, x_3, x_4, x_5, x_313);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_322 = x_319;
} else {
 lean_dec_ref(x_319);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
return x_323;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_324 = lean_ctor_get(x_319, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_319, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_326 = x_319;
} else {
 lean_dec_ref(x_319);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(1, 2, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_324);
lean_ctor_set(x_327, 1, x_325);
return x_327;
}
}
else
{
lean_object* x_328; uint8_t x_329; uint8_t x_330; uint8_t x_331; 
x_328 = lean_ctor_get(x_262, 1);
lean_inc(x_328);
lean_dec(x_262);
x_329 = lean_ctor_get_uint8(x_263, 14);
lean_dec(x_263);
x_330 = 2;
x_331 = l_Lean_Meta_instDecidableEqProjReductionKind(x_329, x_330);
if (x_331 == 0)
{
uint8_t x_332; lean_object* x_333; uint64_t x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_2);
x_332 = 1;
x_333 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_333, 0, x_236);
lean_ctor_set_uint8(x_333, 1, x_237);
lean_ctor_set_uint8(x_333, 2, x_238);
lean_ctor_set_uint8(x_333, 3, x_239);
lean_ctor_set_uint8(x_333, 4, x_240);
lean_ctor_set_uint8(x_333, 5, x_241);
lean_ctor_set_uint8(x_333, 6, x_242);
lean_ctor_set_uint8(x_333, 7, x_243);
lean_ctor_set_uint8(x_333, 8, x_244);
lean_ctor_set_uint8(x_333, 9, x_245);
lean_ctor_set_uint8(x_333, 10, x_246);
lean_ctor_set_uint8(x_333, 11, x_247);
lean_ctor_set_uint8(x_333, 12, x_332);
lean_ctor_set_uint8(x_333, 13, x_332);
lean_ctor_set_uint8(x_333, 14, x_330);
lean_ctor_set_uint8(x_333, 15, x_332);
lean_ctor_set_uint8(x_333, 16, x_332);
lean_ctor_set_uint8(x_333, 17, x_253);
x_334 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_333);
x_335 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_228);
lean_ctor_set(x_335, 2, x_229);
lean_ctor_set(x_335, 3, x_230);
lean_ctor_set(x_335, 4, x_231);
lean_ctor_set(x_335, 5, x_232);
lean_ctor_set(x_335, 6, x_233);
lean_ctor_set_uint64(x_335, sizeof(void*)*7, x_334);
lean_ctor_set_uint8(x_335, sizeof(void*)*7 + 8, x_227);
lean_ctor_set_uint8(x_335, sizeof(void*)*7 + 9, x_234);
lean_ctor_set_uint8(x_335, sizeof(void*)*7 + 10, x_235);
x_336 = lean_apply_5(x_1, x_335, x_3, x_4, x_5, x_328);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_339 = x_336;
} else {
 lean_dec_ref(x_336);
 x_339 = lean_box(0);
}
if (lean_is_scalar(x_339)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_339;
}
lean_ctor_set(x_340, 0, x_337);
lean_ctor_set(x_340, 1, x_338);
return x_340;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_341 = lean_ctor_get(x_336, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_336, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_343 = x_336;
} else {
 lean_dec_ref(x_336);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(1, 2, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_341);
lean_ctor_set(x_344, 1, x_342);
return x_344;
}
}
else
{
lean_object* x_345; 
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
x_345 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_328);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_348 = x_345;
} else {
 lean_dec_ref(x_345);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_346);
lean_ctor_set(x_349, 1, x_347);
return x_349;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_350 = lean_ctor_get(x_345, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_345, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_352 = x_345;
} else {
 lean_dec_ref(x_345);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 2, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_350);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
}
}
}
}
}
}
else
{
lean_object* x_354; uint64_t x_355; uint64_t x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; 
x_354 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_354, 0, x_236);
lean_ctor_set_uint8(x_354, 1, x_237);
lean_ctor_set_uint8(x_354, 2, x_238);
lean_ctor_set_uint8(x_354, 3, x_239);
lean_ctor_set_uint8(x_354, 4, x_240);
lean_ctor_set_uint8(x_354, 5, x_241);
lean_ctor_set_uint8(x_354, 6, x_242);
lean_ctor_set_uint8(x_354, 7, x_243);
lean_ctor_set_uint8(x_354, 8, x_244);
lean_ctor_set_uint8(x_354, 9, x_254);
lean_ctor_set_uint8(x_354, 10, x_246);
lean_ctor_set_uint8(x_354, 11, x_247);
lean_ctor_set_uint8(x_354, 12, x_248);
lean_ctor_set_uint8(x_354, 13, x_249);
lean_ctor_set_uint8(x_354, 14, x_250);
lean_ctor_set_uint8(x_354, 15, x_251);
lean_ctor_set_uint8(x_354, 16, x_252);
lean_ctor_set_uint8(x_354, 17, x_253);
x_355 = l_Lean_Meta_withInferTypeConfig___rarg___closed__1;
x_356 = lean_uint64_lor(x_258, x_355);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_ctor_set(x_2, 0, x_354);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_356);
x_357 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get_uint8(x_358, 13);
if (x_359 == 0)
{
lean_object* x_360; uint8_t x_361; uint8_t x_362; lean_object* x_363; uint64_t x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_358);
lean_dec(x_2);
x_360 = lean_ctor_get(x_357, 1);
lean_inc(x_360);
lean_dec(x_357);
x_361 = 1;
x_362 = 2;
x_363 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_363, 0, x_236);
lean_ctor_set_uint8(x_363, 1, x_237);
lean_ctor_set_uint8(x_363, 2, x_238);
lean_ctor_set_uint8(x_363, 3, x_239);
lean_ctor_set_uint8(x_363, 4, x_240);
lean_ctor_set_uint8(x_363, 5, x_241);
lean_ctor_set_uint8(x_363, 6, x_242);
lean_ctor_set_uint8(x_363, 7, x_243);
lean_ctor_set_uint8(x_363, 8, x_244);
lean_ctor_set_uint8(x_363, 9, x_254);
lean_ctor_set_uint8(x_363, 10, x_246);
lean_ctor_set_uint8(x_363, 11, x_247);
lean_ctor_set_uint8(x_363, 12, x_361);
lean_ctor_set_uint8(x_363, 13, x_361);
lean_ctor_set_uint8(x_363, 14, x_362);
lean_ctor_set_uint8(x_363, 15, x_361);
lean_ctor_set_uint8(x_363, 16, x_361);
lean_ctor_set_uint8(x_363, 17, x_253);
x_364 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_363);
x_365 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_228);
lean_ctor_set(x_365, 2, x_229);
lean_ctor_set(x_365, 3, x_230);
lean_ctor_set(x_365, 4, x_231);
lean_ctor_set(x_365, 5, x_232);
lean_ctor_set(x_365, 6, x_233);
lean_ctor_set_uint64(x_365, sizeof(void*)*7, x_364);
lean_ctor_set_uint8(x_365, sizeof(void*)*7 + 8, x_227);
lean_ctor_set_uint8(x_365, sizeof(void*)*7 + 9, x_234);
lean_ctor_set_uint8(x_365, sizeof(void*)*7 + 10, x_235);
x_366 = lean_apply_5(x_1, x_365, x_3, x_4, x_5, x_360);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_369 = x_366;
} else {
 lean_dec_ref(x_366);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_368);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_371 = lean_ctor_get(x_366, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_366, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_373 = x_366;
} else {
 lean_dec_ref(x_366);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(1, 2, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_372);
return x_374;
}
}
else
{
uint8_t x_375; 
x_375 = lean_ctor_get_uint8(x_358, 12);
if (x_375 == 0)
{
lean_object* x_376; uint8_t x_377; uint8_t x_378; lean_object* x_379; uint64_t x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_358);
lean_dec(x_2);
x_376 = lean_ctor_get(x_357, 1);
lean_inc(x_376);
lean_dec(x_357);
x_377 = 1;
x_378 = 2;
x_379 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_379, 0, x_236);
lean_ctor_set_uint8(x_379, 1, x_237);
lean_ctor_set_uint8(x_379, 2, x_238);
lean_ctor_set_uint8(x_379, 3, x_239);
lean_ctor_set_uint8(x_379, 4, x_240);
lean_ctor_set_uint8(x_379, 5, x_241);
lean_ctor_set_uint8(x_379, 6, x_242);
lean_ctor_set_uint8(x_379, 7, x_243);
lean_ctor_set_uint8(x_379, 8, x_244);
lean_ctor_set_uint8(x_379, 9, x_254);
lean_ctor_set_uint8(x_379, 10, x_246);
lean_ctor_set_uint8(x_379, 11, x_247);
lean_ctor_set_uint8(x_379, 12, x_377);
lean_ctor_set_uint8(x_379, 13, x_377);
lean_ctor_set_uint8(x_379, 14, x_378);
lean_ctor_set_uint8(x_379, 15, x_377);
lean_ctor_set_uint8(x_379, 16, x_377);
lean_ctor_set_uint8(x_379, 17, x_253);
x_380 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_379);
x_381 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_228);
lean_ctor_set(x_381, 2, x_229);
lean_ctor_set(x_381, 3, x_230);
lean_ctor_set(x_381, 4, x_231);
lean_ctor_set(x_381, 5, x_232);
lean_ctor_set(x_381, 6, x_233);
lean_ctor_set_uint64(x_381, sizeof(void*)*7, x_380);
lean_ctor_set_uint8(x_381, sizeof(void*)*7 + 8, x_227);
lean_ctor_set_uint8(x_381, sizeof(void*)*7 + 9, x_234);
lean_ctor_set_uint8(x_381, sizeof(void*)*7 + 10, x_235);
x_382 = lean_apply_5(x_1, x_381, x_3, x_4, x_5, x_376);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_385 = x_382;
} else {
 lean_dec_ref(x_382);
 x_385 = lean_box(0);
}
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_383);
lean_ctor_set(x_386, 1, x_384);
return x_386;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_387 = lean_ctor_get(x_382, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_382, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_389 = x_382;
} else {
 lean_dec_ref(x_382);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(1, 2, 0);
} else {
 x_390 = x_389;
}
lean_ctor_set(x_390, 0, x_387);
lean_ctor_set(x_390, 1, x_388);
return x_390;
}
}
else
{
uint8_t x_391; 
x_391 = lean_ctor_get_uint8(x_358, 15);
if (x_391 == 0)
{
lean_object* x_392; uint8_t x_393; uint8_t x_394; lean_object* x_395; uint64_t x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_358);
lean_dec(x_2);
x_392 = lean_ctor_get(x_357, 1);
lean_inc(x_392);
lean_dec(x_357);
x_393 = 1;
x_394 = 2;
x_395 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_395, 0, x_236);
lean_ctor_set_uint8(x_395, 1, x_237);
lean_ctor_set_uint8(x_395, 2, x_238);
lean_ctor_set_uint8(x_395, 3, x_239);
lean_ctor_set_uint8(x_395, 4, x_240);
lean_ctor_set_uint8(x_395, 5, x_241);
lean_ctor_set_uint8(x_395, 6, x_242);
lean_ctor_set_uint8(x_395, 7, x_243);
lean_ctor_set_uint8(x_395, 8, x_244);
lean_ctor_set_uint8(x_395, 9, x_254);
lean_ctor_set_uint8(x_395, 10, x_246);
lean_ctor_set_uint8(x_395, 11, x_247);
lean_ctor_set_uint8(x_395, 12, x_393);
lean_ctor_set_uint8(x_395, 13, x_393);
lean_ctor_set_uint8(x_395, 14, x_394);
lean_ctor_set_uint8(x_395, 15, x_393);
lean_ctor_set_uint8(x_395, 16, x_393);
lean_ctor_set_uint8(x_395, 17, x_253);
x_396 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_395);
x_397 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_228);
lean_ctor_set(x_397, 2, x_229);
lean_ctor_set(x_397, 3, x_230);
lean_ctor_set(x_397, 4, x_231);
lean_ctor_set(x_397, 5, x_232);
lean_ctor_set(x_397, 6, x_233);
lean_ctor_set_uint64(x_397, sizeof(void*)*7, x_396);
lean_ctor_set_uint8(x_397, sizeof(void*)*7 + 8, x_227);
lean_ctor_set_uint8(x_397, sizeof(void*)*7 + 9, x_234);
lean_ctor_set_uint8(x_397, sizeof(void*)*7 + 10, x_235);
x_398 = lean_apply_5(x_1, x_397, x_3, x_4, x_5, x_392);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_401 = x_398;
} else {
 lean_dec_ref(x_398);
 x_401 = lean_box(0);
}
if (lean_is_scalar(x_401)) {
 x_402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_402 = x_401;
}
lean_ctor_set(x_402, 0, x_399);
lean_ctor_set(x_402, 1, x_400);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_403 = lean_ctor_get(x_398, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_398, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_405 = x_398;
} else {
 lean_dec_ref(x_398);
 x_405 = lean_box(0);
}
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(1, 2, 0);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_403);
lean_ctor_set(x_406, 1, x_404);
return x_406;
}
}
else
{
uint8_t x_407; 
x_407 = lean_ctor_get_uint8(x_358, 16);
if (x_407 == 0)
{
lean_object* x_408; uint8_t x_409; uint8_t x_410; lean_object* x_411; uint64_t x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_358);
lean_dec(x_2);
x_408 = lean_ctor_get(x_357, 1);
lean_inc(x_408);
lean_dec(x_357);
x_409 = 1;
x_410 = 2;
x_411 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_411, 0, x_236);
lean_ctor_set_uint8(x_411, 1, x_237);
lean_ctor_set_uint8(x_411, 2, x_238);
lean_ctor_set_uint8(x_411, 3, x_239);
lean_ctor_set_uint8(x_411, 4, x_240);
lean_ctor_set_uint8(x_411, 5, x_241);
lean_ctor_set_uint8(x_411, 6, x_242);
lean_ctor_set_uint8(x_411, 7, x_243);
lean_ctor_set_uint8(x_411, 8, x_244);
lean_ctor_set_uint8(x_411, 9, x_254);
lean_ctor_set_uint8(x_411, 10, x_246);
lean_ctor_set_uint8(x_411, 11, x_247);
lean_ctor_set_uint8(x_411, 12, x_409);
lean_ctor_set_uint8(x_411, 13, x_409);
lean_ctor_set_uint8(x_411, 14, x_410);
lean_ctor_set_uint8(x_411, 15, x_409);
lean_ctor_set_uint8(x_411, 16, x_409);
lean_ctor_set_uint8(x_411, 17, x_253);
x_412 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_411);
x_413 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_228);
lean_ctor_set(x_413, 2, x_229);
lean_ctor_set(x_413, 3, x_230);
lean_ctor_set(x_413, 4, x_231);
lean_ctor_set(x_413, 5, x_232);
lean_ctor_set(x_413, 6, x_233);
lean_ctor_set_uint64(x_413, sizeof(void*)*7, x_412);
lean_ctor_set_uint8(x_413, sizeof(void*)*7 + 8, x_227);
lean_ctor_set_uint8(x_413, sizeof(void*)*7 + 9, x_234);
lean_ctor_set_uint8(x_413, sizeof(void*)*7 + 10, x_235);
x_414 = lean_apply_5(x_1, x_413, x_3, x_4, x_5, x_408);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_417 = x_414;
} else {
 lean_dec_ref(x_414);
 x_417 = lean_box(0);
}
if (lean_is_scalar(x_417)) {
 x_418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_418 = x_417;
}
lean_ctor_set(x_418, 0, x_415);
lean_ctor_set(x_418, 1, x_416);
return x_418;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_419 = lean_ctor_get(x_414, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_414, 1);
lean_inc(x_420);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_421 = x_414;
} else {
 lean_dec_ref(x_414);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(1, 2, 0);
} else {
 x_422 = x_421;
}
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_420);
return x_422;
}
}
else
{
lean_object* x_423; uint8_t x_424; uint8_t x_425; uint8_t x_426; 
x_423 = lean_ctor_get(x_357, 1);
lean_inc(x_423);
lean_dec(x_357);
x_424 = lean_ctor_get_uint8(x_358, 14);
lean_dec(x_358);
x_425 = 2;
x_426 = l_Lean_Meta_instDecidableEqProjReductionKind(x_424, x_425);
if (x_426 == 0)
{
uint8_t x_427; lean_object* x_428; uint64_t x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_2);
x_427 = 1;
x_428 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_428, 0, x_236);
lean_ctor_set_uint8(x_428, 1, x_237);
lean_ctor_set_uint8(x_428, 2, x_238);
lean_ctor_set_uint8(x_428, 3, x_239);
lean_ctor_set_uint8(x_428, 4, x_240);
lean_ctor_set_uint8(x_428, 5, x_241);
lean_ctor_set_uint8(x_428, 6, x_242);
lean_ctor_set_uint8(x_428, 7, x_243);
lean_ctor_set_uint8(x_428, 8, x_244);
lean_ctor_set_uint8(x_428, 9, x_254);
lean_ctor_set_uint8(x_428, 10, x_246);
lean_ctor_set_uint8(x_428, 11, x_247);
lean_ctor_set_uint8(x_428, 12, x_427);
lean_ctor_set_uint8(x_428, 13, x_427);
lean_ctor_set_uint8(x_428, 14, x_425);
lean_ctor_set_uint8(x_428, 15, x_427);
lean_ctor_set_uint8(x_428, 16, x_427);
lean_ctor_set_uint8(x_428, 17, x_253);
x_429 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_428);
x_430 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_430, 0, x_428);
lean_ctor_set(x_430, 1, x_228);
lean_ctor_set(x_430, 2, x_229);
lean_ctor_set(x_430, 3, x_230);
lean_ctor_set(x_430, 4, x_231);
lean_ctor_set(x_430, 5, x_232);
lean_ctor_set(x_430, 6, x_233);
lean_ctor_set_uint64(x_430, sizeof(void*)*7, x_429);
lean_ctor_set_uint8(x_430, sizeof(void*)*7 + 8, x_227);
lean_ctor_set_uint8(x_430, sizeof(void*)*7 + 9, x_234);
lean_ctor_set_uint8(x_430, sizeof(void*)*7 + 10, x_235);
x_431 = lean_apply_5(x_1, x_430, x_3, x_4, x_5, x_423);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_434 = x_431;
} else {
 lean_dec_ref(x_431);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_432);
lean_ctor_set(x_435, 1, x_433);
return x_435;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_436 = lean_ctor_get(x_431, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_431, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_438 = x_431;
} else {
 lean_dec_ref(x_431);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_436);
lean_ctor_set(x_439, 1, x_437);
return x_439;
}
}
else
{
lean_object* x_440; 
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
x_440 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_423);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_443 = x_440;
} else {
 lean_dec_ref(x_440);
 x_443 = lean_box(0);
}
if (lean_is_scalar(x_443)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_443;
}
lean_ctor_set(x_444, 0, x_441);
lean_ctor_set(x_444, 1, x_442);
return x_444;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_445 = lean_ctor_get(x_440, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_440, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_447 = x_440;
} else {
 lean_dec_ref(x_440);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 2, 0);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_446);
return x_448;
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
lean_object* x_449; uint64_t x_450; uint8_t x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; uint8_t x_459; uint8_t x_460; uint8_t x_461; uint8_t x_462; uint8_t x_463; uint8_t x_464; uint8_t x_465; uint8_t x_466; uint8_t x_467; uint8_t x_468; uint8_t x_469; uint8_t x_470; uint8_t x_471; uint8_t x_472; uint8_t x_473; uint8_t x_474; uint8_t x_475; uint8_t x_476; uint8_t x_477; lean_object* x_478; uint8_t x_479; uint8_t x_480; uint64_t x_481; uint64_t x_482; uint64_t x_483; 
x_449 = lean_ctor_get(x_2, 0);
x_450 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_451 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_452 = lean_ctor_get(x_2, 1);
x_453 = lean_ctor_get(x_2, 2);
x_454 = lean_ctor_get(x_2, 3);
x_455 = lean_ctor_get(x_2, 4);
x_456 = lean_ctor_get(x_2, 5);
x_457 = lean_ctor_get(x_2, 6);
x_458 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_459 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
lean_inc(x_457);
lean_inc(x_456);
lean_inc(x_455);
lean_inc(x_454);
lean_inc(x_453);
lean_inc(x_452);
lean_inc(x_449);
lean_dec(x_2);
x_460 = lean_ctor_get_uint8(x_449, 0);
x_461 = lean_ctor_get_uint8(x_449, 1);
x_462 = lean_ctor_get_uint8(x_449, 2);
x_463 = lean_ctor_get_uint8(x_449, 3);
x_464 = lean_ctor_get_uint8(x_449, 4);
x_465 = lean_ctor_get_uint8(x_449, 5);
x_466 = lean_ctor_get_uint8(x_449, 6);
x_467 = lean_ctor_get_uint8(x_449, 7);
x_468 = lean_ctor_get_uint8(x_449, 8);
x_469 = lean_ctor_get_uint8(x_449, 9);
x_470 = lean_ctor_get_uint8(x_449, 10);
x_471 = lean_ctor_get_uint8(x_449, 11);
x_472 = lean_ctor_get_uint8(x_449, 12);
x_473 = lean_ctor_get_uint8(x_449, 13);
x_474 = lean_ctor_get_uint8(x_449, 14);
x_475 = lean_ctor_get_uint8(x_449, 15);
x_476 = lean_ctor_get_uint8(x_449, 16);
x_477 = lean_ctor_get_uint8(x_449, 17);
if (lean_is_exclusive(x_449)) {
 x_478 = x_449;
} else {
 lean_dec_ref(x_449);
 x_478 = lean_box(0);
}
x_479 = 1;
x_480 = l_Lean_Meta_TransparencyMode_lt(x_469, x_479);
x_481 = 2;
x_482 = lean_uint64_shift_right(x_450, x_481);
x_483 = lean_uint64_shift_left(x_482, x_481);
if (x_480 == 0)
{
lean_object* x_484; uint64_t x_485; uint64_t x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; 
if (lean_is_scalar(x_478)) {
 x_484 = lean_alloc_ctor(0, 0, 18);
} else {
 x_484 = x_478;
}
lean_ctor_set_uint8(x_484, 0, x_460);
lean_ctor_set_uint8(x_484, 1, x_461);
lean_ctor_set_uint8(x_484, 2, x_462);
lean_ctor_set_uint8(x_484, 3, x_463);
lean_ctor_set_uint8(x_484, 4, x_464);
lean_ctor_set_uint8(x_484, 5, x_465);
lean_ctor_set_uint8(x_484, 6, x_466);
lean_ctor_set_uint8(x_484, 7, x_467);
lean_ctor_set_uint8(x_484, 8, x_468);
lean_ctor_set_uint8(x_484, 9, x_469);
lean_ctor_set_uint8(x_484, 10, x_470);
lean_ctor_set_uint8(x_484, 11, x_471);
lean_ctor_set_uint8(x_484, 12, x_472);
lean_ctor_set_uint8(x_484, 13, x_473);
lean_ctor_set_uint8(x_484, 14, x_474);
lean_ctor_set_uint8(x_484, 15, x_475);
lean_ctor_set_uint8(x_484, 16, x_476);
lean_ctor_set_uint8(x_484, 17, x_477);
x_485 = l_Lean_Meta_TransparencyMode_toUInt64(x_469);
x_486 = lean_uint64_lor(x_483, x_485);
lean_inc(x_457);
lean_inc(x_456);
lean_inc(x_455);
lean_inc(x_454);
lean_inc(x_453);
lean_inc(x_452);
x_487 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_487, 0, x_484);
lean_ctor_set(x_487, 1, x_452);
lean_ctor_set(x_487, 2, x_453);
lean_ctor_set(x_487, 3, x_454);
lean_ctor_set(x_487, 4, x_455);
lean_ctor_set(x_487, 5, x_456);
lean_ctor_set(x_487, 6, x_457);
lean_ctor_set_uint64(x_487, sizeof(void*)*7, x_486);
lean_ctor_set_uint8(x_487, sizeof(void*)*7 + 8, x_451);
lean_ctor_set_uint8(x_487, sizeof(void*)*7 + 9, x_458);
lean_ctor_set_uint8(x_487, sizeof(void*)*7 + 10, x_459);
x_488 = l_Lean_Meta_getConfig(x_487, x_3, x_4, x_5, x_6);
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
x_490 = lean_ctor_get_uint8(x_489, 13);
if (x_490 == 0)
{
lean_object* x_491; uint8_t x_492; uint8_t x_493; lean_object* x_494; uint64_t x_495; lean_object* x_496; lean_object* x_497; 
lean_dec(x_489);
lean_dec(x_487);
x_491 = lean_ctor_get(x_488, 1);
lean_inc(x_491);
lean_dec(x_488);
x_492 = 1;
x_493 = 2;
x_494 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_494, 0, x_460);
lean_ctor_set_uint8(x_494, 1, x_461);
lean_ctor_set_uint8(x_494, 2, x_462);
lean_ctor_set_uint8(x_494, 3, x_463);
lean_ctor_set_uint8(x_494, 4, x_464);
lean_ctor_set_uint8(x_494, 5, x_465);
lean_ctor_set_uint8(x_494, 6, x_466);
lean_ctor_set_uint8(x_494, 7, x_467);
lean_ctor_set_uint8(x_494, 8, x_468);
lean_ctor_set_uint8(x_494, 9, x_469);
lean_ctor_set_uint8(x_494, 10, x_470);
lean_ctor_set_uint8(x_494, 11, x_471);
lean_ctor_set_uint8(x_494, 12, x_492);
lean_ctor_set_uint8(x_494, 13, x_492);
lean_ctor_set_uint8(x_494, 14, x_493);
lean_ctor_set_uint8(x_494, 15, x_492);
lean_ctor_set_uint8(x_494, 16, x_492);
lean_ctor_set_uint8(x_494, 17, x_477);
x_495 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_494);
x_496 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set(x_496, 1, x_452);
lean_ctor_set(x_496, 2, x_453);
lean_ctor_set(x_496, 3, x_454);
lean_ctor_set(x_496, 4, x_455);
lean_ctor_set(x_496, 5, x_456);
lean_ctor_set(x_496, 6, x_457);
lean_ctor_set_uint64(x_496, sizeof(void*)*7, x_495);
lean_ctor_set_uint8(x_496, sizeof(void*)*7 + 8, x_451);
lean_ctor_set_uint8(x_496, sizeof(void*)*7 + 9, x_458);
lean_ctor_set_uint8(x_496, sizeof(void*)*7 + 10, x_459);
x_497 = lean_apply_5(x_1, x_496, x_3, x_4, x_5, x_491);
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 x_500 = x_497;
} else {
 lean_dec_ref(x_497);
 x_500 = lean_box(0);
}
if (lean_is_scalar(x_500)) {
 x_501 = lean_alloc_ctor(0, 2, 0);
} else {
 x_501 = x_500;
}
lean_ctor_set(x_501, 0, x_498);
lean_ctor_set(x_501, 1, x_499);
return x_501;
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_502 = lean_ctor_get(x_497, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_497, 1);
lean_inc(x_503);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 x_504 = x_497;
} else {
 lean_dec_ref(x_497);
 x_504 = lean_box(0);
}
if (lean_is_scalar(x_504)) {
 x_505 = lean_alloc_ctor(1, 2, 0);
} else {
 x_505 = x_504;
}
lean_ctor_set(x_505, 0, x_502);
lean_ctor_set(x_505, 1, x_503);
return x_505;
}
}
else
{
uint8_t x_506; 
x_506 = lean_ctor_get_uint8(x_489, 12);
if (x_506 == 0)
{
lean_object* x_507; uint8_t x_508; uint8_t x_509; lean_object* x_510; uint64_t x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_489);
lean_dec(x_487);
x_507 = lean_ctor_get(x_488, 1);
lean_inc(x_507);
lean_dec(x_488);
x_508 = 1;
x_509 = 2;
x_510 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_510, 0, x_460);
lean_ctor_set_uint8(x_510, 1, x_461);
lean_ctor_set_uint8(x_510, 2, x_462);
lean_ctor_set_uint8(x_510, 3, x_463);
lean_ctor_set_uint8(x_510, 4, x_464);
lean_ctor_set_uint8(x_510, 5, x_465);
lean_ctor_set_uint8(x_510, 6, x_466);
lean_ctor_set_uint8(x_510, 7, x_467);
lean_ctor_set_uint8(x_510, 8, x_468);
lean_ctor_set_uint8(x_510, 9, x_469);
lean_ctor_set_uint8(x_510, 10, x_470);
lean_ctor_set_uint8(x_510, 11, x_471);
lean_ctor_set_uint8(x_510, 12, x_508);
lean_ctor_set_uint8(x_510, 13, x_508);
lean_ctor_set_uint8(x_510, 14, x_509);
lean_ctor_set_uint8(x_510, 15, x_508);
lean_ctor_set_uint8(x_510, 16, x_508);
lean_ctor_set_uint8(x_510, 17, x_477);
x_511 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_510);
x_512 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_512, 0, x_510);
lean_ctor_set(x_512, 1, x_452);
lean_ctor_set(x_512, 2, x_453);
lean_ctor_set(x_512, 3, x_454);
lean_ctor_set(x_512, 4, x_455);
lean_ctor_set(x_512, 5, x_456);
lean_ctor_set(x_512, 6, x_457);
lean_ctor_set_uint64(x_512, sizeof(void*)*7, x_511);
lean_ctor_set_uint8(x_512, sizeof(void*)*7 + 8, x_451);
lean_ctor_set_uint8(x_512, sizeof(void*)*7 + 9, x_458);
lean_ctor_set_uint8(x_512, sizeof(void*)*7 + 10, x_459);
x_513 = lean_apply_5(x_1, x_512, x_3, x_4, x_5, x_507);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_516 = x_513;
} else {
 lean_dec_ref(x_513);
 x_516 = lean_box(0);
}
if (lean_is_scalar(x_516)) {
 x_517 = lean_alloc_ctor(0, 2, 0);
} else {
 x_517 = x_516;
}
lean_ctor_set(x_517, 0, x_514);
lean_ctor_set(x_517, 1, x_515);
return x_517;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_518 = lean_ctor_get(x_513, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_513, 1);
lean_inc(x_519);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_520 = x_513;
} else {
 lean_dec_ref(x_513);
 x_520 = lean_box(0);
}
if (lean_is_scalar(x_520)) {
 x_521 = lean_alloc_ctor(1, 2, 0);
} else {
 x_521 = x_520;
}
lean_ctor_set(x_521, 0, x_518);
lean_ctor_set(x_521, 1, x_519);
return x_521;
}
}
else
{
uint8_t x_522; 
x_522 = lean_ctor_get_uint8(x_489, 15);
if (x_522 == 0)
{
lean_object* x_523; uint8_t x_524; uint8_t x_525; lean_object* x_526; uint64_t x_527; lean_object* x_528; lean_object* x_529; 
lean_dec(x_489);
lean_dec(x_487);
x_523 = lean_ctor_get(x_488, 1);
lean_inc(x_523);
lean_dec(x_488);
x_524 = 1;
x_525 = 2;
x_526 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_526, 0, x_460);
lean_ctor_set_uint8(x_526, 1, x_461);
lean_ctor_set_uint8(x_526, 2, x_462);
lean_ctor_set_uint8(x_526, 3, x_463);
lean_ctor_set_uint8(x_526, 4, x_464);
lean_ctor_set_uint8(x_526, 5, x_465);
lean_ctor_set_uint8(x_526, 6, x_466);
lean_ctor_set_uint8(x_526, 7, x_467);
lean_ctor_set_uint8(x_526, 8, x_468);
lean_ctor_set_uint8(x_526, 9, x_469);
lean_ctor_set_uint8(x_526, 10, x_470);
lean_ctor_set_uint8(x_526, 11, x_471);
lean_ctor_set_uint8(x_526, 12, x_524);
lean_ctor_set_uint8(x_526, 13, x_524);
lean_ctor_set_uint8(x_526, 14, x_525);
lean_ctor_set_uint8(x_526, 15, x_524);
lean_ctor_set_uint8(x_526, 16, x_524);
lean_ctor_set_uint8(x_526, 17, x_477);
x_527 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_526);
x_528 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_528, 0, x_526);
lean_ctor_set(x_528, 1, x_452);
lean_ctor_set(x_528, 2, x_453);
lean_ctor_set(x_528, 3, x_454);
lean_ctor_set(x_528, 4, x_455);
lean_ctor_set(x_528, 5, x_456);
lean_ctor_set(x_528, 6, x_457);
lean_ctor_set_uint64(x_528, sizeof(void*)*7, x_527);
lean_ctor_set_uint8(x_528, sizeof(void*)*7 + 8, x_451);
lean_ctor_set_uint8(x_528, sizeof(void*)*7 + 9, x_458);
lean_ctor_set_uint8(x_528, sizeof(void*)*7 + 10, x_459);
x_529 = lean_apply_5(x_1, x_528, x_3, x_4, x_5, x_523);
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 x_532 = x_529;
} else {
 lean_dec_ref(x_529);
 x_532 = lean_box(0);
}
if (lean_is_scalar(x_532)) {
 x_533 = lean_alloc_ctor(0, 2, 0);
} else {
 x_533 = x_532;
}
lean_ctor_set(x_533, 0, x_530);
lean_ctor_set(x_533, 1, x_531);
return x_533;
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_534 = lean_ctor_get(x_529, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_529, 1);
lean_inc(x_535);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 x_536 = x_529;
} else {
 lean_dec_ref(x_529);
 x_536 = lean_box(0);
}
if (lean_is_scalar(x_536)) {
 x_537 = lean_alloc_ctor(1, 2, 0);
} else {
 x_537 = x_536;
}
lean_ctor_set(x_537, 0, x_534);
lean_ctor_set(x_537, 1, x_535);
return x_537;
}
}
else
{
uint8_t x_538; 
x_538 = lean_ctor_get_uint8(x_489, 16);
if (x_538 == 0)
{
lean_object* x_539; uint8_t x_540; uint8_t x_541; lean_object* x_542; uint64_t x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_489);
lean_dec(x_487);
x_539 = lean_ctor_get(x_488, 1);
lean_inc(x_539);
lean_dec(x_488);
x_540 = 1;
x_541 = 2;
x_542 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_542, 0, x_460);
lean_ctor_set_uint8(x_542, 1, x_461);
lean_ctor_set_uint8(x_542, 2, x_462);
lean_ctor_set_uint8(x_542, 3, x_463);
lean_ctor_set_uint8(x_542, 4, x_464);
lean_ctor_set_uint8(x_542, 5, x_465);
lean_ctor_set_uint8(x_542, 6, x_466);
lean_ctor_set_uint8(x_542, 7, x_467);
lean_ctor_set_uint8(x_542, 8, x_468);
lean_ctor_set_uint8(x_542, 9, x_469);
lean_ctor_set_uint8(x_542, 10, x_470);
lean_ctor_set_uint8(x_542, 11, x_471);
lean_ctor_set_uint8(x_542, 12, x_540);
lean_ctor_set_uint8(x_542, 13, x_540);
lean_ctor_set_uint8(x_542, 14, x_541);
lean_ctor_set_uint8(x_542, 15, x_540);
lean_ctor_set_uint8(x_542, 16, x_540);
lean_ctor_set_uint8(x_542, 17, x_477);
x_543 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_542);
x_544 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_452);
lean_ctor_set(x_544, 2, x_453);
lean_ctor_set(x_544, 3, x_454);
lean_ctor_set(x_544, 4, x_455);
lean_ctor_set(x_544, 5, x_456);
lean_ctor_set(x_544, 6, x_457);
lean_ctor_set_uint64(x_544, sizeof(void*)*7, x_543);
lean_ctor_set_uint8(x_544, sizeof(void*)*7 + 8, x_451);
lean_ctor_set_uint8(x_544, sizeof(void*)*7 + 9, x_458);
lean_ctor_set_uint8(x_544, sizeof(void*)*7 + 10, x_459);
x_545 = lean_apply_5(x_1, x_544, x_3, x_4, x_5, x_539);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_545, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 lean_ctor_release(x_545, 1);
 x_548 = x_545;
} else {
 lean_dec_ref(x_545);
 x_548 = lean_box(0);
}
if (lean_is_scalar(x_548)) {
 x_549 = lean_alloc_ctor(0, 2, 0);
} else {
 x_549 = x_548;
}
lean_ctor_set(x_549, 0, x_546);
lean_ctor_set(x_549, 1, x_547);
return x_549;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_550 = lean_ctor_get(x_545, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_545, 1);
lean_inc(x_551);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 lean_ctor_release(x_545, 1);
 x_552 = x_545;
} else {
 lean_dec_ref(x_545);
 x_552 = lean_box(0);
}
if (lean_is_scalar(x_552)) {
 x_553 = lean_alloc_ctor(1, 2, 0);
} else {
 x_553 = x_552;
}
lean_ctor_set(x_553, 0, x_550);
lean_ctor_set(x_553, 1, x_551);
return x_553;
}
}
else
{
lean_object* x_554; uint8_t x_555; uint8_t x_556; uint8_t x_557; 
x_554 = lean_ctor_get(x_488, 1);
lean_inc(x_554);
lean_dec(x_488);
x_555 = lean_ctor_get_uint8(x_489, 14);
lean_dec(x_489);
x_556 = 2;
x_557 = l_Lean_Meta_instDecidableEqProjReductionKind(x_555, x_556);
if (x_557 == 0)
{
uint8_t x_558; lean_object* x_559; uint64_t x_560; lean_object* x_561; lean_object* x_562; 
lean_dec(x_487);
x_558 = 1;
x_559 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_559, 0, x_460);
lean_ctor_set_uint8(x_559, 1, x_461);
lean_ctor_set_uint8(x_559, 2, x_462);
lean_ctor_set_uint8(x_559, 3, x_463);
lean_ctor_set_uint8(x_559, 4, x_464);
lean_ctor_set_uint8(x_559, 5, x_465);
lean_ctor_set_uint8(x_559, 6, x_466);
lean_ctor_set_uint8(x_559, 7, x_467);
lean_ctor_set_uint8(x_559, 8, x_468);
lean_ctor_set_uint8(x_559, 9, x_469);
lean_ctor_set_uint8(x_559, 10, x_470);
lean_ctor_set_uint8(x_559, 11, x_471);
lean_ctor_set_uint8(x_559, 12, x_558);
lean_ctor_set_uint8(x_559, 13, x_558);
lean_ctor_set_uint8(x_559, 14, x_556);
lean_ctor_set_uint8(x_559, 15, x_558);
lean_ctor_set_uint8(x_559, 16, x_558);
lean_ctor_set_uint8(x_559, 17, x_477);
x_560 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_559);
x_561 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_561, 0, x_559);
lean_ctor_set(x_561, 1, x_452);
lean_ctor_set(x_561, 2, x_453);
lean_ctor_set(x_561, 3, x_454);
lean_ctor_set(x_561, 4, x_455);
lean_ctor_set(x_561, 5, x_456);
lean_ctor_set(x_561, 6, x_457);
lean_ctor_set_uint64(x_561, sizeof(void*)*7, x_560);
lean_ctor_set_uint8(x_561, sizeof(void*)*7 + 8, x_451);
lean_ctor_set_uint8(x_561, sizeof(void*)*7 + 9, x_458);
lean_ctor_set_uint8(x_561, sizeof(void*)*7 + 10, x_459);
x_562 = lean_apply_5(x_1, x_561, x_3, x_4, x_5, x_554);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_562, 1);
lean_inc(x_564);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_565 = x_562;
} else {
 lean_dec_ref(x_562);
 x_565 = lean_box(0);
}
if (lean_is_scalar(x_565)) {
 x_566 = lean_alloc_ctor(0, 2, 0);
} else {
 x_566 = x_565;
}
lean_ctor_set(x_566, 0, x_563);
lean_ctor_set(x_566, 1, x_564);
return x_566;
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_567 = lean_ctor_get(x_562, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_562, 1);
lean_inc(x_568);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_569 = x_562;
} else {
 lean_dec_ref(x_562);
 x_569 = lean_box(0);
}
if (lean_is_scalar(x_569)) {
 x_570 = lean_alloc_ctor(1, 2, 0);
} else {
 x_570 = x_569;
}
lean_ctor_set(x_570, 0, x_567);
lean_ctor_set(x_570, 1, x_568);
return x_570;
}
}
else
{
lean_object* x_571; 
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_452);
x_571 = lean_apply_5(x_1, x_487, x_3, x_4, x_5, x_554);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_571, 1);
lean_inc(x_573);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 lean_ctor_release(x_571, 1);
 x_574 = x_571;
} else {
 lean_dec_ref(x_571);
 x_574 = lean_box(0);
}
if (lean_is_scalar(x_574)) {
 x_575 = lean_alloc_ctor(0, 2, 0);
} else {
 x_575 = x_574;
}
lean_ctor_set(x_575, 0, x_572);
lean_ctor_set(x_575, 1, x_573);
return x_575;
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_576 = lean_ctor_get(x_571, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_571, 1);
lean_inc(x_577);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 lean_ctor_release(x_571, 1);
 x_578 = x_571;
} else {
 lean_dec_ref(x_571);
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
}
}
}
}
}
else
{
lean_object* x_580; uint64_t x_581; uint64_t x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; uint8_t x_586; 
if (lean_is_scalar(x_478)) {
 x_580 = lean_alloc_ctor(0, 0, 18);
} else {
 x_580 = x_478;
}
lean_ctor_set_uint8(x_580, 0, x_460);
lean_ctor_set_uint8(x_580, 1, x_461);
lean_ctor_set_uint8(x_580, 2, x_462);
lean_ctor_set_uint8(x_580, 3, x_463);
lean_ctor_set_uint8(x_580, 4, x_464);
lean_ctor_set_uint8(x_580, 5, x_465);
lean_ctor_set_uint8(x_580, 6, x_466);
lean_ctor_set_uint8(x_580, 7, x_467);
lean_ctor_set_uint8(x_580, 8, x_468);
lean_ctor_set_uint8(x_580, 9, x_479);
lean_ctor_set_uint8(x_580, 10, x_470);
lean_ctor_set_uint8(x_580, 11, x_471);
lean_ctor_set_uint8(x_580, 12, x_472);
lean_ctor_set_uint8(x_580, 13, x_473);
lean_ctor_set_uint8(x_580, 14, x_474);
lean_ctor_set_uint8(x_580, 15, x_475);
lean_ctor_set_uint8(x_580, 16, x_476);
lean_ctor_set_uint8(x_580, 17, x_477);
x_581 = l_Lean_Meta_withInferTypeConfig___rarg___closed__1;
x_582 = lean_uint64_lor(x_483, x_581);
lean_inc(x_457);
lean_inc(x_456);
lean_inc(x_455);
lean_inc(x_454);
lean_inc(x_453);
lean_inc(x_452);
x_583 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_583, 0, x_580);
lean_ctor_set(x_583, 1, x_452);
lean_ctor_set(x_583, 2, x_453);
lean_ctor_set(x_583, 3, x_454);
lean_ctor_set(x_583, 4, x_455);
lean_ctor_set(x_583, 5, x_456);
lean_ctor_set(x_583, 6, x_457);
lean_ctor_set_uint64(x_583, sizeof(void*)*7, x_582);
lean_ctor_set_uint8(x_583, sizeof(void*)*7 + 8, x_451);
lean_ctor_set_uint8(x_583, sizeof(void*)*7 + 9, x_458);
lean_ctor_set_uint8(x_583, sizeof(void*)*7 + 10, x_459);
x_584 = l_Lean_Meta_getConfig(x_583, x_3, x_4, x_5, x_6);
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
x_586 = lean_ctor_get_uint8(x_585, 13);
if (x_586 == 0)
{
lean_object* x_587; uint8_t x_588; uint8_t x_589; lean_object* x_590; uint64_t x_591; lean_object* x_592; lean_object* x_593; 
lean_dec(x_585);
lean_dec(x_583);
x_587 = lean_ctor_get(x_584, 1);
lean_inc(x_587);
lean_dec(x_584);
x_588 = 1;
x_589 = 2;
x_590 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_590, 0, x_460);
lean_ctor_set_uint8(x_590, 1, x_461);
lean_ctor_set_uint8(x_590, 2, x_462);
lean_ctor_set_uint8(x_590, 3, x_463);
lean_ctor_set_uint8(x_590, 4, x_464);
lean_ctor_set_uint8(x_590, 5, x_465);
lean_ctor_set_uint8(x_590, 6, x_466);
lean_ctor_set_uint8(x_590, 7, x_467);
lean_ctor_set_uint8(x_590, 8, x_468);
lean_ctor_set_uint8(x_590, 9, x_479);
lean_ctor_set_uint8(x_590, 10, x_470);
lean_ctor_set_uint8(x_590, 11, x_471);
lean_ctor_set_uint8(x_590, 12, x_588);
lean_ctor_set_uint8(x_590, 13, x_588);
lean_ctor_set_uint8(x_590, 14, x_589);
lean_ctor_set_uint8(x_590, 15, x_588);
lean_ctor_set_uint8(x_590, 16, x_588);
lean_ctor_set_uint8(x_590, 17, x_477);
x_591 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_590);
x_592 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_452);
lean_ctor_set(x_592, 2, x_453);
lean_ctor_set(x_592, 3, x_454);
lean_ctor_set(x_592, 4, x_455);
lean_ctor_set(x_592, 5, x_456);
lean_ctor_set(x_592, 6, x_457);
lean_ctor_set_uint64(x_592, sizeof(void*)*7, x_591);
lean_ctor_set_uint8(x_592, sizeof(void*)*7 + 8, x_451);
lean_ctor_set_uint8(x_592, sizeof(void*)*7 + 9, x_458);
lean_ctor_set_uint8(x_592, sizeof(void*)*7 + 10, x_459);
x_593 = lean_apply_5(x_1, x_592, x_3, x_4, x_5, x_587);
if (lean_obj_tag(x_593) == 0)
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_594 = lean_ctor_get(x_593, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_593, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_593)) {
 lean_ctor_release(x_593, 0);
 lean_ctor_release(x_593, 1);
 x_596 = x_593;
} else {
 lean_dec_ref(x_593);
 x_596 = lean_box(0);
}
if (lean_is_scalar(x_596)) {
 x_597 = lean_alloc_ctor(0, 2, 0);
} else {
 x_597 = x_596;
}
lean_ctor_set(x_597, 0, x_594);
lean_ctor_set(x_597, 1, x_595);
return x_597;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_598 = lean_ctor_get(x_593, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_593, 1);
lean_inc(x_599);
if (lean_is_exclusive(x_593)) {
 lean_ctor_release(x_593, 0);
 lean_ctor_release(x_593, 1);
 x_600 = x_593;
} else {
 lean_dec_ref(x_593);
 x_600 = lean_box(0);
}
if (lean_is_scalar(x_600)) {
 x_601 = lean_alloc_ctor(1, 2, 0);
} else {
 x_601 = x_600;
}
lean_ctor_set(x_601, 0, x_598);
lean_ctor_set(x_601, 1, x_599);
return x_601;
}
}
else
{
uint8_t x_602; 
x_602 = lean_ctor_get_uint8(x_585, 12);
if (x_602 == 0)
{
lean_object* x_603; uint8_t x_604; uint8_t x_605; lean_object* x_606; uint64_t x_607; lean_object* x_608; lean_object* x_609; 
lean_dec(x_585);
lean_dec(x_583);
x_603 = lean_ctor_get(x_584, 1);
lean_inc(x_603);
lean_dec(x_584);
x_604 = 1;
x_605 = 2;
x_606 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_606, 0, x_460);
lean_ctor_set_uint8(x_606, 1, x_461);
lean_ctor_set_uint8(x_606, 2, x_462);
lean_ctor_set_uint8(x_606, 3, x_463);
lean_ctor_set_uint8(x_606, 4, x_464);
lean_ctor_set_uint8(x_606, 5, x_465);
lean_ctor_set_uint8(x_606, 6, x_466);
lean_ctor_set_uint8(x_606, 7, x_467);
lean_ctor_set_uint8(x_606, 8, x_468);
lean_ctor_set_uint8(x_606, 9, x_479);
lean_ctor_set_uint8(x_606, 10, x_470);
lean_ctor_set_uint8(x_606, 11, x_471);
lean_ctor_set_uint8(x_606, 12, x_604);
lean_ctor_set_uint8(x_606, 13, x_604);
lean_ctor_set_uint8(x_606, 14, x_605);
lean_ctor_set_uint8(x_606, 15, x_604);
lean_ctor_set_uint8(x_606, 16, x_604);
lean_ctor_set_uint8(x_606, 17, x_477);
x_607 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_606);
x_608 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_608, 0, x_606);
lean_ctor_set(x_608, 1, x_452);
lean_ctor_set(x_608, 2, x_453);
lean_ctor_set(x_608, 3, x_454);
lean_ctor_set(x_608, 4, x_455);
lean_ctor_set(x_608, 5, x_456);
lean_ctor_set(x_608, 6, x_457);
lean_ctor_set_uint64(x_608, sizeof(void*)*7, x_607);
lean_ctor_set_uint8(x_608, sizeof(void*)*7 + 8, x_451);
lean_ctor_set_uint8(x_608, sizeof(void*)*7 + 9, x_458);
lean_ctor_set_uint8(x_608, sizeof(void*)*7 + 10, x_459);
x_609 = lean_apply_5(x_1, x_608, x_3, x_4, x_5, x_603);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
if (lean_is_exclusive(x_609)) {
 lean_ctor_release(x_609, 0);
 lean_ctor_release(x_609, 1);
 x_612 = x_609;
} else {
 lean_dec_ref(x_609);
 x_612 = lean_box(0);
}
if (lean_is_scalar(x_612)) {
 x_613 = lean_alloc_ctor(0, 2, 0);
} else {
 x_613 = x_612;
}
lean_ctor_set(x_613, 0, x_610);
lean_ctor_set(x_613, 1, x_611);
return x_613;
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_614 = lean_ctor_get(x_609, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_609, 1);
lean_inc(x_615);
if (lean_is_exclusive(x_609)) {
 lean_ctor_release(x_609, 0);
 lean_ctor_release(x_609, 1);
 x_616 = x_609;
} else {
 lean_dec_ref(x_609);
 x_616 = lean_box(0);
}
if (lean_is_scalar(x_616)) {
 x_617 = lean_alloc_ctor(1, 2, 0);
} else {
 x_617 = x_616;
}
lean_ctor_set(x_617, 0, x_614);
lean_ctor_set(x_617, 1, x_615);
return x_617;
}
}
else
{
uint8_t x_618; 
x_618 = lean_ctor_get_uint8(x_585, 15);
if (x_618 == 0)
{
lean_object* x_619; uint8_t x_620; uint8_t x_621; lean_object* x_622; uint64_t x_623; lean_object* x_624; lean_object* x_625; 
lean_dec(x_585);
lean_dec(x_583);
x_619 = lean_ctor_get(x_584, 1);
lean_inc(x_619);
lean_dec(x_584);
x_620 = 1;
x_621 = 2;
x_622 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_622, 0, x_460);
lean_ctor_set_uint8(x_622, 1, x_461);
lean_ctor_set_uint8(x_622, 2, x_462);
lean_ctor_set_uint8(x_622, 3, x_463);
lean_ctor_set_uint8(x_622, 4, x_464);
lean_ctor_set_uint8(x_622, 5, x_465);
lean_ctor_set_uint8(x_622, 6, x_466);
lean_ctor_set_uint8(x_622, 7, x_467);
lean_ctor_set_uint8(x_622, 8, x_468);
lean_ctor_set_uint8(x_622, 9, x_479);
lean_ctor_set_uint8(x_622, 10, x_470);
lean_ctor_set_uint8(x_622, 11, x_471);
lean_ctor_set_uint8(x_622, 12, x_620);
lean_ctor_set_uint8(x_622, 13, x_620);
lean_ctor_set_uint8(x_622, 14, x_621);
lean_ctor_set_uint8(x_622, 15, x_620);
lean_ctor_set_uint8(x_622, 16, x_620);
lean_ctor_set_uint8(x_622, 17, x_477);
x_623 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_622);
x_624 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_624, 0, x_622);
lean_ctor_set(x_624, 1, x_452);
lean_ctor_set(x_624, 2, x_453);
lean_ctor_set(x_624, 3, x_454);
lean_ctor_set(x_624, 4, x_455);
lean_ctor_set(x_624, 5, x_456);
lean_ctor_set(x_624, 6, x_457);
lean_ctor_set_uint64(x_624, sizeof(void*)*7, x_623);
lean_ctor_set_uint8(x_624, sizeof(void*)*7 + 8, x_451);
lean_ctor_set_uint8(x_624, sizeof(void*)*7 + 9, x_458);
lean_ctor_set_uint8(x_624, sizeof(void*)*7 + 10, x_459);
x_625 = lean_apply_5(x_1, x_624, x_3, x_4, x_5, x_619);
if (lean_obj_tag(x_625) == 0)
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_626 = lean_ctor_get(x_625, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_625, 1);
lean_inc(x_627);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 x_628 = x_625;
} else {
 lean_dec_ref(x_625);
 x_628 = lean_box(0);
}
if (lean_is_scalar(x_628)) {
 x_629 = lean_alloc_ctor(0, 2, 0);
} else {
 x_629 = x_628;
}
lean_ctor_set(x_629, 0, x_626);
lean_ctor_set(x_629, 1, x_627);
return x_629;
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_630 = lean_ctor_get(x_625, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_625, 1);
lean_inc(x_631);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 x_632 = x_625;
} else {
 lean_dec_ref(x_625);
 x_632 = lean_box(0);
}
if (lean_is_scalar(x_632)) {
 x_633 = lean_alloc_ctor(1, 2, 0);
} else {
 x_633 = x_632;
}
lean_ctor_set(x_633, 0, x_630);
lean_ctor_set(x_633, 1, x_631);
return x_633;
}
}
else
{
uint8_t x_634; 
x_634 = lean_ctor_get_uint8(x_585, 16);
if (x_634 == 0)
{
lean_object* x_635; uint8_t x_636; uint8_t x_637; lean_object* x_638; uint64_t x_639; lean_object* x_640; lean_object* x_641; 
lean_dec(x_585);
lean_dec(x_583);
x_635 = lean_ctor_get(x_584, 1);
lean_inc(x_635);
lean_dec(x_584);
x_636 = 1;
x_637 = 2;
x_638 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_638, 0, x_460);
lean_ctor_set_uint8(x_638, 1, x_461);
lean_ctor_set_uint8(x_638, 2, x_462);
lean_ctor_set_uint8(x_638, 3, x_463);
lean_ctor_set_uint8(x_638, 4, x_464);
lean_ctor_set_uint8(x_638, 5, x_465);
lean_ctor_set_uint8(x_638, 6, x_466);
lean_ctor_set_uint8(x_638, 7, x_467);
lean_ctor_set_uint8(x_638, 8, x_468);
lean_ctor_set_uint8(x_638, 9, x_479);
lean_ctor_set_uint8(x_638, 10, x_470);
lean_ctor_set_uint8(x_638, 11, x_471);
lean_ctor_set_uint8(x_638, 12, x_636);
lean_ctor_set_uint8(x_638, 13, x_636);
lean_ctor_set_uint8(x_638, 14, x_637);
lean_ctor_set_uint8(x_638, 15, x_636);
lean_ctor_set_uint8(x_638, 16, x_636);
lean_ctor_set_uint8(x_638, 17, x_477);
x_639 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_638);
x_640 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_640, 0, x_638);
lean_ctor_set(x_640, 1, x_452);
lean_ctor_set(x_640, 2, x_453);
lean_ctor_set(x_640, 3, x_454);
lean_ctor_set(x_640, 4, x_455);
lean_ctor_set(x_640, 5, x_456);
lean_ctor_set(x_640, 6, x_457);
lean_ctor_set_uint64(x_640, sizeof(void*)*7, x_639);
lean_ctor_set_uint8(x_640, sizeof(void*)*7 + 8, x_451);
lean_ctor_set_uint8(x_640, sizeof(void*)*7 + 9, x_458);
lean_ctor_set_uint8(x_640, sizeof(void*)*7 + 10, x_459);
x_641 = lean_apply_5(x_1, x_640, x_3, x_4, x_5, x_635);
if (lean_obj_tag(x_641) == 0)
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_642 = lean_ctor_get(x_641, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_641, 1);
lean_inc(x_643);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_644 = x_641;
} else {
 lean_dec_ref(x_641);
 x_644 = lean_box(0);
}
if (lean_is_scalar(x_644)) {
 x_645 = lean_alloc_ctor(0, 2, 0);
} else {
 x_645 = x_644;
}
lean_ctor_set(x_645, 0, x_642);
lean_ctor_set(x_645, 1, x_643);
return x_645;
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_646 = lean_ctor_get(x_641, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_641, 1);
lean_inc(x_647);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_648 = x_641;
} else {
 lean_dec_ref(x_641);
 x_648 = lean_box(0);
}
if (lean_is_scalar(x_648)) {
 x_649 = lean_alloc_ctor(1, 2, 0);
} else {
 x_649 = x_648;
}
lean_ctor_set(x_649, 0, x_646);
lean_ctor_set(x_649, 1, x_647);
return x_649;
}
}
else
{
lean_object* x_650; uint8_t x_651; uint8_t x_652; uint8_t x_653; 
x_650 = lean_ctor_get(x_584, 1);
lean_inc(x_650);
lean_dec(x_584);
x_651 = lean_ctor_get_uint8(x_585, 14);
lean_dec(x_585);
x_652 = 2;
x_653 = l_Lean_Meta_instDecidableEqProjReductionKind(x_651, x_652);
if (x_653 == 0)
{
uint8_t x_654; lean_object* x_655; uint64_t x_656; lean_object* x_657; lean_object* x_658; 
lean_dec(x_583);
x_654 = 1;
x_655 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_655, 0, x_460);
lean_ctor_set_uint8(x_655, 1, x_461);
lean_ctor_set_uint8(x_655, 2, x_462);
lean_ctor_set_uint8(x_655, 3, x_463);
lean_ctor_set_uint8(x_655, 4, x_464);
lean_ctor_set_uint8(x_655, 5, x_465);
lean_ctor_set_uint8(x_655, 6, x_466);
lean_ctor_set_uint8(x_655, 7, x_467);
lean_ctor_set_uint8(x_655, 8, x_468);
lean_ctor_set_uint8(x_655, 9, x_479);
lean_ctor_set_uint8(x_655, 10, x_470);
lean_ctor_set_uint8(x_655, 11, x_471);
lean_ctor_set_uint8(x_655, 12, x_654);
lean_ctor_set_uint8(x_655, 13, x_654);
lean_ctor_set_uint8(x_655, 14, x_652);
lean_ctor_set_uint8(x_655, 15, x_654);
lean_ctor_set_uint8(x_655, 16, x_654);
lean_ctor_set_uint8(x_655, 17, x_477);
x_656 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_655);
x_657 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_657, 0, x_655);
lean_ctor_set(x_657, 1, x_452);
lean_ctor_set(x_657, 2, x_453);
lean_ctor_set(x_657, 3, x_454);
lean_ctor_set(x_657, 4, x_455);
lean_ctor_set(x_657, 5, x_456);
lean_ctor_set(x_657, 6, x_457);
lean_ctor_set_uint64(x_657, sizeof(void*)*7, x_656);
lean_ctor_set_uint8(x_657, sizeof(void*)*7 + 8, x_451);
lean_ctor_set_uint8(x_657, sizeof(void*)*7 + 9, x_458);
lean_ctor_set_uint8(x_657, sizeof(void*)*7 + 10, x_459);
x_658 = lean_apply_5(x_1, x_657, x_3, x_4, x_5, x_650);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; 
x_659 = lean_ctor_get(x_658, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_658, 1);
lean_inc(x_660);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 lean_ctor_release(x_658, 1);
 x_661 = x_658;
} else {
 lean_dec_ref(x_658);
 x_661 = lean_box(0);
}
if (lean_is_scalar(x_661)) {
 x_662 = lean_alloc_ctor(0, 2, 0);
} else {
 x_662 = x_661;
}
lean_ctor_set(x_662, 0, x_659);
lean_ctor_set(x_662, 1, x_660);
return x_662;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; 
x_663 = lean_ctor_get(x_658, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_658, 1);
lean_inc(x_664);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 lean_ctor_release(x_658, 1);
 x_665 = x_658;
} else {
 lean_dec_ref(x_658);
 x_665 = lean_box(0);
}
if (lean_is_scalar(x_665)) {
 x_666 = lean_alloc_ctor(1, 2, 0);
} else {
 x_666 = x_665;
}
lean_ctor_set(x_666, 0, x_663);
lean_ctor_set(x_666, 1, x_664);
return x_666;
}
}
else
{
lean_object* x_667; 
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_452);
x_667 = lean_apply_5(x_1, x_583, x_3, x_4, x_5, x_650);
if (lean_obj_tag(x_667) == 0)
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_668 = lean_ctor_get(x_667, 0);
lean_inc(x_668);
x_669 = lean_ctor_get(x_667, 1);
lean_inc(x_669);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 lean_ctor_release(x_667, 1);
 x_670 = x_667;
} else {
 lean_dec_ref(x_667);
 x_670 = lean_box(0);
}
if (lean_is_scalar(x_670)) {
 x_671 = lean_alloc_ctor(0, 2, 0);
} else {
 x_671 = x_670;
}
lean_ctor_set(x_671, 0, x_668);
lean_ctor_set(x_671, 1, x_669);
return x_671;
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_672 = lean_ctor_get(x_667, 0);
lean_inc(x_672);
x_673 = lean_ctor_get(x_667, 1);
lean_inc(x_673);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 lean_ctor_release(x_667, 1);
 x_674 = x_667;
} else {
 lean_dec_ref(x_667);
 x_674 = lean_box(0);
}
if (lean_is_scalar(x_674)) {
 x_675 = lean_alloc_ctor(1, 2, 0);
} else {
 x_675 = x_674;
}
lean_ctor_set(x_675, 0, x_672);
lean_ctor_set(x_675, 1, x_673);
return x_675;
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
uint64_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; 
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
x_62 = lean_ctor_get_uint8(x_38, 17);
x_63 = 1;
x_64 = l_Lean_Meta_TransparencyMode_lt(x_59, x_63);
x_65 = 2;
x_66 = lean_uint64_shift_right(x_40, x_65);
x_67 = lean_uint64_shift_left(x_66, x_65);
if (x_64 == 0)
{
uint64_t x_68; uint64_t x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = l_Lean_Meta_TransparencyMode_toUInt64(x_59);
x_69 = lean_uint64_lor(x_67, x_68);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_69);
x_70 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get_uint8(x_71, 13);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; uint64_t x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_71);
lean_dec(x_2);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = 1;
x_75 = 2;
x_76 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_76, 0, x_50);
lean_ctor_set_uint8(x_76, 1, x_51);
lean_ctor_set_uint8(x_76, 2, x_52);
lean_ctor_set_uint8(x_76, 3, x_53);
lean_ctor_set_uint8(x_76, 4, x_54);
lean_ctor_set_uint8(x_76, 5, x_55);
lean_ctor_set_uint8(x_76, 6, x_56);
lean_ctor_set_uint8(x_76, 7, x_57);
lean_ctor_set_uint8(x_76, 8, x_58);
lean_ctor_set_uint8(x_76, 9, x_59);
lean_ctor_set_uint8(x_76, 10, x_60);
lean_ctor_set_uint8(x_76, 11, x_61);
lean_ctor_set_uint8(x_76, 12, x_74);
lean_ctor_set_uint8(x_76, 13, x_74);
lean_ctor_set_uint8(x_76, 14, x_75);
lean_ctor_set_uint8(x_76, 15, x_74);
lean_ctor_set_uint8(x_76, 16, x_74);
lean_ctor_set_uint8(x_76, 17, x_62);
x_77 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_76);
x_78 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_42);
lean_ctor_set(x_78, 2, x_43);
lean_ctor_set(x_78, 3, x_44);
lean_ctor_set(x_78, 4, x_45);
lean_ctor_set(x_78, 5, x_46);
lean_ctor_set(x_78, 6, x_47);
lean_ctor_set_uint64(x_78, sizeof(void*)*7, x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_78, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_78, sizeof(void*)*7 + 10, x_49);
x_79 = l_Lean_Meta_inferTypeImp_infer(x_1, x_78, x_3, x_4, x_5, x_73);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
return x_79;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_79);
if (x_84 == 0)
{
return x_79;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_79, 0);
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_79);
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
x_88 = lean_ctor_get_uint8(x_71, 12);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; uint8_t x_91; lean_object* x_92; uint64_t x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_71);
lean_dec(x_2);
x_89 = lean_ctor_get(x_70, 1);
lean_inc(x_89);
lean_dec(x_70);
x_90 = 1;
x_91 = 2;
x_92 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_92, 0, x_50);
lean_ctor_set_uint8(x_92, 1, x_51);
lean_ctor_set_uint8(x_92, 2, x_52);
lean_ctor_set_uint8(x_92, 3, x_53);
lean_ctor_set_uint8(x_92, 4, x_54);
lean_ctor_set_uint8(x_92, 5, x_55);
lean_ctor_set_uint8(x_92, 6, x_56);
lean_ctor_set_uint8(x_92, 7, x_57);
lean_ctor_set_uint8(x_92, 8, x_58);
lean_ctor_set_uint8(x_92, 9, x_59);
lean_ctor_set_uint8(x_92, 10, x_60);
lean_ctor_set_uint8(x_92, 11, x_61);
lean_ctor_set_uint8(x_92, 12, x_90);
lean_ctor_set_uint8(x_92, 13, x_90);
lean_ctor_set_uint8(x_92, 14, x_91);
lean_ctor_set_uint8(x_92, 15, x_90);
lean_ctor_set_uint8(x_92, 16, x_90);
lean_ctor_set_uint8(x_92, 17, x_62);
x_93 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_92);
x_94 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_42);
lean_ctor_set(x_94, 2, x_43);
lean_ctor_set(x_94, 3, x_44);
lean_ctor_set(x_94, 4, x_45);
lean_ctor_set(x_94, 5, x_46);
lean_ctor_set(x_94, 6, x_47);
lean_ctor_set_uint64(x_94, sizeof(void*)*7, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_94, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_94, sizeof(void*)*7 + 10, x_49);
x_95 = l_Lean_Meta_inferTypeImp_infer(x_1, x_94, x_3, x_4, x_5, x_89);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
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
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_95);
if (x_100 == 0)
{
return x_95;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_95, 0);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_95);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
x_104 = lean_ctor_get_uint8(x_71, 15);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; uint8_t x_107; lean_object* x_108; uint64_t x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_71);
lean_dec(x_2);
x_105 = lean_ctor_get(x_70, 1);
lean_inc(x_105);
lean_dec(x_70);
x_106 = 1;
x_107 = 2;
x_108 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_108, 0, x_50);
lean_ctor_set_uint8(x_108, 1, x_51);
lean_ctor_set_uint8(x_108, 2, x_52);
lean_ctor_set_uint8(x_108, 3, x_53);
lean_ctor_set_uint8(x_108, 4, x_54);
lean_ctor_set_uint8(x_108, 5, x_55);
lean_ctor_set_uint8(x_108, 6, x_56);
lean_ctor_set_uint8(x_108, 7, x_57);
lean_ctor_set_uint8(x_108, 8, x_58);
lean_ctor_set_uint8(x_108, 9, x_59);
lean_ctor_set_uint8(x_108, 10, x_60);
lean_ctor_set_uint8(x_108, 11, x_61);
lean_ctor_set_uint8(x_108, 12, x_106);
lean_ctor_set_uint8(x_108, 13, x_106);
lean_ctor_set_uint8(x_108, 14, x_107);
lean_ctor_set_uint8(x_108, 15, x_106);
lean_ctor_set_uint8(x_108, 16, x_106);
lean_ctor_set_uint8(x_108, 17, x_62);
x_109 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_108);
x_110 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_42);
lean_ctor_set(x_110, 2, x_43);
lean_ctor_set(x_110, 3, x_44);
lean_ctor_set(x_110, 4, x_45);
lean_ctor_set(x_110, 5, x_46);
lean_ctor_set(x_110, 6, x_47);
lean_ctor_set_uint64(x_110, sizeof(void*)*7, x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_110, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_110, sizeof(void*)*7 + 10, x_49);
x_111 = l_Lean_Meta_inferTypeImp_infer(x_1, x_110, x_3, x_4, x_5, x_105);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
return x_111;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_111, 0);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_111);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_111);
if (x_116 == 0)
{
return x_111;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_111, 0);
x_118 = lean_ctor_get(x_111, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_111);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
x_120 = lean_ctor_get_uint8(x_71, 16);
if (x_120 == 0)
{
lean_object* x_121; uint8_t x_122; uint8_t x_123; lean_object* x_124; uint64_t x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_71);
lean_dec(x_2);
x_121 = lean_ctor_get(x_70, 1);
lean_inc(x_121);
lean_dec(x_70);
x_122 = 1;
x_123 = 2;
x_124 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_124, 0, x_50);
lean_ctor_set_uint8(x_124, 1, x_51);
lean_ctor_set_uint8(x_124, 2, x_52);
lean_ctor_set_uint8(x_124, 3, x_53);
lean_ctor_set_uint8(x_124, 4, x_54);
lean_ctor_set_uint8(x_124, 5, x_55);
lean_ctor_set_uint8(x_124, 6, x_56);
lean_ctor_set_uint8(x_124, 7, x_57);
lean_ctor_set_uint8(x_124, 8, x_58);
lean_ctor_set_uint8(x_124, 9, x_59);
lean_ctor_set_uint8(x_124, 10, x_60);
lean_ctor_set_uint8(x_124, 11, x_61);
lean_ctor_set_uint8(x_124, 12, x_122);
lean_ctor_set_uint8(x_124, 13, x_122);
lean_ctor_set_uint8(x_124, 14, x_123);
lean_ctor_set_uint8(x_124, 15, x_122);
lean_ctor_set_uint8(x_124, 16, x_122);
lean_ctor_set_uint8(x_124, 17, x_62);
x_125 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_124);
x_126 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_42);
lean_ctor_set(x_126, 2, x_43);
lean_ctor_set(x_126, 3, x_44);
lean_ctor_set(x_126, 4, x_45);
lean_ctor_set(x_126, 5, x_46);
lean_ctor_set(x_126, 6, x_47);
lean_ctor_set_uint64(x_126, sizeof(void*)*7, x_125);
lean_ctor_set_uint8(x_126, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_126, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_126, sizeof(void*)*7 + 10, x_49);
x_127 = l_Lean_Meta_inferTypeImp_infer(x_1, x_126, x_3, x_4, x_5, x_121);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
return x_127;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_127);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
else
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_127);
if (x_132 == 0)
{
return x_127;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_127, 0);
x_134 = lean_ctor_get(x_127, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_127);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
lean_object* x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; 
x_136 = lean_ctor_get(x_70, 1);
lean_inc(x_136);
lean_dec(x_70);
x_137 = lean_ctor_get_uint8(x_71, 14);
lean_dec(x_71);
x_138 = 2;
x_139 = l_Lean_Meta_instDecidableEqProjReductionKind(x_137, x_138);
if (x_139 == 0)
{
uint8_t x_140; lean_object* x_141; uint64_t x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_2);
x_140 = 1;
x_141 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_141, 0, x_50);
lean_ctor_set_uint8(x_141, 1, x_51);
lean_ctor_set_uint8(x_141, 2, x_52);
lean_ctor_set_uint8(x_141, 3, x_53);
lean_ctor_set_uint8(x_141, 4, x_54);
lean_ctor_set_uint8(x_141, 5, x_55);
lean_ctor_set_uint8(x_141, 6, x_56);
lean_ctor_set_uint8(x_141, 7, x_57);
lean_ctor_set_uint8(x_141, 8, x_58);
lean_ctor_set_uint8(x_141, 9, x_59);
lean_ctor_set_uint8(x_141, 10, x_60);
lean_ctor_set_uint8(x_141, 11, x_61);
lean_ctor_set_uint8(x_141, 12, x_140);
lean_ctor_set_uint8(x_141, 13, x_140);
lean_ctor_set_uint8(x_141, 14, x_138);
lean_ctor_set_uint8(x_141, 15, x_140);
lean_ctor_set_uint8(x_141, 16, x_140);
lean_ctor_set_uint8(x_141, 17, x_62);
x_142 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_141);
x_143 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_42);
lean_ctor_set(x_143, 2, x_43);
lean_ctor_set(x_143, 3, x_44);
lean_ctor_set(x_143, 4, x_45);
lean_ctor_set(x_143, 5, x_46);
lean_ctor_set(x_143, 6, x_47);
lean_ctor_set_uint64(x_143, sizeof(void*)*7, x_142);
lean_ctor_set_uint8(x_143, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_143, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_143, sizeof(void*)*7 + 10, x_49);
x_144 = l_Lean_Meta_inferTypeImp_infer(x_1, x_143, x_3, x_4, x_5, x_136);
if (lean_obj_tag(x_144) == 0)
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
return x_144;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_144, 0);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_144);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
else
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_144);
if (x_149 == 0)
{
return x_144;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_144, 0);
x_151 = lean_ctor_get(x_144, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_144);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
lean_object* x_153; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_153 = l_Lean_Meta_inferTypeImp_infer(x_1, x_2, x_3, x_4, x_5, x_136);
if (lean_obj_tag(x_153) == 0)
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
return x_153;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_153, 0);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_153);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
else
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_153);
if (x_158 == 0)
{
return x_153;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_153, 0);
x_160 = lean_ctor_get(x_153, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_153);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
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
uint64_t x_162; uint64_t x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
lean_ctor_set_uint8(x_38, 9, x_63);
x_162 = l_Lean_Meta_withInferTypeConfig___rarg___closed__1;
x_163 = lean_uint64_lor(x_67, x_162);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_163);
x_164 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get_uint8(x_165, 13);
if (x_166 == 0)
{
lean_object* x_167; uint8_t x_168; uint8_t x_169; lean_object* x_170; uint64_t x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_165);
lean_dec(x_2);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
lean_dec(x_164);
x_168 = 1;
x_169 = 2;
x_170 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_170, 0, x_50);
lean_ctor_set_uint8(x_170, 1, x_51);
lean_ctor_set_uint8(x_170, 2, x_52);
lean_ctor_set_uint8(x_170, 3, x_53);
lean_ctor_set_uint8(x_170, 4, x_54);
lean_ctor_set_uint8(x_170, 5, x_55);
lean_ctor_set_uint8(x_170, 6, x_56);
lean_ctor_set_uint8(x_170, 7, x_57);
lean_ctor_set_uint8(x_170, 8, x_58);
lean_ctor_set_uint8(x_170, 9, x_63);
lean_ctor_set_uint8(x_170, 10, x_60);
lean_ctor_set_uint8(x_170, 11, x_61);
lean_ctor_set_uint8(x_170, 12, x_168);
lean_ctor_set_uint8(x_170, 13, x_168);
lean_ctor_set_uint8(x_170, 14, x_169);
lean_ctor_set_uint8(x_170, 15, x_168);
lean_ctor_set_uint8(x_170, 16, x_168);
lean_ctor_set_uint8(x_170, 17, x_62);
x_171 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_170);
x_172 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_42);
lean_ctor_set(x_172, 2, x_43);
lean_ctor_set(x_172, 3, x_44);
lean_ctor_set(x_172, 4, x_45);
lean_ctor_set(x_172, 5, x_46);
lean_ctor_set(x_172, 6, x_47);
lean_ctor_set_uint64(x_172, sizeof(void*)*7, x_171);
lean_ctor_set_uint8(x_172, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_172, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_172, sizeof(void*)*7 + 10, x_49);
x_173 = l_Lean_Meta_inferTypeImp_infer(x_1, x_172, x_3, x_4, x_5, x_167);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
return x_173;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_173, 0);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_173);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
else
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_173);
if (x_178 == 0)
{
return x_173;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_173, 0);
x_180 = lean_ctor_get(x_173, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_173);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
else
{
uint8_t x_182; 
x_182 = lean_ctor_get_uint8(x_165, 12);
if (x_182 == 0)
{
lean_object* x_183; uint8_t x_184; uint8_t x_185; lean_object* x_186; uint64_t x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_165);
lean_dec(x_2);
x_183 = lean_ctor_get(x_164, 1);
lean_inc(x_183);
lean_dec(x_164);
x_184 = 1;
x_185 = 2;
x_186 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_186, 0, x_50);
lean_ctor_set_uint8(x_186, 1, x_51);
lean_ctor_set_uint8(x_186, 2, x_52);
lean_ctor_set_uint8(x_186, 3, x_53);
lean_ctor_set_uint8(x_186, 4, x_54);
lean_ctor_set_uint8(x_186, 5, x_55);
lean_ctor_set_uint8(x_186, 6, x_56);
lean_ctor_set_uint8(x_186, 7, x_57);
lean_ctor_set_uint8(x_186, 8, x_58);
lean_ctor_set_uint8(x_186, 9, x_63);
lean_ctor_set_uint8(x_186, 10, x_60);
lean_ctor_set_uint8(x_186, 11, x_61);
lean_ctor_set_uint8(x_186, 12, x_184);
lean_ctor_set_uint8(x_186, 13, x_184);
lean_ctor_set_uint8(x_186, 14, x_185);
lean_ctor_set_uint8(x_186, 15, x_184);
lean_ctor_set_uint8(x_186, 16, x_184);
lean_ctor_set_uint8(x_186, 17, x_62);
x_187 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_186);
x_188 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_42);
lean_ctor_set(x_188, 2, x_43);
lean_ctor_set(x_188, 3, x_44);
lean_ctor_set(x_188, 4, x_45);
lean_ctor_set(x_188, 5, x_46);
lean_ctor_set(x_188, 6, x_47);
lean_ctor_set_uint64(x_188, sizeof(void*)*7, x_187);
lean_ctor_set_uint8(x_188, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_188, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_188, sizeof(void*)*7 + 10, x_49);
x_189 = l_Lean_Meta_inferTypeImp_infer(x_1, x_188, x_3, x_4, x_5, x_183);
if (lean_obj_tag(x_189) == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_189);
if (x_190 == 0)
{
return x_189;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_189, 0);
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_189);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
else
{
uint8_t x_194; 
x_194 = !lean_is_exclusive(x_189);
if (x_194 == 0)
{
return x_189;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_189, 0);
x_196 = lean_ctor_get(x_189, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_189);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
uint8_t x_198; 
x_198 = lean_ctor_get_uint8(x_165, 15);
if (x_198 == 0)
{
lean_object* x_199; uint8_t x_200; uint8_t x_201; lean_object* x_202; uint64_t x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_165);
lean_dec(x_2);
x_199 = lean_ctor_get(x_164, 1);
lean_inc(x_199);
lean_dec(x_164);
x_200 = 1;
x_201 = 2;
x_202 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_202, 0, x_50);
lean_ctor_set_uint8(x_202, 1, x_51);
lean_ctor_set_uint8(x_202, 2, x_52);
lean_ctor_set_uint8(x_202, 3, x_53);
lean_ctor_set_uint8(x_202, 4, x_54);
lean_ctor_set_uint8(x_202, 5, x_55);
lean_ctor_set_uint8(x_202, 6, x_56);
lean_ctor_set_uint8(x_202, 7, x_57);
lean_ctor_set_uint8(x_202, 8, x_58);
lean_ctor_set_uint8(x_202, 9, x_63);
lean_ctor_set_uint8(x_202, 10, x_60);
lean_ctor_set_uint8(x_202, 11, x_61);
lean_ctor_set_uint8(x_202, 12, x_200);
lean_ctor_set_uint8(x_202, 13, x_200);
lean_ctor_set_uint8(x_202, 14, x_201);
lean_ctor_set_uint8(x_202, 15, x_200);
lean_ctor_set_uint8(x_202, 16, x_200);
lean_ctor_set_uint8(x_202, 17, x_62);
x_203 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_202);
x_204 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_42);
lean_ctor_set(x_204, 2, x_43);
lean_ctor_set(x_204, 3, x_44);
lean_ctor_set(x_204, 4, x_45);
lean_ctor_set(x_204, 5, x_46);
lean_ctor_set(x_204, 6, x_47);
lean_ctor_set_uint64(x_204, sizeof(void*)*7, x_203);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_204, sizeof(void*)*7 + 10, x_49);
x_205 = l_Lean_Meta_inferTypeImp_infer(x_1, x_204, x_3, x_4, x_5, x_199);
if (lean_obj_tag(x_205) == 0)
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
return x_205;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_205, 0);
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_205);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
else
{
uint8_t x_210; 
x_210 = !lean_is_exclusive(x_205);
if (x_210 == 0)
{
return x_205;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_205, 0);
x_212 = lean_ctor_get(x_205, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_205);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
else
{
uint8_t x_214; 
x_214 = lean_ctor_get_uint8(x_165, 16);
if (x_214 == 0)
{
lean_object* x_215; uint8_t x_216; uint8_t x_217; lean_object* x_218; uint64_t x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_165);
lean_dec(x_2);
x_215 = lean_ctor_get(x_164, 1);
lean_inc(x_215);
lean_dec(x_164);
x_216 = 1;
x_217 = 2;
x_218 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_218, 0, x_50);
lean_ctor_set_uint8(x_218, 1, x_51);
lean_ctor_set_uint8(x_218, 2, x_52);
lean_ctor_set_uint8(x_218, 3, x_53);
lean_ctor_set_uint8(x_218, 4, x_54);
lean_ctor_set_uint8(x_218, 5, x_55);
lean_ctor_set_uint8(x_218, 6, x_56);
lean_ctor_set_uint8(x_218, 7, x_57);
lean_ctor_set_uint8(x_218, 8, x_58);
lean_ctor_set_uint8(x_218, 9, x_63);
lean_ctor_set_uint8(x_218, 10, x_60);
lean_ctor_set_uint8(x_218, 11, x_61);
lean_ctor_set_uint8(x_218, 12, x_216);
lean_ctor_set_uint8(x_218, 13, x_216);
lean_ctor_set_uint8(x_218, 14, x_217);
lean_ctor_set_uint8(x_218, 15, x_216);
lean_ctor_set_uint8(x_218, 16, x_216);
lean_ctor_set_uint8(x_218, 17, x_62);
x_219 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_218);
x_220 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_42);
lean_ctor_set(x_220, 2, x_43);
lean_ctor_set(x_220, 3, x_44);
lean_ctor_set(x_220, 4, x_45);
lean_ctor_set(x_220, 5, x_46);
lean_ctor_set(x_220, 6, x_47);
lean_ctor_set_uint64(x_220, sizeof(void*)*7, x_219);
lean_ctor_set_uint8(x_220, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_220, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_220, sizeof(void*)*7 + 10, x_49);
x_221 = l_Lean_Meta_inferTypeImp_infer(x_1, x_220, x_3, x_4, x_5, x_215);
if (lean_obj_tag(x_221) == 0)
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
return x_221;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_221, 0);
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_221);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
else
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_221);
if (x_226 == 0)
{
return x_221;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_221, 0);
x_228 = lean_ctor_get(x_221, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_221);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
else
{
lean_object* x_230; uint8_t x_231; uint8_t x_232; uint8_t x_233; 
x_230 = lean_ctor_get(x_164, 1);
lean_inc(x_230);
lean_dec(x_164);
x_231 = lean_ctor_get_uint8(x_165, 14);
lean_dec(x_165);
x_232 = 2;
x_233 = l_Lean_Meta_instDecidableEqProjReductionKind(x_231, x_232);
if (x_233 == 0)
{
uint8_t x_234; lean_object* x_235; uint64_t x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_2);
x_234 = 1;
x_235 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_235, 0, x_50);
lean_ctor_set_uint8(x_235, 1, x_51);
lean_ctor_set_uint8(x_235, 2, x_52);
lean_ctor_set_uint8(x_235, 3, x_53);
lean_ctor_set_uint8(x_235, 4, x_54);
lean_ctor_set_uint8(x_235, 5, x_55);
lean_ctor_set_uint8(x_235, 6, x_56);
lean_ctor_set_uint8(x_235, 7, x_57);
lean_ctor_set_uint8(x_235, 8, x_58);
lean_ctor_set_uint8(x_235, 9, x_63);
lean_ctor_set_uint8(x_235, 10, x_60);
lean_ctor_set_uint8(x_235, 11, x_61);
lean_ctor_set_uint8(x_235, 12, x_234);
lean_ctor_set_uint8(x_235, 13, x_234);
lean_ctor_set_uint8(x_235, 14, x_232);
lean_ctor_set_uint8(x_235, 15, x_234);
lean_ctor_set_uint8(x_235, 16, x_234);
lean_ctor_set_uint8(x_235, 17, x_62);
x_236 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_235);
x_237 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_42);
lean_ctor_set(x_237, 2, x_43);
lean_ctor_set(x_237, 3, x_44);
lean_ctor_set(x_237, 4, x_45);
lean_ctor_set(x_237, 5, x_46);
lean_ctor_set(x_237, 6, x_47);
lean_ctor_set_uint64(x_237, sizeof(void*)*7, x_236);
lean_ctor_set_uint8(x_237, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_237, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_237, sizeof(void*)*7 + 10, x_49);
x_238 = l_Lean_Meta_inferTypeImp_infer(x_1, x_237, x_3, x_4, x_5, x_230);
if (lean_obj_tag(x_238) == 0)
{
uint8_t x_239; 
x_239 = !lean_is_exclusive(x_238);
if (x_239 == 0)
{
return x_238;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_238, 0);
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_238);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
else
{
uint8_t x_243; 
x_243 = !lean_is_exclusive(x_238);
if (x_243 == 0)
{
return x_238;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_238, 0);
x_245 = lean_ctor_get(x_238, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_238);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
else
{
lean_object* x_247; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_247 = l_Lean_Meta_inferTypeImp_infer(x_1, x_2, x_3, x_4, x_5, x_230);
if (lean_obj_tag(x_247) == 0)
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_247);
if (x_248 == 0)
{
return x_247;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_247, 0);
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_247);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
else
{
uint8_t x_252; 
x_252 = !lean_is_exclusive(x_247);
if (x_252 == 0)
{
return x_247;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_247, 0);
x_254 = lean_ctor_get(x_247, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_247);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
return x_255;
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
uint64_t x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; uint8_t x_265; uint8_t x_266; uint8_t x_267; uint8_t x_268; uint8_t x_269; uint8_t x_270; uint8_t x_271; uint8_t x_272; uint8_t x_273; uint8_t x_274; uint8_t x_275; uint8_t x_276; uint8_t x_277; uint8_t x_278; uint8_t x_279; uint8_t x_280; uint8_t x_281; uint8_t x_282; uint8_t x_283; uint8_t x_284; uint8_t x_285; uint64_t x_286; uint64_t x_287; uint64_t x_288; 
x_256 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_257 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_258 = lean_ctor_get(x_2, 1);
x_259 = lean_ctor_get(x_2, 2);
x_260 = lean_ctor_get(x_2, 3);
x_261 = lean_ctor_get(x_2, 4);
x_262 = lean_ctor_get(x_2, 5);
x_263 = lean_ctor_get(x_2, 6);
x_264 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_265 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
x_266 = lean_ctor_get_uint8(x_38, 0);
x_267 = lean_ctor_get_uint8(x_38, 1);
x_268 = lean_ctor_get_uint8(x_38, 2);
x_269 = lean_ctor_get_uint8(x_38, 3);
x_270 = lean_ctor_get_uint8(x_38, 4);
x_271 = lean_ctor_get_uint8(x_38, 5);
x_272 = lean_ctor_get_uint8(x_38, 6);
x_273 = lean_ctor_get_uint8(x_38, 7);
x_274 = lean_ctor_get_uint8(x_38, 8);
x_275 = lean_ctor_get_uint8(x_38, 9);
x_276 = lean_ctor_get_uint8(x_38, 10);
x_277 = lean_ctor_get_uint8(x_38, 11);
x_278 = lean_ctor_get_uint8(x_38, 12);
x_279 = lean_ctor_get_uint8(x_38, 13);
x_280 = lean_ctor_get_uint8(x_38, 14);
x_281 = lean_ctor_get_uint8(x_38, 15);
x_282 = lean_ctor_get_uint8(x_38, 16);
x_283 = lean_ctor_get_uint8(x_38, 17);
lean_dec(x_38);
x_284 = 1;
x_285 = l_Lean_Meta_TransparencyMode_lt(x_275, x_284);
x_286 = 2;
x_287 = lean_uint64_shift_right(x_256, x_286);
x_288 = lean_uint64_shift_left(x_287, x_286);
if (x_285 == 0)
{
lean_object* x_289; uint64_t x_290; uint64_t x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; 
x_289 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_289, 0, x_266);
lean_ctor_set_uint8(x_289, 1, x_267);
lean_ctor_set_uint8(x_289, 2, x_268);
lean_ctor_set_uint8(x_289, 3, x_269);
lean_ctor_set_uint8(x_289, 4, x_270);
lean_ctor_set_uint8(x_289, 5, x_271);
lean_ctor_set_uint8(x_289, 6, x_272);
lean_ctor_set_uint8(x_289, 7, x_273);
lean_ctor_set_uint8(x_289, 8, x_274);
lean_ctor_set_uint8(x_289, 9, x_275);
lean_ctor_set_uint8(x_289, 10, x_276);
lean_ctor_set_uint8(x_289, 11, x_277);
lean_ctor_set_uint8(x_289, 12, x_278);
lean_ctor_set_uint8(x_289, 13, x_279);
lean_ctor_set_uint8(x_289, 14, x_280);
lean_ctor_set_uint8(x_289, 15, x_281);
lean_ctor_set_uint8(x_289, 16, x_282);
lean_ctor_set_uint8(x_289, 17, x_283);
x_290 = l_Lean_Meta_TransparencyMode_toUInt64(x_275);
x_291 = lean_uint64_lor(x_288, x_290);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_258);
lean_ctor_set(x_2, 0, x_289);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_291);
x_292 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get_uint8(x_293, 13);
if (x_294 == 0)
{
lean_object* x_295; uint8_t x_296; uint8_t x_297; lean_object* x_298; uint64_t x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_293);
lean_dec(x_2);
x_295 = lean_ctor_get(x_292, 1);
lean_inc(x_295);
lean_dec(x_292);
x_296 = 1;
x_297 = 2;
x_298 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_298, 0, x_266);
lean_ctor_set_uint8(x_298, 1, x_267);
lean_ctor_set_uint8(x_298, 2, x_268);
lean_ctor_set_uint8(x_298, 3, x_269);
lean_ctor_set_uint8(x_298, 4, x_270);
lean_ctor_set_uint8(x_298, 5, x_271);
lean_ctor_set_uint8(x_298, 6, x_272);
lean_ctor_set_uint8(x_298, 7, x_273);
lean_ctor_set_uint8(x_298, 8, x_274);
lean_ctor_set_uint8(x_298, 9, x_275);
lean_ctor_set_uint8(x_298, 10, x_276);
lean_ctor_set_uint8(x_298, 11, x_277);
lean_ctor_set_uint8(x_298, 12, x_296);
lean_ctor_set_uint8(x_298, 13, x_296);
lean_ctor_set_uint8(x_298, 14, x_297);
lean_ctor_set_uint8(x_298, 15, x_296);
lean_ctor_set_uint8(x_298, 16, x_296);
lean_ctor_set_uint8(x_298, 17, x_283);
x_299 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_298);
x_300 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_258);
lean_ctor_set(x_300, 2, x_259);
lean_ctor_set(x_300, 3, x_260);
lean_ctor_set(x_300, 4, x_261);
lean_ctor_set(x_300, 5, x_262);
lean_ctor_set(x_300, 6, x_263);
lean_ctor_set_uint64(x_300, sizeof(void*)*7, x_299);
lean_ctor_set_uint8(x_300, sizeof(void*)*7 + 8, x_257);
lean_ctor_set_uint8(x_300, sizeof(void*)*7 + 9, x_264);
lean_ctor_set_uint8(x_300, sizeof(void*)*7 + 10, x_265);
x_301 = l_Lean_Meta_inferTypeImp_infer(x_1, x_300, x_3, x_4, x_5, x_295);
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
x_310 = lean_ctor_get_uint8(x_293, 12);
if (x_310 == 0)
{
lean_object* x_311; uint8_t x_312; uint8_t x_313; lean_object* x_314; uint64_t x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_293);
lean_dec(x_2);
x_311 = lean_ctor_get(x_292, 1);
lean_inc(x_311);
lean_dec(x_292);
x_312 = 1;
x_313 = 2;
x_314 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_314, 0, x_266);
lean_ctor_set_uint8(x_314, 1, x_267);
lean_ctor_set_uint8(x_314, 2, x_268);
lean_ctor_set_uint8(x_314, 3, x_269);
lean_ctor_set_uint8(x_314, 4, x_270);
lean_ctor_set_uint8(x_314, 5, x_271);
lean_ctor_set_uint8(x_314, 6, x_272);
lean_ctor_set_uint8(x_314, 7, x_273);
lean_ctor_set_uint8(x_314, 8, x_274);
lean_ctor_set_uint8(x_314, 9, x_275);
lean_ctor_set_uint8(x_314, 10, x_276);
lean_ctor_set_uint8(x_314, 11, x_277);
lean_ctor_set_uint8(x_314, 12, x_312);
lean_ctor_set_uint8(x_314, 13, x_312);
lean_ctor_set_uint8(x_314, 14, x_313);
lean_ctor_set_uint8(x_314, 15, x_312);
lean_ctor_set_uint8(x_314, 16, x_312);
lean_ctor_set_uint8(x_314, 17, x_283);
x_315 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_314);
x_316 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_258);
lean_ctor_set(x_316, 2, x_259);
lean_ctor_set(x_316, 3, x_260);
lean_ctor_set(x_316, 4, x_261);
lean_ctor_set(x_316, 5, x_262);
lean_ctor_set(x_316, 6, x_263);
lean_ctor_set_uint64(x_316, sizeof(void*)*7, x_315);
lean_ctor_set_uint8(x_316, sizeof(void*)*7 + 8, x_257);
lean_ctor_set_uint8(x_316, sizeof(void*)*7 + 9, x_264);
lean_ctor_set_uint8(x_316, sizeof(void*)*7 + 10, x_265);
x_317 = l_Lean_Meta_inferTypeImp_infer(x_1, x_316, x_3, x_4, x_5, x_311);
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
uint8_t x_326; 
x_326 = lean_ctor_get_uint8(x_293, 15);
if (x_326 == 0)
{
lean_object* x_327; uint8_t x_328; uint8_t x_329; lean_object* x_330; uint64_t x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_293);
lean_dec(x_2);
x_327 = lean_ctor_get(x_292, 1);
lean_inc(x_327);
lean_dec(x_292);
x_328 = 1;
x_329 = 2;
x_330 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_330, 0, x_266);
lean_ctor_set_uint8(x_330, 1, x_267);
lean_ctor_set_uint8(x_330, 2, x_268);
lean_ctor_set_uint8(x_330, 3, x_269);
lean_ctor_set_uint8(x_330, 4, x_270);
lean_ctor_set_uint8(x_330, 5, x_271);
lean_ctor_set_uint8(x_330, 6, x_272);
lean_ctor_set_uint8(x_330, 7, x_273);
lean_ctor_set_uint8(x_330, 8, x_274);
lean_ctor_set_uint8(x_330, 9, x_275);
lean_ctor_set_uint8(x_330, 10, x_276);
lean_ctor_set_uint8(x_330, 11, x_277);
lean_ctor_set_uint8(x_330, 12, x_328);
lean_ctor_set_uint8(x_330, 13, x_328);
lean_ctor_set_uint8(x_330, 14, x_329);
lean_ctor_set_uint8(x_330, 15, x_328);
lean_ctor_set_uint8(x_330, 16, x_328);
lean_ctor_set_uint8(x_330, 17, x_283);
x_331 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_330);
x_332 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_258);
lean_ctor_set(x_332, 2, x_259);
lean_ctor_set(x_332, 3, x_260);
lean_ctor_set(x_332, 4, x_261);
lean_ctor_set(x_332, 5, x_262);
lean_ctor_set(x_332, 6, x_263);
lean_ctor_set_uint64(x_332, sizeof(void*)*7, x_331);
lean_ctor_set_uint8(x_332, sizeof(void*)*7 + 8, x_257);
lean_ctor_set_uint8(x_332, sizeof(void*)*7 + 9, x_264);
lean_ctor_set_uint8(x_332, sizeof(void*)*7 + 10, x_265);
x_333 = l_Lean_Meta_inferTypeImp_infer(x_1, x_332, x_3, x_4, x_5, x_327);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_336 = x_333;
} else {
 lean_dec_ref(x_333);
 x_336 = lean_box(0);
}
if (lean_is_scalar(x_336)) {
 x_337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_337 = x_336;
}
lean_ctor_set(x_337, 0, x_334);
lean_ctor_set(x_337, 1, x_335);
return x_337;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_338 = lean_ctor_get(x_333, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_333, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_340 = x_333;
} else {
 lean_dec_ref(x_333);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 2, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_339);
return x_341;
}
}
else
{
uint8_t x_342; 
x_342 = lean_ctor_get_uint8(x_293, 16);
if (x_342 == 0)
{
lean_object* x_343; uint8_t x_344; uint8_t x_345; lean_object* x_346; uint64_t x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_293);
lean_dec(x_2);
x_343 = lean_ctor_get(x_292, 1);
lean_inc(x_343);
lean_dec(x_292);
x_344 = 1;
x_345 = 2;
x_346 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_346, 0, x_266);
lean_ctor_set_uint8(x_346, 1, x_267);
lean_ctor_set_uint8(x_346, 2, x_268);
lean_ctor_set_uint8(x_346, 3, x_269);
lean_ctor_set_uint8(x_346, 4, x_270);
lean_ctor_set_uint8(x_346, 5, x_271);
lean_ctor_set_uint8(x_346, 6, x_272);
lean_ctor_set_uint8(x_346, 7, x_273);
lean_ctor_set_uint8(x_346, 8, x_274);
lean_ctor_set_uint8(x_346, 9, x_275);
lean_ctor_set_uint8(x_346, 10, x_276);
lean_ctor_set_uint8(x_346, 11, x_277);
lean_ctor_set_uint8(x_346, 12, x_344);
lean_ctor_set_uint8(x_346, 13, x_344);
lean_ctor_set_uint8(x_346, 14, x_345);
lean_ctor_set_uint8(x_346, 15, x_344);
lean_ctor_set_uint8(x_346, 16, x_344);
lean_ctor_set_uint8(x_346, 17, x_283);
x_347 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_346);
x_348 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_258);
lean_ctor_set(x_348, 2, x_259);
lean_ctor_set(x_348, 3, x_260);
lean_ctor_set(x_348, 4, x_261);
lean_ctor_set(x_348, 5, x_262);
lean_ctor_set(x_348, 6, x_263);
lean_ctor_set_uint64(x_348, sizeof(void*)*7, x_347);
lean_ctor_set_uint8(x_348, sizeof(void*)*7 + 8, x_257);
lean_ctor_set_uint8(x_348, sizeof(void*)*7 + 9, x_264);
lean_ctor_set_uint8(x_348, sizeof(void*)*7 + 10, x_265);
x_349 = l_Lean_Meta_inferTypeImp_infer(x_1, x_348, x_3, x_4, x_5, x_343);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 x_352 = x_349;
} else {
 lean_dec_ref(x_349);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_350);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_354 = lean_ctor_get(x_349, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_349, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 x_356 = x_349;
} else {
 lean_dec_ref(x_349);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_354);
lean_ctor_set(x_357, 1, x_355);
return x_357;
}
}
else
{
lean_object* x_358; uint8_t x_359; uint8_t x_360; uint8_t x_361; 
x_358 = lean_ctor_get(x_292, 1);
lean_inc(x_358);
lean_dec(x_292);
x_359 = lean_ctor_get_uint8(x_293, 14);
lean_dec(x_293);
x_360 = 2;
x_361 = l_Lean_Meta_instDecidableEqProjReductionKind(x_359, x_360);
if (x_361 == 0)
{
uint8_t x_362; lean_object* x_363; uint64_t x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_2);
x_362 = 1;
x_363 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_363, 0, x_266);
lean_ctor_set_uint8(x_363, 1, x_267);
lean_ctor_set_uint8(x_363, 2, x_268);
lean_ctor_set_uint8(x_363, 3, x_269);
lean_ctor_set_uint8(x_363, 4, x_270);
lean_ctor_set_uint8(x_363, 5, x_271);
lean_ctor_set_uint8(x_363, 6, x_272);
lean_ctor_set_uint8(x_363, 7, x_273);
lean_ctor_set_uint8(x_363, 8, x_274);
lean_ctor_set_uint8(x_363, 9, x_275);
lean_ctor_set_uint8(x_363, 10, x_276);
lean_ctor_set_uint8(x_363, 11, x_277);
lean_ctor_set_uint8(x_363, 12, x_362);
lean_ctor_set_uint8(x_363, 13, x_362);
lean_ctor_set_uint8(x_363, 14, x_360);
lean_ctor_set_uint8(x_363, 15, x_362);
lean_ctor_set_uint8(x_363, 16, x_362);
lean_ctor_set_uint8(x_363, 17, x_283);
x_364 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_363);
x_365 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_258);
lean_ctor_set(x_365, 2, x_259);
lean_ctor_set(x_365, 3, x_260);
lean_ctor_set(x_365, 4, x_261);
lean_ctor_set(x_365, 5, x_262);
lean_ctor_set(x_365, 6, x_263);
lean_ctor_set_uint64(x_365, sizeof(void*)*7, x_364);
lean_ctor_set_uint8(x_365, sizeof(void*)*7 + 8, x_257);
lean_ctor_set_uint8(x_365, sizeof(void*)*7 + 9, x_264);
lean_ctor_set_uint8(x_365, sizeof(void*)*7 + 10, x_265);
x_366 = l_Lean_Meta_inferTypeImp_infer(x_1, x_365, x_3, x_4, x_5, x_358);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_369 = x_366;
} else {
 lean_dec_ref(x_366);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_368);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_371 = lean_ctor_get(x_366, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_366, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_373 = x_366;
} else {
 lean_dec_ref(x_366);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(1, 2, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_372);
return x_374;
}
}
else
{
lean_object* x_375; 
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
x_375 = l_Lean_Meta_inferTypeImp_infer(x_1, x_2, x_3, x_4, x_5, x_358);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_378 = x_375;
} else {
 lean_dec_ref(x_375);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_376);
lean_ctor_set(x_379, 1, x_377);
return x_379;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_380 = lean_ctor_get(x_375, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_375, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_382 = x_375;
} else {
 lean_dec_ref(x_375);
 x_382 = lean_box(0);
}
if (lean_is_scalar(x_382)) {
 x_383 = lean_alloc_ctor(1, 2, 0);
} else {
 x_383 = x_382;
}
lean_ctor_set(x_383, 0, x_380);
lean_ctor_set(x_383, 1, x_381);
return x_383;
}
}
}
}
}
}
}
else
{
lean_object* x_384; uint64_t x_385; uint64_t x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; 
x_384 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_384, 0, x_266);
lean_ctor_set_uint8(x_384, 1, x_267);
lean_ctor_set_uint8(x_384, 2, x_268);
lean_ctor_set_uint8(x_384, 3, x_269);
lean_ctor_set_uint8(x_384, 4, x_270);
lean_ctor_set_uint8(x_384, 5, x_271);
lean_ctor_set_uint8(x_384, 6, x_272);
lean_ctor_set_uint8(x_384, 7, x_273);
lean_ctor_set_uint8(x_384, 8, x_274);
lean_ctor_set_uint8(x_384, 9, x_284);
lean_ctor_set_uint8(x_384, 10, x_276);
lean_ctor_set_uint8(x_384, 11, x_277);
lean_ctor_set_uint8(x_384, 12, x_278);
lean_ctor_set_uint8(x_384, 13, x_279);
lean_ctor_set_uint8(x_384, 14, x_280);
lean_ctor_set_uint8(x_384, 15, x_281);
lean_ctor_set_uint8(x_384, 16, x_282);
lean_ctor_set_uint8(x_384, 17, x_283);
x_385 = l_Lean_Meta_withInferTypeConfig___rarg___closed__1;
x_386 = lean_uint64_lor(x_288, x_385);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_258);
lean_ctor_set(x_2, 0, x_384);
lean_ctor_set_uint64(x_2, sizeof(void*)*7, x_386);
x_387 = l_Lean_Meta_getConfig(x_2, x_3, x_4, x_5, x_6);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get_uint8(x_388, 13);
if (x_389 == 0)
{
lean_object* x_390; uint8_t x_391; uint8_t x_392; lean_object* x_393; uint64_t x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_388);
lean_dec(x_2);
x_390 = lean_ctor_get(x_387, 1);
lean_inc(x_390);
lean_dec(x_387);
x_391 = 1;
x_392 = 2;
x_393 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_393, 0, x_266);
lean_ctor_set_uint8(x_393, 1, x_267);
lean_ctor_set_uint8(x_393, 2, x_268);
lean_ctor_set_uint8(x_393, 3, x_269);
lean_ctor_set_uint8(x_393, 4, x_270);
lean_ctor_set_uint8(x_393, 5, x_271);
lean_ctor_set_uint8(x_393, 6, x_272);
lean_ctor_set_uint8(x_393, 7, x_273);
lean_ctor_set_uint8(x_393, 8, x_274);
lean_ctor_set_uint8(x_393, 9, x_284);
lean_ctor_set_uint8(x_393, 10, x_276);
lean_ctor_set_uint8(x_393, 11, x_277);
lean_ctor_set_uint8(x_393, 12, x_391);
lean_ctor_set_uint8(x_393, 13, x_391);
lean_ctor_set_uint8(x_393, 14, x_392);
lean_ctor_set_uint8(x_393, 15, x_391);
lean_ctor_set_uint8(x_393, 16, x_391);
lean_ctor_set_uint8(x_393, 17, x_283);
x_394 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_393);
x_395 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_258);
lean_ctor_set(x_395, 2, x_259);
lean_ctor_set(x_395, 3, x_260);
lean_ctor_set(x_395, 4, x_261);
lean_ctor_set(x_395, 5, x_262);
lean_ctor_set(x_395, 6, x_263);
lean_ctor_set_uint64(x_395, sizeof(void*)*7, x_394);
lean_ctor_set_uint8(x_395, sizeof(void*)*7 + 8, x_257);
lean_ctor_set_uint8(x_395, sizeof(void*)*7 + 9, x_264);
lean_ctor_set_uint8(x_395, sizeof(void*)*7 + 10, x_265);
x_396 = l_Lean_Meta_inferTypeImp_infer(x_1, x_395, x_3, x_4, x_5, x_390);
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
x_405 = lean_ctor_get_uint8(x_388, 12);
if (x_405 == 0)
{
lean_object* x_406; uint8_t x_407; uint8_t x_408; lean_object* x_409; uint64_t x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_388);
lean_dec(x_2);
x_406 = lean_ctor_get(x_387, 1);
lean_inc(x_406);
lean_dec(x_387);
x_407 = 1;
x_408 = 2;
x_409 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_409, 0, x_266);
lean_ctor_set_uint8(x_409, 1, x_267);
lean_ctor_set_uint8(x_409, 2, x_268);
lean_ctor_set_uint8(x_409, 3, x_269);
lean_ctor_set_uint8(x_409, 4, x_270);
lean_ctor_set_uint8(x_409, 5, x_271);
lean_ctor_set_uint8(x_409, 6, x_272);
lean_ctor_set_uint8(x_409, 7, x_273);
lean_ctor_set_uint8(x_409, 8, x_274);
lean_ctor_set_uint8(x_409, 9, x_284);
lean_ctor_set_uint8(x_409, 10, x_276);
lean_ctor_set_uint8(x_409, 11, x_277);
lean_ctor_set_uint8(x_409, 12, x_407);
lean_ctor_set_uint8(x_409, 13, x_407);
lean_ctor_set_uint8(x_409, 14, x_408);
lean_ctor_set_uint8(x_409, 15, x_407);
lean_ctor_set_uint8(x_409, 16, x_407);
lean_ctor_set_uint8(x_409, 17, x_283);
x_410 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_409);
x_411 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_258);
lean_ctor_set(x_411, 2, x_259);
lean_ctor_set(x_411, 3, x_260);
lean_ctor_set(x_411, 4, x_261);
lean_ctor_set(x_411, 5, x_262);
lean_ctor_set(x_411, 6, x_263);
lean_ctor_set_uint64(x_411, sizeof(void*)*7, x_410);
lean_ctor_set_uint8(x_411, sizeof(void*)*7 + 8, x_257);
lean_ctor_set_uint8(x_411, sizeof(void*)*7 + 9, x_264);
lean_ctor_set_uint8(x_411, sizeof(void*)*7 + 10, x_265);
x_412 = l_Lean_Meta_inferTypeImp_infer(x_1, x_411, x_3, x_4, x_5, x_406);
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
uint8_t x_421; 
x_421 = lean_ctor_get_uint8(x_388, 15);
if (x_421 == 0)
{
lean_object* x_422; uint8_t x_423; uint8_t x_424; lean_object* x_425; uint64_t x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_388);
lean_dec(x_2);
x_422 = lean_ctor_get(x_387, 1);
lean_inc(x_422);
lean_dec(x_387);
x_423 = 1;
x_424 = 2;
x_425 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_425, 0, x_266);
lean_ctor_set_uint8(x_425, 1, x_267);
lean_ctor_set_uint8(x_425, 2, x_268);
lean_ctor_set_uint8(x_425, 3, x_269);
lean_ctor_set_uint8(x_425, 4, x_270);
lean_ctor_set_uint8(x_425, 5, x_271);
lean_ctor_set_uint8(x_425, 6, x_272);
lean_ctor_set_uint8(x_425, 7, x_273);
lean_ctor_set_uint8(x_425, 8, x_274);
lean_ctor_set_uint8(x_425, 9, x_284);
lean_ctor_set_uint8(x_425, 10, x_276);
lean_ctor_set_uint8(x_425, 11, x_277);
lean_ctor_set_uint8(x_425, 12, x_423);
lean_ctor_set_uint8(x_425, 13, x_423);
lean_ctor_set_uint8(x_425, 14, x_424);
lean_ctor_set_uint8(x_425, 15, x_423);
lean_ctor_set_uint8(x_425, 16, x_423);
lean_ctor_set_uint8(x_425, 17, x_283);
x_426 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_425);
x_427 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set(x_427, 1, x_258);
lean_ctor_set(x_427, 2, x_259);
lean_ctor_set(x_427, 3, x_260);
lean_ctor_set(x_427, 4, x_261);
lean_ctor_set(x_427, 5, x_262);
lean_ctor_set(x_427, 6, x_263);
lean_ctor_set_uint64(x_427, sizeof(void*)*7, x_426);
lean_ctor_set_uint8(x_427, sizeof(void*)*7 + 8, x_257);
lean_ctor_set_uint8(x_427, sizeof(void*)*7 + 9, x_264);
lean_ctor_set_uint8(x_427, sizeof(void*)*7 + 10, x_265);
x_428 = l_Lean_Meta_inferTypeImp_infer(x_1, x_427, x_3, x_4, x_5, x_422);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_431 = x_428;
} else {
 lean_dec_ref(x_428);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(0, 2, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_429);
lean_ctor_set(x_432, 1, x_430);
return x_432;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_433 = lean_ctor_get(x_428, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_428, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_435 = x_428;
} else {
 lean_dec_ref(x_428);
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
uint8_t x_437; 
x_437 = lean_ctor_get_uint8(x_388, 16);
if (x_437 == 0)
{
lean_object* x_438; uint8_t x_439; uint8_t x_440; lean_object* x_441; uint64_t x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_388);
lean_dec(x_2);
x_438 = lean_ctor_get(x_387, 1);
lean_inc(x_438);
lean_dec(x_387);
x_439 = 1;
x_440 = 2;
x_441 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_441, 0, x_266);
lean_ctor_set_uint8(x_441, 1, x_267);
lean_ctor_set_uint8(x_441, 2, x_268);
lean_ctor_set_uint8(x_441, 3, x_269);
lean_ctor_set_uint8(x_441, 4, x_270);
lean_ctor_set_uint8(x_441, 5, x_271);
lean_ctor_set_uint8(x_441, 6, x_272);
lean_ctor_set_uint8(x_441, 7, x_273);
lean_ctor_set_uint8(x_441, 8, x_274);
lean_ctor_set_uint8(x_441, 9, x_284);
lean_ctor_set_uint8(x_441, 10, x_276);
lean_ctor_set_uint8(x_441, 11, x_277);
lean_ctor_set_uint8(x_441, 12, x_439);
lean_ctor_set_uint8(x_441, 13, x_439);
lean_ctor_set_uint8(x_441, 14, x_440);
lean_ctor_set_uint8(x_441, 15, x_439);
lean_ctor_set_uint8(x_441, 16, x_439);
lean_ctor_set_uint8(x_441, 17, x_283);
x_442 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_441);
x_443 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_258);
lean_ctor_set(x_443, 2, x_259);
lean_ctor_set(x_443, 3, x_260);
lean_ctor_set(x_443, 4, x_261);
lean_ctor_set(x_443, 5, x_262);
lean_ctor_set(x_443, 6, x_263);
lean_ctor_set_uint64(x_443, sizeof(void*)*7, x_442);
lean_ctor_set_uint8(x_443, sizeof(void*)*7 + 8, x_257);
lean_ctor_set_uint8(x_443, sizeof(void*)*7 + 9, x_264);
lean_ctor_set_uint8(x_443, sizeof(void*)*7 + 10, x_265);
x_444 = l_Lean_Meta_inferTypeImp_infer(x_1, x_443, x_3, x_4, x_5, x_438);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_444, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_447 = x_444;
} else {
 lean_dec_ref(x_444);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_446);
return x_448;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_449 = lean_ctor_get(x_444, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_444, 1);
lean_inc(x_450);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_451 = x_444;
} else {
 lean_dec_ref(x_444);
 x_451 = lean_box(0);
}
if (lean_is_scalar(x_451)) {
 x_452 = lean_alloc_ctor(1, 2, 0);
} else {
 x_452 = x_451;
}
lean_ctor_set(x_452, 0, x_449);
lean_ctor_set(x_452, 1, x_450);
return x_452;
}
}
else
{
lean_object* x_453; uint8_t x_454; uint8_t x_455; uint8_t x_456; 
x_453 = lean_ctor_get(x_387, 1);
lean_inc(x_453);
lean_dec(x_387);
x_454 = lean_ctor_get_uint8(x_388, 14);
lean_dec(x_388);
x_455 = 2;
x_456 = l_Lean_Meta_instDecidableEqProjReductionKind(x_454, x_455);
if (x_456 == 0)
{
uint8_t x_457; lean_object* x_458; uint64_t x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_2);
x_457 = 1;
x_458 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_458, 0, x_266);
lean_ctor_set_uint8(x_458, 1, x_267);
lean_ctor_set_uint8(x_458, 2, x_268);
lean_ctor_set_uint8(x_458, 3, x_269);
lean_ctor_set_uint8(x_458, 4, x_270);
lean_ctor_set_uint8(x_458, 5, x_271);
lean_ctor_set_uint8(x_458, 6, x_272);
lean_ctor_set_uint8(x_458, 7, x_273);
lean_ctor_set_uint8(x_458, 8, x_274);
lean_ctor_set_uint8(x_458, 9, x_284);
lean_ctor_set_uint8(x_458, 10, x_276);
lean_ctor_set_uint8(x_458, 11, x_277);
lean_ctor_set_uint8(x_458, 12, x_457);
lean_ctor_set_uint8(x_458, 13, x_457);
lean_ctor_set_uint8(x_458, 14, x_455);
lean_ctor_set_uint8(x_458, 15, x_457);
lean_ctor_set_uint8(x_458, 16, x_457);
lean_ctor_set_uint8(x_458, 17, x_283);
x_459 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_458);
x_460 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_460, 0, x_458);
lean_ctor_set(x_460, 1, x_258);
lean_ctor_set(x_460, 2, x_259);
lean_ctor_set(x_460, 3, x_260);
lean_ctor_set(x_460, 4, x_261);
lean_ctor_set(x_460, 5, x_262);
lean_ctor_set(x_460, 6, x_263);
lean_ctor_set_uint64(x_460, sizeof(void*)*7, x_459);
lean_ctor_set_uint8(x_460, sizeof(void*)*7 + 8, x_257);
lean_ctor_set_uint8(x_460, sizeof(void*)*7 + 9, x_264);
lean_ctor_set_uint8(x_460, sizeof(void*)*7 + 10, x_265);
x_461 = l_Lean_Meta_inferTypeImp_infer(x_1, x_460, x_3, x_4, x_5, x_453);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_461, 1);
lean_inc(x_463);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_464 = x_461;
} else {
 lean_dec_ref(x_461);
 x_464 = lean_box(0);
}
if (lean_is_scalar(x_464)) {
 x_465 = lean_alloc_ctor(0, 2, 0);
} else {
 x_465 = x_464;
}
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_463);
return x_465;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_466 = lean_ctor_get(x_461, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_461, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_468 = x_461;
} else {
 lean_dec_ref(x_461);
 x_468 = lean_box(0);
}
if (lean_is_scalar(x_468)) {
 x_469 = lean_alloc_ctor(1, 2, 0);
} else {
 x_469 = x_468;
}
lean_ctor_set(x_469, 0, x_466);
lean_ctor_set(x_469, 1, x_467);
return x_469;
}
}
else
{
lean_object* x_470; 
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
x_470 = l_Lean_Meta_inferTypeImp_infer(x_1, x_2, x_3, x_4, x_5, x_453);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_473 = x_470;
} else {
 lean_dec_ref(x_470);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(0, 2, 0);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_471);
lean_ctor_set(x_474, 1, x_472);
return x_474;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_475 = lean_ctor_get(x_470, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_470, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_477 = x_470;
} else {
 lean_dec_ref(x_470);
 x_477 = lean_box(0);
}
if (lean_is_scalar(x_477)) {
 x_478 = lean_alloc_ctor(1, 2, 0);
} else {
 x_478 = x_477;
}
lean_ctor_set(x_478, 0, x_475);
lean_ctor_set(x_478, 1, x_476);
return x_478;
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
lean_object* x_479; uint64_t x_480; uint8_t x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; uint8_t x_489; uint8_t x_490; uint8_t x_491; uint8_t x_492; uint8_t x_493; uint8_t x_494; uint8_t x_495; uint8_t x_496; uint8_t x_497; uint8_t x_498; uint8_t x_499; uint8_t x_500; uint8_t x_501; uint8_t x_502; uint8_t x_503; uint8_t x_504; uint8_t x_505; uint8_t x_506; uint8_t x_507; lean_object* x_508; uint8_t x_509; uint8_t x_510; uint64_t x_511; uint64_t x_512; uint64_t x_513; 
x_479 = lean_ctor_get(x_2, 0);
x_480 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_481 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_482 = lean_ctor_get(x_2, 1);
x_483 = lean_ctor_get(x_2, 2);
x_484 = lean_ctor_get(x_2, 3);
x_485 = lean_ctor_get(x_2, 4);
x_486 = lean_ctor_get(x_2, 5);
x_487 = lean_ctor_get(x_2, 6);
x_488 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_489 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
lean_inc(x_487);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_inc(x_482);
lean_inc(x_479);
lean_dec(x_2);
x_490 = lean_ctor_get_uint8(x_479, 0);
x_491 = lean_ctor_get_uint8(x_479, 1);
x_492 = lean_ctor_get_uint8(x_479, 2);
x_493 = lean_ctor_get_uint8(x_479, 3);
x_494 = lean_ctor_get_uint8(x_479, 4);
x_495 = lean_ctor_get_uint8(x_479, 5);
x_496 = lean_ctor_get_uint8(x_479, 6);
x_497 = lean_ctor_get_uint8(x_479, 7);
x_498 = lean_ctor_get_uint8(x_479, 8);
x_499 = lean_ctor_get_uint8(x_479, 9);
x_500 = lean_ctor_get_uint8(x_479, 10);
x_501 = lean_ctor_get_uint8(x_479, 11);
x_502 = lean_ctor_get_uint8(x_479, 12);
x_503 = lean_ctor_get_uint8(x_479, 13);
x_504 = lean_ctor_get_uint8(x_479, 14);
x_505 = lean_ctor_get_uint8(x_479, 15);
x_506 = lean_ctor_get_uint8(x_479, 16);
x_507 = lean_ctor_get_uint8(x_479, 17);
if (lean_is_exclusive(x_479)) {
 x_508 = x_479;
} else {
 lean_dec_ref(x_479);
 x_508 = lean_box(0);
}
x_509 = 1;
x_510 = l_Lean_Meta_TransparencyMode_lt(x_499, x_509);
x_511 = 2;
x_512 = lean_uint64_shift_right(x_480, x_511);
x_513 = lean_uint64_shift_left(x_512, x_511);
if (x_510 == 0)
{
lean_object* x_514; uint64_t x_515; uint64_t x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; 
if (lean_is_scalar(x_508)) {
 x_514 = lean_alloc_ctor(0, 0, 18);
} else {
 x_514 = x_508;
}
lean_ctor_set_uint8(x_514, 0, x_490);
lean_ctor_set_uint8(x_514, 1, x_491);
lean_ctor_set_uint8(x_514, 2, x_492);
lean_ctor_set_uint8(x_514, 3, x_493);
lean_ctor_set_uint8(x_514, 4, x_494);
lean_ctor_set_uint8(x_514, 5, x_495);
lean_ctor_set_uint8(x_514, 6, x_496);
lean_ctor_set_uint8(x_514, 7, x_497);
lean_ctor_set_uint8(x_514, 8, x_498);
lean_ctor_set_uint8(x_514, 9, x_499);
lean_ctor_set_uint8(x_514, 10, x_500);
lean_ctor_set_uint8(x_514, 11, x_501);
lean_ctor_set_uint8(x_514, 12, x_502);
lean_ctor_set_uint8(x_514, 13, x_503);
lean_ctor_set_uint8(x_514, 14, x_504);
lean_ctor_set_uint8(x_514, 15, x_505);
lean_ctor_set_uint8(x_514, 16, x_506);
lean_ctor_set_uint8(x_514, 17, x_507);
x_515 = l_Lean_Meta_TransparencyMode_toUInt64(x_499);
x_516 = lean_uint64_lor(x_513, x_515);
lean_inc(x_487);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_inc(x_482);
x_517 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_517, 0, x_514);
lean_ctor_set(x_517, 1, x_482);
lean_ctor_set(x_517, 2, x_483);
lean_ctor_set(x_517, 3, x_484);
lean_ctor_set(x_517, 4, x_485);
lean_ctor_set(x_517, 5, x_486);
lean_ctor_set(x_517, 6, x_487);
lean_ctor_set_uint64(x_517, sizeof(void*)*7, x_516);
lean_ctor_set_uint8(x_517, sizeof(void*)*7 + 8, x_481);
lean_ctor_set_uint8(x_517, sizeof(void*)*7 + 9, x_488);
lean_ctor_set_uint8(x_517, sizeof(void*)*7 + 10, x_489);
x_518 = l_Lean_Meta_getConfig(x_517, x_3, x_4, x_5, x_6);
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_ctor_get_uint8(x_519, 13);
if (x_520 == 0)
{
lean_object* x_521; uint8_t x_522; uint8_t x_523; lean_object* x_524; uint64_t x_525; lean_object* x_526; lean_object* x_527; 
lean_dec(x_519);
lean_dec(x_517);
x_521 = lean_ctor_get(x_518, 1);
lean_inc(x_521);
lean_dec(x_518);
x_522 = 1;
x_523 = 2;
x_524 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_524, 0, x_490);
lean_ctor_set_uint8(x_524, 1, x_491);
lean_ctor_set_uint8(x_524, 2, x_492);
lean_ctor_set_uint8(x_524, 3, x_493);
lean_ctor_set_uint8(x_524, 4, x_494);
lean_ctor_set_uint8(x_524, 5, x_495);
lean_ctor_set_uint8(x_524, 6, x_496);
lean_ctor_set_uint8(x_524, 7, x_497);
lean_ctor_set_uint8(x_524, 8, x_498);
lean_ctor_set_uint8(x_524, 9, x_499);
lean_ctor_set_uint8(x_524, 10, x_500);
lean_ctor_set_uint8(x_524, 11, x_501);
lean_ctor_set_uint8(x_524, 12, x_522);
lean_ctor_set_uint8(x_524, 13, x_522);
lean_ctor_set_uint8(x_524, 14, x_523);
lean_ctor_set_uint8(x_524, 15, x_522);
lean_ctor_set_uint8(x_524, 16, x_522);
lean_ctor_set_uint8(x_524, 17, x_507);
x_525 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_524);
x_526 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_526, 0, x_524);
lean_ctor_set(x_526, 1, x_482);
lean_ctor_set(x_526, 2, x_483);
lean_ctor_set(x_526, 3, x_484);
lean_ctor_set(x_526, 4, x_485);
lean_ctor_set(x_526, 5, x_486);
lean_ctor_set(x_526, 6, x_487);
lean_ctor_set_uint64(x_526, sizeof(void*)*7, x_525);
lean_ctor_set_uint8(x_526, sizeof(void*)*7 + 8, x_481);
lean_ctor_set_uint8(x_526, sizeof(void*)*7 + 9, x_488);
lean_ctor_set_uint8(x_526, sizeof(void*)*7 + 10, x_489);
x_527 = l_Lean_Meta_inferTypeImp_infer(x_1, x_526, x_3, x_4, x_5, x_521);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_527, 1);
lean_inc(x_529);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 lean_ctor_release(x_527, 1);
 x_530 = x_527;
} else {
 lean_dec_ref(x_527);
 x_530 = lean_box(0);
}
if (lean_is_scalar(x_530)) {
 x_531 = lean_alloc_ctor(0, 2, 0);
} else {
 x_531 = x_530;
}
lean_ctor_set(x_531, 0, x_528);
lean_ctor_set(x_531, 1, x_529);
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_532 = lean_ctor_get(x_527, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_527, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 lean_ctor_release(x_527, 1);
 x_534 = x_527;
} else {
 lean_dec_ref(x_527);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(1, 2, 0);
} else {
 x_535 = x_534;
}
lean_ctor_set(x_535, 0, x_532);
lean_ctor_set(x_535, 1, x_533);
return x_535;
}
}
else
{
uint8_t x_536; 
x_536 = lean_ctor_get_uint8(x_519, 12);
if (x_536 == 0)
{
lean_object* x_537; uint8_t x_538; uint8_t x_539; lean_object* x_540; uint64_t x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_519);
lean_dec(x_517);
x_537 = lean_ctor_get(x_518, 1);
lean_inc(x_537);
lean_dec(x_518);
x_538 = 1;
x_539 = 2;
x_540 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_540, 0, x_490);
lean_ctor_set_uint8(x_540, 1, x_491);
lean_ctor_set_uint8(x_540, 2, x_492);
lean_ctor_set_uint8(x_540, 3, x_493);
lean_ctor_set_uint8(x_540, 4, x_494);
lean_ctor_set_uint8(x_540, 5, x_495);
lean_ctor_set_uint8(x_540, 6, x_496);
lean_ctor_set_uint8(x_540, 7, x_497);
lean_ctor_set_uint8(x_540, 8, x_498);
lean_ctor_set_uint8(x_540, 9, x_499);
lean_ctor_set_uint8(x_540, 10, x_500);
lean_ctor_set_uint8(x_540, 11, x_501);
lean_ctor_set_uint8(x_540, 12, x_538);
lean_ctor_set_uint8(x_540, 13, x_538);
lean_ctor_set_uint8(x_540, 14, x_539);
lean_ctor_set_uint8(x_540, 15, x_538);
lean_ctor_set_uint8(x_540, 16, x_538);
lean_ctor_set_uint8(x_540, 17, x_507);
x_541 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_540);
x_542 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_542, 0, x_540);
lean_ctor_set(x_542, 1, x_482);
lean_ctor_set(x_542, 2, x_483);
lean_ctor_set(x_542, 3, x_484);
lean_ctor_set(x_542, 4, x_485);
lean_ctor_set(x_542, 5, x_486);
lean_ctor_set(x_542, 6, x_487);
lean_ctor_set_uint64(x_542, sizeof(void*)*7, x_541);
lean_ctor_set_uint8(x_542, sizeof(void*)*7 + 8, x_481);
lean_ctor_set_uint8(x_542, sizeof(void*)*7 + 9, x_488);
lean_ctor_set_uint8(x_542, sizeof(void*)*7 + 10, x_489);
x_543 = l_Lean_Meta_inferTypeImp_infer(x_1, x_542, x_3, x_4, x_5, x_537);
if (lean_obj_tag(x_543) == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_543, 1);
lean_inc(x_545);
if (lean_is_exclusive(x_543)) {
 lean_ctor_release(x_543, 0);
 lean_ctor_release(x_543, 1);
 x_546 = x_543;
} else {
 lean_dec_ref(x_543);
 x_546 = lean_box(0);
}
if (lean_is_scalar(x_546)) {
 x_547 = lean_alloc_ctor(0, 2, 0);
} else {
 x_547 = x_546;
}
lean_ctor_set(x_547, 0, x_544);
lean_ctor_set(x_547, 1, x_545);
return x_547;
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_548 = lean_ctor_get(x_543, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_543, 1);
lean_inc(x_549);
if (lean_is_exclusive(x_543)) {
 lean_ctor_release(x_543, 0);
 lean_ctor_release(x_543, 1);
 x_550 = x_543;
} else {
 lean_dec_ref(x_543);
 x_550 = lean_box(0);
}
if (lean_is_scalar(x_550)) {
 x_551 = lean_alloc_ctor(1, 2, 0);
} else {
 x_551 = x_550;
}
lean_ctor_set(x_551, 0, x_548);
lean_ctor_set(x_551, 1, x_549);
return x_551;
}
}
else
{
uint8_t x_552; 
x_552 = lean_ctor_get_uint8(x_519, 15);
if (x_552 == 0)
{
lean_object* x_553; uint8_t x_554; uint8_t x_555; lean_object* x_556; uint64_t x_557; lean_object* x_558; lean_object* x_559; 
lean_dec(x_519);
lean_dec(x_517);
x_553 = lean_ctor_get(x_518, 1);
lean_inc(x_553);
lean_dec(x_518);
x_554 = 1;
x_555 = 2;
x_556 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_556, 0, x_490);
lean_ctor_set_uint8(x_556, 1, x_491);
lean_ctor_set_uint8(x_556, 2, x_492);
lean_ctor_set_uint8(x_556, 3, x_493);
lean_ctor_set_uint8(x_556, 4, x_494);
lean_ctor_set_uint8(x_556, 5, x_495);
lean_ctor_set_uint8(x_556, 6, x_496);
lean_ctor_set_uint8(x_556, 7, x_497);
lean_ctor_set_uint8(x_556, 8, x_498);
lean_ctor_set_uint8(x_556, 9, x_499);
lean_ctor_set_uint8(x_556, 10, x_500);
lean_ctor_set_uint8(x_556, 11, x_501);
lean_ctor_set_uint8(x_556, 12, x_554);
lean_ctor_set_uint8(x_556, 13, x_554);
lean_ctor_set_uint8(x_556, 14, x_555);
lean_ctor_set_uint8(x_556, 15, x_554);
lean_ctor_set_uint8(x_556, 16, x_554);
lean_ctor_set_uint8(x_556, 17, x_507);
x_557 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_556);
x_558 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_558, 0, x_556);
lean_ctor_set(x_558, 1, x_482);
lean_ctor_set(x_558, 2, x_483);
lean_ctor_set(x_558, 3, x_484);
lean_ctor_set(x_558, 4, x_485);
lean_ctor_set(x_558, 5, x_486);
lean_ctor_set(x_558, 6, x_487);
lean_ctor_set_uint64(x_558, sizeof(void*)*7, x_557);
lean_ctor_set_uint8(x_558, sizeof(void*)*7 + 8, x_481);
lean_ctor_set_uint8(x_558, sizeof(void*)*7 + 9, x_488);
lean_ctor_set_uint8(x_558, sizeof(void*)*7 + 10, x_489);
x_559 = l_Lean_Meta_inferTypeImp_infer(x_1, x_558, x_3, x_4, x_5, x_553);
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
uint8_t x_568; 
x_568 = lean_ctor_get_uint8(x_519, 16);
if (x_568 == 0)
{
lean_object* x_569; uint8_t x_570; uint8_t x_571; lean_object* x_572; uint64_t x_573; lean_object* x_574; lean_object* x_575; 
lean_dec(x_519);
lean_dec(x_517);
x_569 = lean_ctor_get(x_518, 1);
lean_inc(x_569);
lean_dec(x_518);
x_570 = 1;
x_571 = 2;
x_572 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_572, 0, x_490);
lean_ctor_set_uint8(x_572, 1, x_491);
lean_ctor_set_uint8(x_572, 2, x_492);
lean_ctor_set_uint8(x_572, 3, x_493);
lean_ctor_set_uint8(x_572, 4, x_494);
lean_ctor_set_uint8(x_572, 5, x_495);
lean_ctor_set_uint8(x_572, 6, x_496);
lean_ctor_set_uint8(x_572, 7, x_497);
lean_ctor_set_uint8(x_572, 8, x_498);
lean_ctor_set_uint8(x_572, 9, x_499);
lean_ctor_set_uint8(x_572, 10, x_500);
lean_ctor_set_uint8(x_572, 11, x_501);
lean_ctor_set_uint8(x_572, 12, x_570);
lean_ctor_set_uint8(x_572, 13, x_570);
lean_ctor_set_uint8(x_572, 14, x_571);
lean_ctor_set_uint8(x_572, 15, x_570);
lean_ctor_set_uint8(x_572, 16, x_570);
lean_ctor_set_uint8(x_572, 17, x_507);
x_573 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_572);
x_574 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_574, 0, x_572);
lean_ctor_set(x_574, 1, x_482);
lean_ctor_set(x_574, 2, x_483);
lean_ctor_set(x_574, 3, x_484);
lean_ctor_set(x_574, 4, x_485);
lean_ctor_set(x_574, 5, x_486);
lean_ctor_set(x_574, 6, x_487);
lean_ctor_set_uint64(x_574, sizeof(void*)*7, x_573);
lean_ctor_set_uint8(x_574, sizeof(void*)*7 + 8, x_481);
lean_ctor_set_uint8(x_574, sizeof(void*)*7 + 9, x_488);
lean_ctor_set_uint8(x_574, sizeof(void*)*7 + 10, x_489);
x_575 = l_Lean_Meta_inferTypeImp_infer(x_1, x_574, x_3, x_4, x_5, x_569);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_576 = lean_ctor_get(x_575, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_575, 1);
lean_inc(x_577);
if (lean_is_exclusive(x_575)) {
 lean_ctor_release(x_575, 0);
 lean_ctor_release(x_575, 1);
 x_578 = x_575;
} else {
 lean_dec_ref(x_575);
 x_578 = lean_box(0);
}
if (lean_is_scalar(x_578)) {
 x_579 = lean_alloc_ctor(0, 2, 0);
} else {
 x_579 = x_578;
}
lean_ctor_set(x_579, 0, x_576);
lean_ctor_set(x_579, 1, x_577);
return x_579;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_580 = lean_ctor_get(x_575, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_575, 1);
lean_inc(x_581);
if (lean_is_exclusive(x_575)) {
 lean_ctor_release(x_575, 0);
 lean_ctor_release(x_575, 1);
 x_582 = x_575;
} else {
 lean_dec_ref(x_575);
 x_582 = lean_box(0);
}
if (lean_is_scalar(x_582)) {
 x_583 = lean_alloc_ctor(1, 2, 0);
} else {
 x_583 = x_582;
}
lean_ctor_set(x_583, 0, x_580);
lean_ctor_set(x_583, 1, x_581);
return x_583;
}
}
else
{
lean_object* x_584; uint8_t x_585; uint8_t x_586; uint8_t x_587; 
x_584 = lean_ctor_get(x_518, 1);
lean_inc(x_584);
lean_dec(x_518);
x_585 = lean_ctor_get_uint8(x_519, 14);
lean_dec(x_519);
x_586 = 2;
x_587 = l_Lean_Meta_instDecidableEqProjReductionKind(x_585, x_586);
if (x_587 == 0)
{
uint8_t x_588; lean_object* x_589; uint64_t x_590; lean_object* x_591; lean_object* x_592; 
lean_dec(x_517);
x_588 = 1;
x_589 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_589, 0, x_490);
lean_ctor_set_uint8(x_589, 1, x_491);
lean_ctor_set_uint8(x_589, 2, x_492);
lean_ctor_set_uint8(x_589, 3, x_493);
lean_ctor_set_uint8(x_589, 4, x_494);
lean_ctor_set_uint8(x_589, 5, x_495);
lean_ctor_set_uint8(x_589, 6, x_496);
lean_ctor_set_uint8(x_589, 7, x_497);
lean_ctor_set_uint8(x_589, 8, x_498);
lean_ctor_set_uint8(x_589, 9, x_499);
lean_ctor_set_uint8(x_589, 10, x_500);
lean_ctor_set_uint8(x_589, 11, x_501);
lean_ctor_set_uint8(x_589, 12, x_588);
lean_ctor_set_uint8(x_589, 13, x_588);
lean_ctor_set_uint8(x_589, 14, x_586);
lean_ctor_set_uint8(x_589, 15, x_588);
lean_ctor_set_uint8(x_589, 16, x_588);
lean_ctor_set_uint8(x_589, 17, x_507);
x_590 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_589);
x_591 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_591, 0, x_589);
lean_ctor_set(x_591, 1, x_482);
lean_ctor_set(x_591, 2, x_483);
lean_ctor_set(x_591, 3, x_484);
lean_ctor_set(x_591, 4, x_485);
lean_ctor_set(x_591, 5, x_486);
lean_ctor_set(x_591, 6, x_487);
lean_ctor_set_uint64(x_591, sizeof(void*)*7, x_590);
lean_ctor_set_uint8(x_591, sizeof(void*)*7 + 8, x_481);
lean_ctor_set_uint8(x_591, sizeof(void*)*7 + 9, x_488);
lean_ctor_set_uint8(x_591, sizeof(void*)*7 + 10, x_489);
x_592 = l_Lean_Meta_inferTypeImp_infer(x_1, x_591, x_3, x_4, x_5, x_584);
if (lean_obj_tag(x_592) == 0)
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_592, 1);
lean_inc(x_594);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 lean_ctor_release(x_592, 1);
 x_595 = x_592;
} else {
 lean_dec_ref(x_592);
 x_595 = lean_box(0);
}
if (lean_is_scalar(x_595)) {
 x_596 = lean_alloc_ctor(0, 2, 0);
} else {
 x_596 = x_595;
}
lean_ctor_set(x_596, 0, x_593);
lean_ctor_set(x_596, 1, x_594);
return x_596;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_597 = lean_ctor_get(x_592, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_592, 1);
lean_inc(x_598);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 lean_ctor_release(x_592, 1);
 x_599 = x_592;
} else {
 lean_dec_ref(x_592);
 x_599 = lean_box(0);
}
if (lean_is_scalar(x_599)) {
 x_600 = lean_alloc_ctor(1, 2, 0);
} else {
 x_600 = x_599;
}
lean_ctor_set(x_600, 0, x_597);
lean_ctor_set(x_600, 1, x_598);
return x_600;
}
}
else
{
lean_object* x_601; 
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_484);
lean_dec(x_483);
lean_dec(x_482);
x_601 = l_Lean_Meta_inferTypeImp_infer(x_1, x_517, x_3, x_4, x_5, x_584);
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_604 = x_601;
} else {
 lean_dec_ref(x_601);
 x_604 = lean_box(0);
}
if (lean_is_scalar(x_604)) {
 x_605 = lean_alloc_ctor(0, 2, 0);
} else {
 x_605 = x_604;
}
lean_ctor_set(x_605, 0, x_602);
lean_ctor_set(x_605, 1, x_603);
return x_605;
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_606 = lean_ctor_get(x_601, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_601, 1);
lean_inc(x_607);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_608 = x_601;
} else {
 lean_dec_ref(x_601);
 x_608 = lean_box(0);
}
if (lean_is_scalar(x_608)) {
 x_609 = lean_alloc_ctor(1, 2, 0);
} else {
 x_609 = x_608;
}
lean_ctor_set(x_609, 0, x_606);
lean_ctor_set(x_609, 1, x_607);
return x_609;
}
}
}
}
}
}
}
else
{
lean_object* x_610; uint64_t x_611; uint64_t x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; uint8_t x_616; 
if (lean_is_scalar(x_508)) {
 x_610 = lean_alloc_ctor(0, 0, 18);
} else {
 x_610 = x_508;
}
lean_ctor_set_uint8(x_610, 0, x_490);
lean_ctor_set_uint8(x_610, 1, x_491);
lean_ctor_set_uint8(x_610, 2, x_492);
lean_ctor_set_uint8(x_610, 3, x_493);
lean_ctor_set_uint8(x_610, 4, x_494);
lean_ctor_set_uint8(x_610, 5, x_495);
lean_ctor_set_uint8(x_610, 6, x_496);
lean_ctor_set_uint8(x_610, 7, x_497);
lean_ctor_set_uint8(x_610, 8, x_498);
lean_ctor_set_uint8(x_610, 9, x_509);
lean_ctor_set_uint8(x_610, 10, x_500);
lean_ctor_set_uint8(x_610, 11, x_501);
lean_ctor_set_uint8(x_610, 12, x_502);
lean_ctor_set_uint8(x_610, 13, x_503);
lean_ctor_set_uint8(x_610, 14, x_504);
lean_ctor_set_uint8(x_610, 15, x_505);
lean_ctor_set_uint8(x_610, 16, x_506);
lean_ctor_set_uint8(x_610, 17, x_507);
x_611 = l_Lean_Meta_withInferTypeConfig___rarg___closed__1;
x_612 = lean_uint64_lor(x_513, x_611);
lean_inc(x_487);
lean_inc(x_486);
lean_inc(x_485);
lean_inc(x_484);
lean_inc(x_483);
lean_inc(x_482);
x_613 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_613, 0, x_610);
lean_ctor_set(x_613, 1, x_482);
lean_ctor_set(x_613, 2, x_483);
lean_ctor_set(x_613, 3, x_484);
lean_ctor_set(x_613, 4, x_485);
lean_ctor_set(x_613, 5, x_486);
lean_ctor_set(x_613, 6, x_487);
lean_ctor_set_uint64(x_613, sizeof(void*)*7, x_612);
lean_ctor_set_uint8(x_613, sizeof(void*)*7 + 8, x_481);
lean_ctor_set_uint8(x_613, sizeof(void*)*7 + 9, x_488);
lean_ctor_set_uint8(x_613, sizeof(void*)*7 + 10, x_489);
x_614 = l_Lean_Meta_getConfig(x_613, x_3, x_4, x_5, x_6);
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
x_616 = lean_ctor_get_uint8(x_615, 13);
if (x_616 == 0)
{
lean_object* x_617; uint8_t x_618; uint8_t x_619; lean_object* x_620; uint64_t x_621; lean_object* x_622; lean_object* x_623; 
lean_dec(x_615);
lean_dec(x_613);
x_617 = lean_ctor_get(x_614, 1);
lean_inc(x_617);
lean_dec(x_614);
x_618 = 1;
x_619 = 2;
x_620 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_620, 0, x_490);
lean_ctor_set_uint8(x_620, 1, x_491);
lean_ctor_set_uint8(x_620, 2, x_492);
lean_ctor_set_uint8(x_620, 3, x_493);
lean_ctor_set_uint8(x_620, 4, x_494);
lean_ctor_set_uint8(x_620, 5, x_495);
lean_ctor_set_uint8(x_620, 6, x_496);
lean_ctor_set_uint8(x_620, 7, x_497);
lean_ctor_set_uint8(x_620, 8, x_498);
lean_ctor_set_uint8(x_620, 9, x_509);
lean_ctor_set_uint8(x_620, 10, x_500);
lean_ctor_set_uint8(x_620, 11, x_501);
lean_ctor_set_uint8(x_620, 12, x_618);
lean_ctor_set_uint8(x_620, 13, x_618);
lean_ctor_set_uint8(x_620, 14, x_619);
lean_ctor_set_uint8(x_620, 15, x_618);
lean_ctor_set_uint8(x_620, 16, x_618);
lean_ctor_set_uint8(x_620, 17, x_507);
x_621 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_620);
x_622 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_622, 0, x_620);
lean_ctor_set(x_622, 1, x_482);
lean_ctor_set(x_622, 2, x_483);
lean_ctor_set(x_622, 3, x_484);
lean_ctor_set(x_622, 4, x_485);
lean_ctor_set(x_622, 5, x_486);
lean_ctor_set(x_622, 6, x_487);
lean_ctor_set_uint64(x_622, sizeof(void*)*7, x_621);
lean_ctor_set_uint8(x_622, sizeof(void*)*7 + 8, x_481);
lean_ctor_set_uint8(x_622, sizeof(void*)*7 + 9, x_488);
lean_ctor_set_uint8(x_622, sizeof(void*)*7 + 10, x_489);
x_623 = l_Lean_Meta_inferTypeImp_infer(x_1, x_622, x_3, x_4, x_5, x_617);
if (lean_obj_tag(x_623) == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_623, 1);
lean_inc(x_625);
if (lean_is_exclusive(x_623)) {
 lean_ctor_release(x_623, 0);
 lean_ctor_release(x_623, 1);
 x_626 = x_623;
} else {
 lean_dec_ref(x_623);
 x_626 = lean_box(0);
}
if (lean_is_scalar(x_626)) {
 x_627 = lean_alloc_ctor(0, 2, 0);
} else {
 x_627 = x_626;
}
lean_ctor_set(x_627, 0, x_624);
lean_ctor_set(x_627, 1, x_625);
return x_627;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_628 = lean_ctor_get(x_623, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_623, 1);
lean_inc(x_629);
if (lean_is_exclusive(x_623)) {
 lean_ctor_release(x_623, 0);
 lean_ctor_release(x_623, 1);
 x_630 = x_623;
} else {
 lean_dec_ref(x_623);
 x_630 = lean_box(0);
}
if (lean_is_scalar(x_630)) {
 x_631 = lean_alloc_ctor(1, 2, 0);
} else {
 x_631 = x_630;
}
lean_ctor_set(x_631, 0, x_628);
lean_ctor_set(x_631, 1, x_629);
return x_631;
}
}
else
{
uint8_t x_632; 
x_632 = lean_ctor_get_uint8(x_615, 12);
if (x_632 == 0)
{
lean_object* x_633; uint8_t x_634; uint8_t x_635; lean_object* x_636; uint64_t x_637; lean_object* x_638; lean_object* x_639; 
lean_dec(x_615);
lean_dec(x_613);
x_633 = lean_ctor_get(x_614, 1);
lean_inc(x_633);
lean_dec(x_614);
x_634 = 1;
x_635 = 2;
x_636 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_636, 0, x_490);
lean_ctor_set_uint8(x_636, 1, x_491);
lean_ctor_set_uint8(x_636, 2, x_492);
lean_ctor_set_uint8(x_636, 3, x_493);
lean_ctor_set_uint8(x_636, 4, x_494);
lean_ctor_set_uint8(x_636, 5, x_495);
lean_ctor_set_uint8(x_636, 6, x_496);
lean_ctor_set_uint8(x_636, 7, x_497);
lean_ctor_set_uint8(x_636, 8, x_498);
lean_ctor_set_uint8(x_636, 9, x_509);
lean_ctor_set_uint8(x_636, 10, x_500);
lean_ctor_set_uint8(x_636, 11, x_501);
lean_ctor_set_uint8(x_636, 12, x_634);
lean_ctor_set_uint8(x_636, 13, x_634);
lean_ctor_set_uint8(x_636, 14, x_635);
lean_ctor_set_uint8(x_636, 15, x_634);
lean_ctor_set_uint8(x_636, 16, x_634);
lean_ctor_set_uint8(x_636, 17, x_507);
x_637 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_636);
x_638 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_638, 0, x_636);
lean_ctor_set(x_638, 1, x_482);
lean_ctor_set(x_638, 2, x_483);
lean_ctor_set(x_638, 3, x_484);
lean_ctor_set(x_638, 4, x_485);
lean_ctor_set(x_638, 5, x_486);
lean_ctor_set(x_638, 6, x_487);
lean_ctor_set_uint64(x_638, sizeof(void*)*7, x_637);
lean_ctor_set_uint8(x_638, sizeof(void*)*7 + 8, x_481);
lean_ctor_set_uint8(x_638, sizeof(void*)*7 + 9, x_488);
lean_ctor_set_uint8(x_638, sizeof(void*)*7 + 10, x_489);
x_639 = l_Lean_Meta_inferTypeImp_infer(x_1, x_638, x_3, x_4, x_5, x_633);
if (lean_obj_tag(x_639) == 0)
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_639, 1);
lean_inc(x_641);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 lean_ctor_release(x_639, 1);
 x_642 = x_639;
} else {
 lean_dec_ref(x_639);
 x_642 = lean_box(0);
}
if (lean_is_scalar(x_642)) {
 x_643 = lean_alloc_ctor(0, 2, 0);
} else {
 x_643 = x_642;
}
lean_ctor_set(x_643, 0, x_640);
lean_ctor_set(x_643, 1, x_641);
return x_643;
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_644 = lean_ctor_get(x_639, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_639, 1);
lean_inc(x_645);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 lean_ctor_release(x_639, 1);
 x_646 = x_639;
} else {
 lean_dec_ref(x_639);
 x_646 = lean_box(0);
}
if (lean_is_scalar(x_646)) {
 x_647 = lean_alloc_ctor(1, 2, 0);
} else {
 x_647 = x_646;
}
lean_ctor_set(x_647, 0, x_644);
lean_ctor_set(x_647, 1, x_645);
return x_647;
}
}
else
{
uint8_t x_648; 
x_648 = lean_ctor_get_uint8(x_615, 15);
if (x_648 == 0)
{
lean_object* x_649; uint8_t x_650; uint8_t x_651; lean_object* x_652; uint64_t x_653; lean_object* x_654; lean_object* x_655; 
lean_dec(x_615);
lean_dec(x_613);
x_649 = lean_ctor_get(x_614, 1);
lean_inc(x_649);
lean_dec(x_614);
x_650 = 1;
x_651 = 2;
x_652 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_652, 0, x_490);
lean_ctor_set_uint8(x_652, 1, x_491);
lean_ctor_set_uint8(x_652, 2, x_492);
lean_ctor_set_uint8(x_652, 3, x_493);
lean_ctor_set_uint8(x_652, 4, x_494);
lean_ctor_set_uint8(x_652, 5, x_495);
lean_ctor_set_uint8(x_652, 6, x_496);
lean_ctor_set_uint8(x_652, 7, x_497);
lean_ctor_set_uint8(x_652, 8, x_498);
lean_ctor_set_uint8(x_652, 9, x_509);
lean_ctor_set_uint8(x_652, 10, x_500);
lean_ctor_set_uint8(x_652, 11, x_501);
lean_ctor_set_uint8(x_652, 12, x_650);
lean_ctor_set_uint8(x_652, 13, x_650);
lean_ctor_set_uint8(x_652, 14, x_651);
lean_ctor_set_uint8(x_652, 15, x_650);
lean_ctor_set_uint8(x_652, 16, x_650);
lean_ctor_set_uint8(x_652, 17, x_507);
x_653 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_652);
x_654 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_654, 0, x_652);
lean_ctor_set(x_654, 1, x_482);
lean_ctor_set(x_654, 2, x_483);
lean_ctor_set(x_654, 3, x_484);
lean_ctor_set(x_654, 4, x_485);
lean_ctor_set(x_654, 5, x_486);
lean_ctor_set(x_654, 6, x_487);
lean_ctor_set_uint64(x_654, sizeof(void*)*7, x_653);
lean_ctor_set_uint8(x_654, sizeof(void*)*7 + 8, x_481);
lean_ctor_set_uint8(x_654, sizeof(void*)*7 + 9, x_488);
lean_ctor_set_uint8(x_654, sizeof(void*)*7 + 10, x_489);
x_655 = l_Lean_Meta_inferTypeImp_infer(x_1, x_654, x_3, x_4, x_5, x_649);
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
uint8_t x_664; 
x_664 = lean_ctor_get_uint8(x_615, 16);
if (x_664 == 0)
{
lean_object* x_665; uint8_t x_666; uint8_t x_667; lean_object* x_668; uint64_t x_669; lean_object* x_670; lean_object* x_671; 
lean_dec(x_615);
lean_dec(x_613);
x_665 = lean_ctor_get(x_614, 1);
lean_inc(x_665);
lean_dec(x_614);
x_666 = 1;
x_667 = 2;
x_668 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_668, 0, x_490);
lean_ctor_set_uint8(x_668, 1, x_491);
lean_ctor_set_uint8(x_668, 2, x_492);
lean_ctor_set_uint8(x_668, 3, x_493);
lean_ctor_set_uint8(x_668, 4, x_494);
lean_ctor_set_uint8(x_668, 5, x_495);
lean_ctor_set_uint8(x_668, 6, x_496);
lean_ctor_set_uint8(x_668, 7, x_497);
lean_ctor_set_uint8(x_668, 8, x_498);
lean_ctor_set_uint8(x_668, 9, x_509);
lean_ctor_set_uint8(x_668, 10, x_500);
lean_ctor_set_uint8(x_668, 11, x_501);
lean_ctor_set_uint8(x_668, 12, x_666);
lean_ctor_set_uint8(x_668, 13, x_666);
lean_ctor_set_uint8(x_668, 14, x_667);
lean_ctor_set_uint8(x_668, 15, x_666);
lean_ctor_set_uint8(x_668, 16, x_666);
lean_ctor_set_uint8(x_668, 17, x_507);
x_669 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_668);
x_670 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_670, 0, x_668);
lean_ctor_set(x_670, 1, x_482);
lean_ctor_set(x_670, 2, x_483);
lean_ctor_set(x_670, 3, x_484);
lean_ctor_set(x_670, 4, x_485);
lean_ctor_set(x_670, 5, x_486);
lean_ctor_set(x_670, 6, x_487);
lean_ctor_set_uint64(x_670, sizeof(void*)*7, x_669);
lean_ctor_set_uint8(x_670, sizeof(void*)*7 + 8, x_481);
lean_ctor_set_uint8(x_670, sizeof(void*)*7 + 9, x_488);
lean_ctor_set_uint8(x_670, sizeof(void*)*7 + 10, x_489);
x_671 = l_Lean_Meta_inferTypeImp_infer(x_1, x_670, x_3, x_4, x_5, x_665);
if (lean_obj_tag(x_671) == 0)
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_672 = lean_ctor_get(x_671, 0);
lean_inc(x_672);
x_673 = lean_ctor_get(x_671, 1);
lean_inc(x_673);
if (lean_is_exclusive(x_671)) {
 lean_ctor_release(x_671, 0);
 lean_ctor_release(x_671, 1);
 x_674 = x_671;
} else {
 lean_dec_ref(x_671);
 x_674 = lean_box(0);
}
if (lean_is_scalar(x_674)) {
 x_675 = lean_alloc_ctor(0, 2, 0);
} else {
 x_675 = x_674;
}
lean_ctor_set(x_675, 0, x_672);
lean_ctor_set(x_675, 1, x_673);
return x_675;
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_676 = lean_ctor_get(x_671, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_671, 1);
lean_inc(x_677);
if (lean_is_exclusive(x_671)) {
 lean_ctor_release(x_671, 0);
 lean_ctor_release(x_671, 1);
 x_678 = x_671;
} else {
 lean_dec_ref(x_671);
 x_678 = lean_box(0);
}
if (lean_is_scalar(x_678)) {
 x_679 = lean_alloc_ctor(1, 2, 0);
} else {
 x_679 = x_678;
}
lean_ctor_set(x_679, 0, x_676);
lean_ctor_set(x_679, 1, x_677);
return x_679;
}
}
else
{
lean_object* x_680; uint8_t x_681; uint8_t x_682; uint8_t x_683; 
x_680 = lean_ctor_get(x_614, 1);
lean_inc(x_680);
lean_dec(x_614);
x_681 = lean_ctor_get_uint8(x_615, 14);
lean_dec(x_615);
x_682 = 2;
x_683 = l_Lean_Meta_instDecidableEqProjReductionKind(x_681, x_682);
if (x_683 == 0)
{
uint8_t x_684; lean_object* x_685; uint64_t x_686; lean_object* x_687; lean_object* x_688; 
lean_dec(x_613);
x_684 = 1;
x_685 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_685, 0, x_490);
lean_ctor_set_uint8(x_685, 1, x_491);
lean_ctor_set_uint8(x_685, 2, x_492);
lean_ctor_set_uint8(x_685, 3, x_493);
lean_ctor_set_uint8(x_685, 4, x_494);
lean_ctor_set_uint8(x_685, 5, x_495);
lean_ctor_set_uint8(x_685, 6, x_496);
lean_ctor_set_uint8(x_685, 7, x_497);
lean_ctor_set_uint8(x_685, 8, x_498);
lean_ctor_set_uint8(x_685, 9, x_509);
lean_ctor_set_uint8(x_685, 10, x_500);
lean_ctor_set_uint8(x_685, 11, x_501);
lean_ctor_set_uint8(x_685, 12, x_684);
lean_ctor_set_uint8(x_685, 13, x_684);
lean_ctor_set_uint8(x_685, 14, x_682);
lean_ctor_set_uint8(x_685, 15, x_684);
lean_ctor_set_uint8(x_685, 16, x_684);
lean_ctor_set_uint8(x_685, 17, x_507);
x_686 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_685);
x_687 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_687, 0, x_685);
lean_ctor_set(x_687, 1, x_482);
lean_ctor_set(x_687, 2, x_483);
lean_ctor_set(x_687, 3, x_484);
lean_ctor_set(x_687, 4, x_485);
lean_ctor_set(x_687, 5, x_486);
lean_ctor_set(x_687, 6, x_487);
lean_ctor_set_uint64(x_687, sizeof(void*)*7, x_686);
lean_ctor_set_uint8(x_687, sizeof(void*)*7 + 8, x_481);
lean_ctor_set_uint8(x_687, sizeof(void*)*7 + 9, x_488);
lean_ctor_set_uint8(x_687, sizeof(void*)*7 + 10, x_489);
x_688 = l_Lean_Meta_inferTypeImp_infer(x_1, x_687, x_3, x_4, x_5, x_680);
if (lean_obj_tag(x_688) == 0)
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_688, 1);
lean_inc(x_690);
if (lean_is_exclusive(x_688)) {
 lean_ctor_release(x_688, 0);
 lean_ctor_release(x_688, 1);
 x_691 = x_688;
} else {
 lean_dec_ref(x_688);
 x_691 = lean_box(0);
}
if (lean_is_scalar(x_691)) {
 x_692 = lean_alloc_ctor(0, 2, 0);
} else {
 x_692 = x_691;
}
lean_ctor_set(x_692, 0, x_689);
lean_ctor_set(x_692, 1, x_690);
return x_692;
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_693 = lean_ctor_get(x_688, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_688, 1);
lean_inc(x_694);
if (lean_is_exclusive(x_688)) {
 lean_ctor_release(x_688, 0);
 lean_ctor_release(x_688, 1);
 x_695 = x_688;
} else {
 lean_dec_ref(x_688);
 x_695 = lean_box(0);
}
if (lean_is_scalar(x_695)) {
 x_696 = lean_alloc_ctor(1, 2, 0);
} else {
 x_696 = x_695;
}
lean_ctor_set(x_696, 0, x_693);
lean_ctor_set(x_696, 1, x_694);
return x_696;
}
}
else
{
lean_object* x_697; 
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_484);
lean_dec(x_483);
lean_dec(x_482);
x_697 = l_Lean_Meta_inferTypeImp_infer(x_1, x_613, x_3, x_4, x_5, x_680);
if (lean_obj_tag(x_697) == 0)
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; 
x_698 = lean_ctor_get(x_697, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_697, 1);
lean_inc(x_699);
if (lean_is_exclusive(x_697)) {
 lean_ctor_release(x_697, 0);
 lean_ctor_release(x_697, 1);
 x_700 = x_697;
} else {
 lean_dec_ref(x_697);
 x_700 = lean_box(0);
}
if (lean_is_scalar(x_700)) {
 x_701 = lean_alloc_ctor(0, 2, 0);
} else {
 x_701 = x_700;
}
lean_ctor_set(x_701, 0, x_698);
lean_ctor_set(x_701, 1, x_699);
return x_701;
}
else
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; 
x_702 = lean_ctor_get(x_697, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_697, 1);
lean_inc(x_703);
if (lean_is_exclusive(x_697)) {
 lean_ctor_release(x_697, 0);
 lean_ctor_release(x_697, 1);
 x_704 = x_697;
} else {
 lean_dec_ref(x_697);
 x_704 = lean_box(0);
}
if (lean_is_scalar(x_704)) {
 x_705 = lean_alloc_ctor(1, 2, 0);
} else {
 x_705 = x_704;
}
lean_ctor_set(x_705, 0, x_702);
lean_ctor_set(x_705, 1, x_703);
return x_705;
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
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; uint64_t x_710; uint8_t x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; uint8_t x_718; uint8_t x_719; lean_object* x_720; uint8_t x_721; uint8_t x_722; uint8_t x_723; uint8_t x_724; uint8_t x_725; uint8_t x_726; uint8_t x_727; uint8_t x_728; uint8_t x_729; uint8_t x_730; uint8_t x_731; uint8_t x_732; uint8_t x_733; uint8_t x_734; uint8_t x_735; uint8_t x_736; uint8_t x_737; uint8_t x_738; lean_object* x_739; uint8_t x_740; uint8_t x_741; uint64_t x_742; uint64_t x_743; uint64_t x_744; 
lean_dec(x_4);
x_706 = lean_unsigned_to_nat(1u);
x_707 = lean_nat_add(x_10, x_706);
lean_dec(x_10);
x_708 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_708, 0, x_7);
lean_ctor_set(x_708, 1, x_8);
lean_ctor_set(x_708, 2, x_9);
lean_ctor_set(x_708, 3, x_707);
lean_ctor_set(x_708, 4, x_11);
lean_ctor_set(x_708, 5, x_12);
lean_ctor_set(x_708, 6, x_13);
lean_ctor_set(x_708, 7, x_14);
lean_ctor_set(x_708, 8, x_15);
lean_ctor_set(x_708, 9, x_16);
lean_ctor_set(x_708, 10, x_17);
lean_ctor_set(x_708, 11, x_19);
lean_ctor_set_uint8(x_708, sizeof(void*)*12, x_18);
lean_ctor_set_uint8(x_708, sizeof(void*)*12 + 1, x_20);
x_709 = lean_ctor_get(x_2, 0);
lean_inc(x_709);
x_710 = lean_ctor_get_uint64(x_2, sizeof(void*)*7);
x_711 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_712 = lean_ctor_get(x_2, 1);
lean_inc(x_712);
x_713 = lean_ctor_get(x_2, 2);
lean_inc(x_713);
x_714 = lean_ctor_get(x_2, 3);
lean_inc(x_714);
x_715 = lean_ctor_get(x_2, 4);
lean_inc(x_715);
x_716 = lean_ctor_get(x_2, 5);
lean_inc(x_716);
x_717 = lean_ctor_get(x_2, 6);
lean_inc(x_717);
x_718 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_719 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_720 = x_2;
} else {
 lean_dec_ref(x_2);
 x_720 = lean_box(0);
}
x_721 = lean_ctor_get_uint8(x_709, 0);
x_722 = lean_ctor_get_uint8(x_709, 1);
x_723 = lean_ctor_get_uint8(x_709, 2);
x_724 = lean_ctor_get_uint8(x_709, 3);
x_725 = lean_ctor_get_uint8(x_709, 4);
x_726 = lean_ctor_get_uint8(x_709, 5);
x_727 = lean_ctor_get_uint8(x_709, 6);
x_728 = lean_ctor_get_uint8(x_709, 7);
x_729 = lean_ctor_get_uint8(x_709, 8);
x_730 = lean_ctor_get_uint8(x_709, 9);
x_731 = lean_ctor_get_uint8(x_709, 10);
x_732 = lean_ctor_get_uint8(x_709, 11);
x_733 = lean_ctor_get_uint8(x_709, 12);
x_734 = lean_ctor_get_uint8(x_709, 13);
x_735 = lean_ctor_get_uint8(x_709, 14);
x_736 = lean_ctor_get_uint8(x_709, 15);
x_737 = lean_ctor_get_uint8(x_709, 16);
x_738 = lean_ctor_get_uint8(x_709, 17);
if (lean_is_exclusive(x_709)) {
 x_739 = x_709;
} else {
 lean_dec_ref(x_709);
 x_739 = lean_box(0);
}
x_740 = 1;
x_741 = l_Lean_Meta_TransparencyMode_lt(x_730, x_740);
x_742 = 2;
x_743 = lean_uint64_shift_right(x_710, x_742);
x_744 = lean_uint64_shift_left(x_743, x_742);
if (x_741 == 0)
{
lean_object* x_745; uint64_t x_746; uint64_t x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; 
if (lean_is_scalar(x_739)) {
 x_745 = lean_alloc_ctor(0, 0, 18);
} else {
 x_745 = x_739;
}
lean_ctor_set_uint8(x_745, 0, x_721);
lean_ctor_set_uint8(x_745, 1, x_722);
lean_ctor_set_uint8(x_745, 2, x_723);
lean_ctor_set_uint8(x_745, 3, x_724);
lean_ctor_set_uint8(x_745, 4, x_725);
lean_ctor_set_uint8(x_745, 5, x_726);
lean_ctor_set_uint8(x_745, 6, x_727);
lean_ctor_set_uint8(x_745, 7, x_728);
lean_ctor_set_uint8(x_745, 8, x_729);
lean_ctor_set_uint8(x_745, 9, x_730);
lean_ctor_set_uint8(x_745, 10, x_731);
lean_ctor_set_uint8(x_745, 11, x_732);
lean_ctor_set_uint8(x_745, 12, x_733);
lean_ctor_set_uint8(x_745, 13, x_734);
lean_ctor_set_uint8(x_745, 14, x_735);
lean_ctor_set_uint8(x_745, 15, x_736);
lean_ctor_set_uint8(x_745, 16, x_737);
lean_ctor_set_uint8(x_745, 17, x_738);
x_746 = l_Lean_Meta_TransparencyMode_toUInt64(x_730);
x_747 = lean_uint64_lor(x_744, x_746);
lean_inc(x_717);
lean_inc(x_716);
lean_inc(x_715);
lean_inc(x_714);
lean_inc(x_713);
lean_inc(x_712);
if (lean_is_scalar(x_720)) {
 x_748 = lean_alloc_ctor(0, 7, 11);
} else {
 x_748 = x_720;
}
lean_ctor_set(x_748, 0, x_745);
lean_ctor_set(x_748, 1, x_712);
lean_ctor_set(x_748, 2, x_713);
lean_ctor_set(x_748, 3, x_714);
lean_ctor_set(x_748, 4, x_715);
lean_ctor_set(x_748, 5, x_716);
lean_ctor_set(x_748, 6, x_717);
lean_ctor_set_uint64(x_748, sizeof(void*)*7, x_747);
lean_ctor_set_uint8(x_748, sizeof(void*)*7 + 8, x_711);
lean_ctor_set_uint8(x_748, sizeof(void*)*7 + 9, x_718);
lean_ctor_set_uint8(x_748, sizeof(void*)*7 + 10, x_719);
x_749 = l_Lean_Meta_getConfig(x_748, x_3, x_708, x_5, x_6);
x_750 = lean_ctor_get(x_749, 0);
lean_inc(x_750);
x_751 = lean_ctor_get_uint8(x_750, 13);
if (x_751 == 0)
{
lean_object* x_752; uint8_t x_753; uint8_t x_754; lean_object* x_755; uint64_t x_756; lean_object* x_757; lean_object* x_758; 
lean_dec(x_750);
lean_dec(x_748);
x_752 = lean_ctor_get(x_749, 1);
lean_inc(x_752);
lean_dec(x_749);
x_753 = 1;
x_754 = 2;
x_755 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_755, 0, x_721);
lean_ctor_set_uint8(x_755, 1, x_722);
lean_ctor_set_uint8(x_755, 2, x_723);
lean_ctor_set_uint8(x_755, 3, x_724);
lean_ctor_set_uint8(x_755, 4, x_725);
lean_ctor_set_uint8(x_755, 5, x_726);
lean_ctor_set_uint8(x_755, 6, x_727);
lean_ctor_set_uint8(x_755, 7, x_728);
lean_ctor_set_uint8(x_755, 8, x_729);
lean_ctor_set_uint8(x_755, 9, x_730);
lean_ctor_set_uint8(x_755, 10, x_731);
lean_ctor_set_uint8(x_755, 11, x_732);
lean_ctor_set_uint8(x_755, 12, x_753);
lean_ctor_set_uint8(x_755, 13, x_753);
lean_ctor_set_uint8(x_755, 14, x_754);
lean_ctor_set_uint8(x_755, 15, x_753);
lean_ctor_set_uint8(x_755, 16, x_753);
lean_ctor_set_uint8(x_755, 17, x_738);
x_756 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_755);
x_757 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_757, 0, x_755);
lean_ctor_set(x_757, 1, x_712);
lean_ctor_set(x_757, 2, x_713);
lean_ctor_set(x_757, 3, x_714);
lean_ctor_set(x_757, 4, x_715);
lean_ctor_set(x_757, 5, x_716);
lean_ctor_set(x_757, 6, x_717);
lean_ctor_set_uint64(x_757, sizeof(void*)*7, x_756);
lean_ctor_set_uint8(x_757, sizeof(void*)*7 + 8, x_711);
lean_ctor_set_uint8(x_757, sizeof(void*)*7 + 9, x_718);
lean_ctor_set_uint8(x_757, sizeof(void*)*7 + 10, x_719);
x_758 = l_Lean_Meta_inferTypeImp_infer(x_1, x_757, x_3, x_708, x_5, x_752);
if (lean_obj_tag(x_758) == 0)
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; 
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
if (lean_is_exclusive(x_758)) {
 lean_ctor_release(x_758, 0);
 lean_ctor_release(x_758, 1);
 x_761 = x_758;
} else {
 lean_dec_ref(x_758);
 x_761 = lean_box(0);
}
if (lean_is_scalar(x_761)) {
 x_762 = lean_alloc_ctor(0, 2, 0);
} else {
 x_762 = x_761;
}
lean_ctor_set(x_762, 0, x_759);
lean_ctor_set(x_762, 1, x_760);
return x_762;
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_763 = lean_ctor_get(x_758, 0);
lean_inc(x_763);
x_764 = lean_ctor_get(x_758, 1);
lean_inc(x_764);
if (lean_is_exclusive(x_758)) {
 lean_ctor_release(x_758, 0);
 lean_ctor_release(x_758, 1);
 x_765 = x_758;
} else {
 lean_dec_ref(x_758);
 x_765 = lean_box(0);
}
if (lean_is_scalar(x_765)) {
 x_766 = lean_alloc_ctor(1, 2, 0);
} else {
 x_766 = x_765;
}
lean_ctor_set(x_766, 0, x_763);
lean_ctor_set(x_766, 1, x_764);
return x_766;
}
}
else
{
uint8_t x_767; 
x_767 = lean_ctor_get_uint8(x_750, 12);
if (x_767 == 0)
{
lean_object* x_768; uint8_t x_769; uint8_t x_770; lean_object* x_771; uint64_t x_772; lean_object* x_773; lean_object* x_774; 
lean_dec(x_750);
lean_dec(x_748);
x_768 = lean_ctor_get(x_749, 1);
lean_inc(x_768);
lean_dec(x_749);
x_769 = 1;
x_770 = 2;
x_771 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_771, 0, x_721);
lean_ctor_set_uint8(x_771, 1, x_722);
lean_ctor_set_uint8(x_771, 2, x_723);
lean_ctor_set_uint8(x_771, 3, x_724);
lean_ctor_set_uint8(x_771, 4, x_725);
lean_ctor_set_uint8(x_771, 5, x_726);
lean_ctor_set_uint8(x_771, 6, x_727);
lean_ctor_set_uint8(x_771, 7, x_728);
lean_ctor_set_uint8(x_771, 8, x_729);
lean_ctor_set_uint8(x_771, 9, x_730);
lean_ctor_set_uint8(x_771, 10, x_731);
lean_ctor_set_uint8(x_771, 11, x_732);
lean_ctor_set_uint8(x_771, 12, x_769);
lean_ctor_set_uint8(x_771, 13, x_769);
lean_ctor_set_uint8(x_771, 14, x_770);
lean_ctor_set_uint8(x_771, 15, x_769);
lean_ctor_set_uint8(x_771, 16, x_769);
lean_ctor_set_uint8(x_771, 17, x_738);
x_772 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_771);
x_773 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_773, 0, x_771);
lean_ctor_set(x_773, 1, x_712);
lean_ctor_set(x_773, 2, x_713);
lean_ctor_set(x_773, 3, x_714);
lean_ctor_set(x_773, 4, x_715);
lean_ctor_set(x_773, 5, x_716);
lean_ctor_set(x_773, 6, x_717);
lean_ctor_set_uint64(x_773, sizeof(void*)*7, x_772);
lean_ctor_set_uint8(x_773, sizeof(void*)*7 + 8, x_711);
lean_ctor_set_uint8(x_773, sizeof(void*)*7 + 9, x_718);
lean_ctor_set_uint8(x_773, sizeof(void*)*7 + 10, x_719);
x_774 = l_Lean_Meta_inferTypeImp_infer(x_1, x_773, x_3, x_708, x_5, x_768);
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_775 = lean_ctor_get(x_774, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_774, 1);
lean_inc(x_776);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 lean_ctor_release(x_774, 1);
 x_777 = x_774;
} else {
 lean_dec_ref(x_774);
 x_777 = lean_box(0);
}
if (lean_is_scalar(x_777)) {
 x_778 = lean_alloc_ctor(0, 2, 0);
} else {
 x_778 = x_777;
}
lean_ctor_set(x_778, 0, x_775);
lean_ctor_set(x_778, 1, x_776);
return x_778;
}
else
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_779 = lean_ctor_get(x_774, 0);
lean_inc(x_779);
x_780 = lean_ctor_get(x_774, 1);
lean_inc(x_780);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 lean_ctor_release(x_774, 1);
 x_781 = x_774;
} else {
 lean_dec_ref(x_774);
 x_781 = lean_box(0);
}
if (lean_is_scalar(x_781)) {
 x_782 = lean_alloc_ctor(1, 2, 0);
} else {
 x_782 = x_781;
}
lean_ctor_set(x_782, 0, x_779);
lean_ctor_set(x_782, 1, x_780);
return x_782;
}
}
else
{
uint8_t x_783; 
x_783 = lean_ctor_get_uint8(x_750, 15);
if (x_783 == 0)
{
lean_object* x_784; uint8_t x_785; uint8_t x_786; lean_object* x_787; uint64_t x_788; lean_object* x_789; lean_object* x_790; 
lean_dec(x_750);
lean_dec(x_748);
x_784 = lean_ctor_get(x_749, 1);
lean_inc(x_784);
lean_dec(x_749);
x_785 = 1;
x_786 = 2;
x_787 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_787, 0, x_721);
lean_ctor_set_uint8(x_787, 1, x_722);
lean_ctor_set_uint8(x_787, 2, x_723);
lean_ctor_set_uint8(x_787, 3, x_724);
lean_ctor_set_uint8(x_787, 4, x_725);
lean_ctor_set_uint8(x_787, 5, x_726);
lean_ctor_set_uint8(x_787, 6, x_727);
lean_ctor_set_uint8(x_787, 7, x_728);
lean_ctor_set_uint8(x_787, 8, x_729);
lean_ctor_set_uint8(x_787, 9, x_730);
lean_ctor_set_uint8(x_787, 10, x_731);
lean_ctor_set_uint8(x_787, 11, x_732);
lean_ctor_set_uint8(x_787, 12, x_785);
lean_ctor_set_uint8(x_787, 13, x_785);
lean_ctor_set_uint8(x_787, 14, x_786);
lean_ctor_set_uint8(x_787, 15, x_785);
lean_ctor_set_uint8(x_787, 16, x_785);
lean_ctor_set_uint8(x_787, 17, x_738);
x_788 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_787);
x_789 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_789, 0, x_787);
lean_ctor_set(x_789, 1, x_712);
lean_ctor_set(x_789, 2, x_713);
lean_ctor_set(x_789, 3, x_714);
lean_ctor_set(x_789, 4, x_715);
lean_ctor_set(x_789, 5, x_716);
lean_ctor_set(x_789, 6, x_717);
lean_ctor_set_uint64(x_789, sizeof(void*)*7, x_788);
lean_ctor_set_uint8(x_789, sizeof(void*)*7 + 8, x_711);
lean_ctor_set_uint8(x_789, sizeof(void*)*7 + 9, x_718);
lean_ctor_set_uint8(x_789, sizeof(void*)*7 + 10, x_719);
x_790 = l_Lean_Meta_inferTypeImp_infer(x_1, x_789, x_3, x_708, x_5, x_784);
if (lean_obj_tag(x_790) == 0)
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_791 = lean_ctor_get(x_790, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_790, 1);
lean_inc(x_792);
if (lean_is_exclusive(x_790)) {
 lean_ctor_release(x_790, 0);
 lean_ctor_release(x_790, 1);
 x_793 = x_790;
} else {
 lean_dec_ref(x_790);
 x_793 = lean_box(0);
}
if (lean_is_scalar(x_793)) {
 x_794 = lean_alloc_ctor(0, 2, 0);
} else {
 x_794 = x_793;
}
lean_ctor_set(x_794, 0, x_791);
lean_ctor_set(x_794, 1, x_792);
return x_794;
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
x_795 = lean_ctor_get(x_790, 0);
lean_inc(x_795);
x_796 = lean_ctor_get(x_790, 1);
lean_inc(x_796);
if (lean_is_exclusive(x_790)) {
 lean_ctor_release(x_790, 0);
 lean_ctor_release(x_790, 1);
 x_797 = x_790;
} else {
 lean_dec_ref(x_790);
 x_797 = lean_box(0);
}
if (lean_is_scalar(x_797)) {
 x_798 = lean_alloc_ctor(1, 2, 0);
} else {
 x_798 = x_797;
}
lean_ctor_set(x_798, 0, x_795);
lean_ctor_set(x_798, 1, x_796);
return x_798;
}
}
else
{
uint8_t x_799; 
x_799 = lean_ctor_get_uint8(x_750, 16);
if (x_799 == 0)
{
lean_object* x_800; uint8_t x_801; uint8_t x_802; lean_object* x_803; uint64_t x_804; lean_object* x_805; lean_object* x_806; 
lean_dec(x_750);
lean_dec(x_748);
x_800 = lean_ctor_get(x_749, 1);
lean_inc(x_800);
lean_dec(x_749);
x_801 = 1;
x_802 = 2;
x_803 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_803, 0, x_721);
lean_ctor_set_uint8(x_803, 1, x_722);
lean_ctor_set_uint8(x_803, 2, x_723);
lean_ctor_set_uint8(x_803, 3, x_724);
lean_ctor_set_uint8(x_803, 4, x_725);
lean_ctor_set_uint8(x_803, 5, x_726);
lean_ctor_set_uint8(x_803, 6, x_727);
lean_ctor_set_uint8(x_803, 7, x_728);
lean_ctor_set_uint8(x_803, 8, x_729);
lean_ctor_set_uint8(x_803, 9, x_730);
lean_ctor_set_uint8(x_803, 10, x_731);
lean_ctor_set_uint8(x_803, 11, x_732);
lean_ctor_set_uint8(x_803, 12, x_801);
lean_ctor_set_uint8(x_803, 13, x_801);
lean_ctor_set_uint8(x_803, 14, x_802);
lean_ctor_set_uint8(x_803, 15, x_801);
lean_ctor_set_uint8(x_803, 16, x_801);
lean_ctor_set_uint8(x_803, 17, x_738);
x_804 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_803);
x_805 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_805, 0, x_803);
lean_ctor_set(x_805, 1, x_712);
lean_ctor_set(x_805, 2, x_713);
lean_ctor_set(x_805, 3, x_714);
lean_ctor_set(x_805, 4, x_715);
lean_ctor_set(x_805, 5, x_716);
lean_ctor_set(x_805, 6, x_717);
lean_ctor_set_uint64(x_805, sizeof(void*)*7, x_804);
lean_ctor_set_uint8(x_805, sizeof(void*)*7 + 8, x_711);
lean_ctor_set_uint8(x_805, sizeof(void*)*7 + 9, x_718);
lean_ctor_set_uint8(x_805, sizeof(void*)*7 + 10, x_719);
x_806 = l_Lean_Meta_inferTypeImp_infer(x_1, x_805, x_3, x_708, x_5, x_800);
if (lean_obj_tag(x_806) == 0)
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_807 = lean_ctor_get(x_806, 0);
lean_inc(x_807);
x_808 = lean_ctor_get(x_806, 1);
lean_inc(x_808);
if (lean_is_exclusive(x_806)) {
 lean_ctor_release(x_806, 0);
 lean_ctor_release(x_806, 1);
 x_809 = x_806;
} else {
 lean_dec_ref(x_806);
 x_809 = lean_box(0);
}
if (lean_is_scalar(x_809)) {
 x_810 = lean_alloc_ctor(0, 2, 0);
} else {
 x_810 = x_809;
}
lean_ctor_set(x_810, 0, x_807);
lean_ctor_set(x_810, 1, x_808);
return x_810;
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_811 = lean_ctor_get(x_806, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_806, 1);
lean_inc(x_812);
if (lean_is_exclusive(x_806)) {
 lean_ctor_release(x_806, 0);
 lean_ctor_release(x_806, 1);
 x_813 = x_806;
} else {
 lean_dec_ref(x_806);
 x_813 = lean_box(0);
}
if (lean_is_scalar(x_813)) {
 x_814 = lean_alloc_ctor(1, 2, 0);
} else {
 x_814 = x_813;
}
lean_ctor_set(x_814, 0, x_811);
lean_ctor_set(x_814, 1, x_812);
return x_814;
}
}
else
{
lean_object* x_815; uint8_t x_816; uint8_t x_817; uint8_t x_818; 
x_815 = lean_ctor_get(x_749, 1);
lean_inc(x_815);
lean_dec(x_749);
x_816 = lean_ctor_get_uint8(x_750, 14);
lean_dec(x_750);
x_817 = 2;
x_818 = l_Lean_Meta_instDecidableEqProjReductionKind(x_816, x_817);
if (x_818 == 0)
{
uint8_t x_819; lean_object* x_820; uint64_t x_821; lean_object* x_822; lean_object* x_823; 
lean_dec(x_748);
x_819 = 1;
x_820 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_820, 0, x_721);
lean_ctor_set_uint8(x_820, 1, x_722);
lean_ctor_set_uint8(x_820, 2, x_723);
lean_ctor_set_uint8(x_820, 3, x_724);
lean_ctor_set_uint8(x_820, 4, x_725);
lean_ctor_set_uint8(x_820, 5, x_726);
lean_ctor_set_uint8(x_820, 6, x_727);
lean_ctor_set_uint8(x_820, 7, x_728);
lean_ctor_set_uint8(x_820, 8, x_729);
lean_ctor_set_uint8(x_820, 9, x_730);
lean_ctor_set_uint8(x_820, 10, x_731);
lean_ctor_set_uint8(x_820, 11, x_732);
lean_ctor_set_uint8(x_820, 12, x_819);
lean_ctor_set_uint8(x_820, 13, x_819);
lean_ctor_set_uint8(x_820, 14, x_817);
lean_ctor_set_uint8(x_820, 15, x_819);
lean_ctor_set_uint8(x_820, 16, x_819);
lean_ctor_set_uint8(x_820, 17, x_738);
x_821 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_820);
x_822 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_822, 0, x_820);
lean_ctor_set(x_822, 1, x_712);
lean_ctor_set(x_822, 2, x_713);
lean_ctor_set(x_822, 3, x_714);
lean_ctor_set(x_822, 4, x_715);
lean_ctor_set(x_822, 5, x_716);
lean_ctor_set(x_822, 6, x_717);
lean_ctor_set_uint64(x_822, sizeof(void*)*7, x_821);
lean_ctor_set_uint8(x_822, sizeof(void*)*7 + 8, x_711);
lean_ctor_set_uint8(x_822, sizeof(void*)*7 + 9, x_718);
lean_ctor_set_uint8(x_822, sizeof(void*)*7 + 10, x_719);
x_823 = l_Lean_Meta_inferTypeImp_infer(x_1, x_822, x_3, x_708, x_5, x_815);
if (lean_obj_tag(x_823) == 0)
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_824 = lean_ctor_get(x_823, 0);
lean_inc(x_824);
x_825 = lean_ctor_get(x_823, 1);
lean_inc(x_825);
if (lean_is_exclusive(x_823)) {
 lean_ctor_release(x_823, 0);
 lean_ctor_release(x_823, 1);
 x_826 = x_823;
} else {
 lean_dec_ref(x_823);
 x_826 = lean_box(0);
}
if (lean_is_scalar(x_826)) {
 x_827 = lean_alloc_ctor(0, 2, 0);
} else {
 x_827 = x_826;
}
lean_ctor_set(x_827, 0, x_824);
lean_ctor_set(x_827, 1, x_825);
return x_827;
}
else
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; 
x_828 = lean_ctor_get(x_823, 0);
lean_inc(x_828);
x_829 = lean_ctor_get(x_823, 1);
lean_inc(x_829);
if (lean_is_exclusive(x_823)) {
 lean_ctor_release(x_823, 0);
 lean_ctor_release(x_823, 1);
 x_830 = x_823;
} else {
 lean_dec_ref(x_823);
 x_830 = lean_box(0);
}
if (lean_is_scalar(x_830)) {
 x_831 = lean_alloc_ctor(1, 2, 0);
} else {
 x_831 = x_830;
}
lean_ctor_set(x_831, 0, x_828);
lean_ctor_set(x_831, 1, x_829);
return x_831;
}
}
else
{
lean_object* x_832; 
lean_dec(x_717);
lean_dec(x_716);
lean_dec(x_715);
lean_dec(x_714);
lean_dec(x_713);
lean_dec(x_712);
x_832 = l_Lean_Meta_inferTypeImp_infer(x_1, x_748, x_3, x_708, x_5, x_815);
if (lean_obj_tag(x_832) == 0)
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; 
x_833 = lean_ctor_get(x_832, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_832, 1);
lean_inc(x_834);
if (lean_is_exclusive(x_832)) {
 lean_ctor_release(x_832, 0);
 lean_ctor_release(x_832, 1);
 x_835 = x_832;
} else {
 lean_dec_ref(x_832);
 x_835 = lean_box(0);
}
if (lean_is_scalar(x_835)) {
 x_836 = lean_alloc_ctor(0, 2, 0);
} else {
 x_836 = x_835;
}
lean_ctor_set(x_836, 0, x_833);
lean_ctor_set(x_836, 1, x_834);
return x_836;
}
else
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; 
x_837 = lean_ctor_get(x_832, 0);
lean_inc(x_837);
x_838 = lean_ctor_get(x_832, 1);
lean_inc(x_838);
if (lean_is_exclusive(x_832)) {
 lean_ctor_release(x_832, 0);
 lean_ctor_release(x_832, 1);
 x_839 = x_832;
} else {
 lean_dec_ref(x_832);
 x_839 = lean_box(0);
}
if (lean_is_scalar(x_839)) {
 x_840 = lean_alloc_ctor(1, 2, 0);
} else {
 x_840 = x_839;
}
lean_ctor_set(x_840, 0, x_837);
lean_ctor_set(x_840, 1, x_838);
return x_840;
}
}
}
}
}
}
}
else
{
lean_object* x_841; uint64_t x_842; uint64_t x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; uint8_t x_847; 
if (lean_is_scalar(x_739)) {
 x_841 = lean_alloc_ctor(0, 0, 18);
} else {
 x_841 = x_739;
}
lean_ctor_set_uint8(x_841, 0, x_721);
lean_ctor_set_uint8(x_841, 1, x_722);
lean_ctor_set_uint8(x_841, 2, x_723);
lean_ctor_set_uint8(x_841, 3, x_724);
lean_ctor_set_uint8(x_841, 4, x_725);
lean_ctor_set_uint8(x_841, 5, x_726);
lean_ctor_set_uint8(x_841, 6, x_727);
lean_ctor_set_uint8(x_841, 7, x_728);
lean_ctor_set_uint8(x_841, 8, x_729);
lean_ctor_set_uint8(x_841, 9, x_740);
lean_ctor_set_uint8(x_841, 10, x_731);
lean_ctor_set_uint8(x_841, 11, x_732);
lean_ctor_set_uint8(x_841, 12, x_733);
lean_ctor_set_uint8(x_841, 13, x_734);
lean_ctor_set_uint8(x_841, 14, x_735);
lean_ctor_set_uint8(x_841, 15, x_736);
lean_ctor_set_uint8(x_841, 16, x_737);
lean_ctor_set_uint8(x_841, 17, x_738);
x_842 = l_Lean_Meta_withInferTypeConfig___rarg___closed__1;
x_843 = lean_uint64_lor(x_744, x_842);
lean_inc(x_717);
lean_inc(x_716);
lean_inc(x_715);
lean_inc(x_714);
lean_inc(x_713);
lean_inc(x_712);
if (lean_is_scalar(x_720)) {
 x_844 = lean_alloc_ctor(0, 7, 11);
} else {
 x_844 = x_720;
}
lean_ctor_set(x_844, 0, x_841);
lean_ctor_set(x_844, 1, x_712);
lean_ctor_set(x_844, 2, x_713);
lean_ctor_set(x_844, 3, x_714);
lean_ctor_set(x_844, 4, x_715);
lean_ctor_set(x_844, 5, x_716);
lean_ctor_set(x_844, 6, x_717);
lean_ctor_set_uint64(x_844, sizeof(void*)*7, x_843);
lean_ctor_set_uint8(x_844, sizeof(void*)*7 + 8, x_711);
lean_ctor_set_uint8(x_844, sizeof(void*)*7 + 9, x_718);
lean_ctor_set_uint8(x_844, sizeof(void*)*7 + 10, x_719);
x_845 = l_Lean_Meta_getConfig(x_844, x_3, x_708, x_5, x_6);
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
x_847 = lean_ctor_get_uint8(x_846, 13);
if (x_847 == 0)
{
lean_object* x_848; uint8_t x_849; uint8_t x_850; lean_object* x_851; uint64_t x_852; lean_object* x_853; lean_object* x_854; 
lean_dec(x_846);
lean_dec(x_844);
x_848 = lean_ctor_get(x_845, 1);
lean_inc(x_848);
lean_dec(x_845);
x_849 = 1;
x_850 = 2;
x_851 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_851, 0, x_721);
lean_ctor_set_uint8(x_851, 1, x_722);
lean_ctor_set_uint8(x_851, 2, x_723);
lean_ctor_set_uint8(x_851, 3, x_724);
lean_ctor_set_uint8(x_851, 4, x_725);
lean_ctor_set_uint8(x_851, 5, x_726);
lean_ctor_set_uint8(x_851, 6, x_727);
lean_ctor_set_uint8(x_851, 7, x_728);
lean_ctor_set_uint8(x_851, 8, x_729);
lean_ctor_set_uint8(x_851, 9, x_740);
lean_ctor_set_uint8(x_851, 10, x_731);
lean_ctor_set_uint8(x_851, 11, x_732);
lean_ctor_set_uint8(x_851, 12, x_849);
lean_ctor_set_uint8(x_851, 13, x_849);
lean_ctor_set_uint8(x_851, 14, x_850);
lean_ctor_set_uint8(x_851, 15, x_849);
lean_ctor_set_uint8(x_851, 16, x_849);
lean_ctor_set_uint8(x_851, 17, x_738);
x_852 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_851);
x_853 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_853, 0, x_851);
lean_ctor_set(x_853, 1, x_712);
lean_ctor_set(x_853, 2, x_713);
lean_ctor_set(x_853, 3, x_714);
lean_ctor_set(x_853, 4, x_715);
lean_ctor_set(x_853, 5, x_716);
lean_ctor_set(x_853, 6, x_717);
lean_ctor_set_uint64(x_853, sizeof(void*)*7, x_852);
lean_ctor_set_uint8(x_853, sizeof(void*)*7 + 8, x_711);
lean_ctor_set_uint8(x_853, sizeof(void*)*7 + 9, x_718);
lean_ctor_set_uint8(x_853, sizeof(void*)*7 + 10, x_719);
x_854 = l_Lean_Meta_inferTypeImp_infer(x_1, x_853, x_3, x_708, x_5, x_848);
if (lean_obj_tag(x_854) == 0)
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; 
x_855 = lean_ctor_get(x_854, 0);
lean_inc(x_855);
x_856 = lean_ctor_get(x_854, 1);
lean_inc(x_856);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_857 = x_854;
} else {
 lean_dec_ref(x_854);
 x_857 = lean_box(0);
}
if (lean_is_scalar(x_857)) {
 x_858 = lean_alloc_ctor(0, 2, 0);
} else {
 x_858 = x_857;
}
lean_ctor_set(x_858, 0, x_855);
lean_ctor_set(x_858, 1, x_856);
return x_858;
}
else
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; 
x_859 = lean_ctor_get(x_854, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_854, 1);
lean_inc(x_860);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_861 = x_854;
} else {
 lean_dec_ref(x_854);
 x_861 = lean_box(0);
}
if (lean_is_scalar(x_861)) {
 x_862 = lean_alloc_ctor(1, 2, 0);
} else {
 x_862 = x_861;
}
lean_ctor_set(x_862, 0, x_859);
lean_ctor_set(x_862, 1, x_860);
return x_862;
}
}
else
{
uint8_t x_863; 
x_863 = lean_ctor_get_uint8(x_846, 12);
if (x_863 == 0)
{
lean_object* x_864; uint8_t x_865; uint8_t x_866; lean_object* x_867; uint64_t x_868; lean_object* x_869; lean_object* x_870; 
lean_dec(x_846);
lean_dec(x_844);
x_864 = lean_ctor_get(x_845, 1);
lean_inc(x_864);
lean_dec(x_845);
x_865 = 1;
x_866 = 2;
x_867 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_867, 0, x_721);
lean_ctor_set_uint8(x_867, 1, x_722);
lean_ctor_set_uint8(x_867, 2, x_723);
lean_ctor_set_uint8(x_867, 3, x_724);
lean_ctor_set_uint8(x_867, 4, x_725);
lean_ctor_set_uint8(x_867, 5, x_726);
lean_ctor_set_uint8(x_867, 6, x_727);
lean_ctor_set_uint8(x_867, 7, x_728);
lean_ctor_set_uint8(x_867, 8, x_729);
lean_ctor_set_uint8(x_867, 9, x_740);
lean_ctor_set_uint8(x_867, 10, x_731);
lean_ctor_set_uint8(x_867, 11, x_732);
lean_ctor_set_uint8(x_867, 12, x_865);
lean_ctor_set_uint8(x_867, 13, x_865);
lean_ctor_set_uint8(x_867, 14, x_866);
lean_ctor_set_uint8(x_867, 15, x_865);
lean_ctor_set_uint8(x_867, 16, x_865);
lean_ctor_set_uint8(x_867, 17, x_738);
x_868 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_867);
x_869 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_869, 0, x_867);
lean_ctor_set(x_869, 1, x_712);
lean_ctor_set(x_869, 2, x_713);
lean_ctor_set(x_869, 3, x_714);
lean_ctor_set(x_869, 4, x_715);
lean_ctor_set(x_869, 5, x_716);
lean_ctor_set(x_869, 6, x_717);
lean_ctor_set_uint64(x_869, sizeof(void*)*7, x_868);
lean_ctor_set_uint8(x_869, sizeof(void*)*7 + 8, x_711);
lean_ctor_set_uint8(x_869, sizeof(void*)*7 + 9, x_718);
lean_ctor_set_uint8(x_869, sizeof(void*)*7 + 10, x_719);
x_870 = l_Lean_Meta_inferTypeImp_infer(x_1, x_869, x_3, x_708, x_5, x_864);
if (lean_obj_tag(x_870) == 0)
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; 
x_871 = lean_ctor_get(x_870, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_870, 1);
lean_inc(x_872);
if (lean_is_exclusive(x_870)) {
 lean_ctor_release(x_870, 0);
 lean_ctor_release(x_870, 1);
 x_873 = x_870;
} else {
 lean_dec_ref(x_870);
 x_873 = lean_box(0);
}
if (lean_is_scalar(x_873)) {
 x_874 = lean_alloc_ctor(0, 2, 0);
} else {
 x_874 = x_873;
}
lean_ctor_set(x_874, 0, x_871);
lean_ctor_set(x_874, 1, x_872);
return x_874;
}
else
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; 
x_875 = lean_ctor_get(x_870, 0);
lean_inc(x_875);
x_876 = lean_ctor_get(x_870, 1);
lean_inc(x_876);
if (lean_is_exclusive(x_870)) {
 lean_ctor_release(x_870, 0);
 lean_ctor_release(x_870, 1);
 x_877 = x_870;
} else {
 lean_dec_ref(x_870);
 x_877 = lean_box(0);
}
if (lean_is_scalar(x_877)) {
 x_878 = lean_alloc_ctor(1, 2, 0);
} else {
 x_878 = x_877;
}
lean_ctor_set(x_878, 0, x_875);
lean_ctor_set(x_878, 1, x_876);
return x_878;
}
}
else
{
uint8_t x_879; 
x_879 = lean_ctor_get_uint8(x_846, 15);
if (x_879 == 0)
{
lean_object* x_880; uint8_t x_881; uint8_t x_882; lean_object* x_883; uint64_t x_884; lean_object* x_885; lean_object* x_886; 
lean_dec(x_846);
lean_dec(x_844);
x_880 = lean_ctor_get(x_845, 1);
lean_inc(x_880);
lean_dec(x_845);
x_881 = 1;
x_882 = 2;
x_883 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_883, 0, x_721);
lean_ctor_set_uint8(x_883, 1, x_722);
lean_ctor_set_uint8(x_883, 2, x_723);
lean_ctor_set_uint8(x_883, 3, x_724);
lean_ctor_set_uint8(x_883, 4, x_725);
lean_ctor_set_uint8(x_883, 5, x_726);
lean_ctor_set_uint8(x_883, 6, x_727);
lean_ctor_set_uint8(x_883, 7, x_728);
lean_ctor_set_uint8(x_883, 8, x_729);
lean_ctor_set_uint8(x_883, 9, x_740);
lean_ctor_set_uint8(x_883, 10, x_731);
lean_ctor_set_uint8(x_883, 11, x_732);
lean_ctor_set_uint8(x_883, 12, x_881);
lean_ctor_set_uint8(x_883, 13, x_881);
lean_ctor_set_uint8(x_883, 14, x_882);
lean_ctor_set_uint8(x_883, 15, x_881);
lean_ctor_set_uint8(x_883, 16, x_881);
lean_ctor_set_uint8(x_883, 17, x_738);
x_884 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_883);
x_885 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_885, 0, x_883);
lean_ctor_set(x_885, 1, x_712);
lean_ctor_set(x_885, 2, x_713);
lean_ctor_set(x_885, 3, x_714);
lean_ctor_set(x_885, 4, x_715);
lean_ctor_set(x_885, 5, x_716);
lean_ctor_set(x_885, 6, x_717);
lean_ctor_set_uint64(x_885, sizeof(void*)*7, x_884);
lean_ctor_set_uint8(x_885, sizeof(void*)*7 + 8, x_711);
lean_ctor_set_uint8(x_885, sizeof(void*)*7 + 9, x_718);
lean_ctor_set_uint8(x_885, sizeof(void*)*7 + 10, x_719);
x_886 = l_Lean_Meta_inferTypeImp_infer(x_1, x_885, x_3, x_708, x_5, x_880);
if (lean_obj_tag(x_886) == 0)
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
x_887 = lean_ctor_get(x_886, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_886, 1);
lean_inc(x_888);
if (lean_is_exclusive(x_886)) {
 lean_ctor_release(x_886, 0);
 lean_ctor_release(x_886, 1);
 x_889 = x_886;
} else {
 lean_dec_ref(x_886);
 x_889 = lean_box(0);
}
if (lean_is_scalar(x_889)) {
 x_890 = lean_alloc_ctor(0, 2, 0);
} else {
 x_890 = x_889;
}
lean_ctor_set(x_890, 0, x_887);
lean_ctor_set(x_890, 1, x_888);
return x_890;
}
else
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_891 = lean_ctor_get(x_886, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_886, 1);
lean_inc(x_892);
if (lean_is_exclusive(x_886)) {
 lean_ctor_release(x_886, 0);
 lean_ctor_release(x_886, 1);
 x_893 = x_886;
} else {
 lean_dec_ref(x_886);
 x_893 = lean_box(0);
}
if (lean_is_scalar(x_893)) {
 x_894 = lean_alloc_ctor(1, 2, 0);
} else {
 x_894 = x_893;
}
lean_ctor_set(x_894, 0, x_891);
lean_ctor_set(x_894, 1, x_892);
return x_894;
}
}
else
{
uint8_t x_895; 
x_895 = lean_ctor_get_uint8(x_846, 16);
if (x_895 == 0)
{
lean_object* x_896; uint8_t x_897; uint8_t x_898; lean_object* x_899; uint64_t x_900; lean_object* x_901; lean_object* x_902; 
lean_dec(x_846);
lean_dec(x_844);
x_896 = lean_ctor_get(x_845, 1);
lean_inc(x_896);
lean_dec(x_845);
x_897 = 1;
x_898 = 2;
x_899 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_899, 0, x_721);
lean_ctor_set_uint8(x_899, 1, x_722);
lean_ctor_set_uint8(x_899, 2, x_723);
lean_ctor_set_uint8(x_899, 3, x_724);
lean_ctor_set_uint8(x_899, 4, x_725);
lean_ctor_set_uint8(x_899, 5, x_726);
lean_ctor_set_uint8(x_899, 6, x_727);
lean_ctor_set_uint8(x_899, 7, x_728);
lean_ctor_set_uint8(x_899, 8, x_729);
lean_ctor_set_uint8(x_899, 9, x_740);
lean_ctor_set_uint8(x_899, 10, x_731);
lean_ctor_set_uint8(x_899, 11, x_732);
lean_ctor_set_uint8(x_899, 12, x_897);
lean_ctor_set_uint8(x_899, 13, x_897);
lean_ctor_set_uint8(x_899, 14, x_898);
lean_ctor_set_uint8(x_899, 15, x_897);
lean_ctor_set_uint8(x_899, 16, x_897);
lean_ctor_set_uint8(x_899, 17, x_738);
x_900 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_899);
x_901 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_901, 0, x_899);
lean_ctor_set(x_901, 1, x_712);
lean_ctor_set(x_901, 2, x_713);
lean_ctor_set(x_901, 3, x_714);
lean_ctor_set(x_901, 4, x_715);
lean_ctor_set(x_901, 5, x_716);
lean_ctor_set(x_901, 6, x_717);
lean_ctor_set_uint64(x_901, sizeof(void*)*7, x_900);
lean_ctor_set_uint8(x_901, sizeof(void*)*7 + 8, x_711);
lean_ctor_set_uint8(x_901, sizeof(void*)*7 + 9, x_718);
lean_ctor_set_uint8(x_901, sizeof(void*)*7 + 10, x_719);
x_902 = l_Lean_Meta_inferTypeImp_infer(x_1, x_901, x_3, x_708, x_5, x_896);
if (lean_obj_tag(x_902) == 0)
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; 
x_903 = lean_ctor_get(x_902, 0);
lean_inc(x_903);
x_904 = lean_ctor_get(x_902, 1);
lean_inc(x_904);
if (lean_is_exclusive(x_902)) {
 lean_ctor_release(x_902, 0);
 lean_ctor_release(x_902, 1);
 x_905 = x_902;
} else {
 lean_dec_ref(x_902);
 x_905 = lean_box(0);
}
if (lean_is_scalar(x_905)) {
 x_906 = lean_alloc_ctor(0, 2, 0);
} else {
 x_906 = x_905;
}
lean_ctor_set(x_906, 0, x_903);
lean_ctor_set(x_906, 1, x_904);
return x_906;
}
else
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; 
x_907 = lean_ctor_get(x_902, 0);
lean_inc(x_907);
x_908 = lean_ctor_get(x_902, 1);
lean_inc(x_908);
if (lean_is_exclusive(x_902)) {
 lean_ctor_release(x_902, 0);
 lean_ctor_release(x_902, 1);
 x_909 = x_902;
} else {
 lean_dec_ref(x_902);
 x_909 = lean_box(0);
}
if (lean_is_scalar(x_909)) {
 x_910 = lean_alloc_ctor(1, 2, 0);
} else {
 x_910 = x_909;
}
lean_ctor_set(x_910, 0, x_907);
lean_ctor_set(x_910, 1, x_908);
return x_910;
}
}
else
{
lean_object* x_911; uint8_t x_912; uint8_t x_913; uint8_t x_914; 
x_911 = lean_ctor_get(x_845, 1);
lean_inc(x_911);
lean_dec(x_845);
x_912 = lean_ctor_get_uint8(x_846, 14);
lean_dec(x_846);
x_913 = 2;
x_914 = l_Lean_Meta_instDecidableEqProjReductionKind(x_912, x_913);
if (x_914 == 0)
{
uint8_t x_915; lean_object* x_916; uint64_t x_917; lean_object* x_918; lean_object* x_919; 
lean_dec(x_844);
x_915 = 1;
x_916 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_916, 0, x_721);
lean_ctor_set_uint8(x_916, 1, x_722);
lean_ctor_set_uint8(x_916, 2, x_723);
lean_ctor_set_uint8(x_916, 3, x_724);
lean_ctor_set_uint8(x_916, 4, x_725);
lean_ctor_set_uint8(x_916, 5, x_726);
lean_ctor_set_uint8(x_916, 6, x_727);
lean_ctor_set_uint8(x_916, 7, x_728);
lean_ctor_set_uint8(x_916, 8, x_729);
lean_ctor_set_uint8(x_916, 9, x_740);
lean_ctor_set_uint8(x_916, 10, x_731);
lean_ctor_set_uint8(x_916, 11, x_732);
lean_ctor_set_uint8(x_916, 12, x_915);
lean_ctor_set_uint8(x_916, 13, x_915);
lean_ctor_set_uint8(x_916, 14, x_913);
lean_ctor_set_uint8(x_916, 15, x_915);
lean_ctor_set_uint8(x_916, 16, x_915);
lean_ctor_set_uint8(x_916, 17, x_738);
x_917 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_916);
x_918 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_918, 0, x_916);
lean_ctor_set(x_918, 1, x_712);
lean_ctor_set(x_918, 2, x_713);
lean_ctor_set(x_918, 3, x_714);
lean_ctor_set(x_918, 4, x_715);
lean_ctor_set(x_918, 5, x_716);
lean_ctor_set(x_918, 6, x_717);
lean_ctor_set_uint64(x_918, sizeof(void*)*7, x_917);
lean_ctor_set_uint8(x_918, sizeof(void*)*7 + 8, x_711);
lean_ctor_set_uint8(x_918, sizeof(void*)*7 + 9, x_718);
lean_ctor_set_uint8(x_918, sizeof(void*)*7 + 10, x_719);
x_919 = l_Lean_Meta_inferTypeImp_infer(x_1, x_918, x_3, x_708, x_5, x_911);
if (lean_obj_tag(x_919) == 0)
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; 
x_920 = lean_ctor_get(x_919, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_919, 1);
lean_inc(x_921);
if (lean_is_exclusive(x_919)) {
 lean_ctor_release(x_919, 0);
 lean_ctor_release(x_919, 1);
 x_922 = x_919;
} else {
 lean_dec_ref(x_919);
 x_922 = lean_box(0);
}
if (lean_is_scalar(x_922)) {
 x_923 = lean_alloc_ctor(0, 2, 0);
} else {
 x_923 = x_922;
}
lean_ctor_set(x_923, 0, x_920);
lean_ctor_set(x_923, 1, x_921);
return x_923;
}
else
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; 
x_924 = lean_ctor_get(x_919, 0);
lean_inc(x_924);
x_925 = lean_ctor_get(x_919, 1);
lean_inc(x_925);
if (lean_is_exclusive(x_919)) {
 lean_ctor_release(x_919, 0);
 lean_ctor_release(x_919, 1);
 x_926 = x_919;
} else {
 lean_dec_ref(x_919);
 x_926 = lean_box(0);
}
if (lean_is_scalar(x_926)) {
 x_927 = lean_alloc_ctor(1, 2, 0);
} else {
 x_927 = x_926;
}
lean_ctor_set(x_927, 0, x_924);
lean_ctor_set(x_927, 1, x_925);
return x_927;
}
}
else
{
lean_object* x_928; 
lean_dec(x_717);
lean_dec(x_716);
lean_dec(x_715);
lean_dec(x_714);
lean_dec(x_713);
lean_dec(x_712);
x_928 = l_Lean_Meta_inferTypeImp_infer(x_1, x_844, x_3, x_708, x_5, x_911);
if (lean_obj_tag(x_928) == 0)
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; 
x_929 = lean_ctor_get(x_928, 0);
lean_inc(x_929);
x_930 = lean_ctor_get(x_928, 1);
lean_inc(x_930);
if (lean_is_exclusive(x_928)) {
 lean_ctor_release(x_928, 0);
 lean_ctor_release(x_928, 1);
 x_931 = x_928;
} else {
 lean_dec_ref(x_928);
 x_931 = lean_box(0);
}
if (lean_is_scalar(x_931)) {
 x_932 = lean_alloc_ctor(0, 2, 0);
} else {
 x_932 = x_931;
}
lean_ctor_set(x_932, 0, x_929);
lean_ctor_set(x_932, 1, x_930);
return x_932;
}
else
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; 
x_933 = lean_ctor_get(x_928, 0);
lean_inc(x_933);
x_934 = lean_ctor_get(x_928, 1);
lean_inc(x_934);
if (lean_is_exclusive(x_928)) {
 lean_ctor_release(x_928, 0);
 lean_ctor_release(x_928, 1);
 x_935 = x_928;
} else {
 lean_dec_ref(x_928);
 x_935 = lean_box(0);
}
if (lean_is_scalar(x_935)) {
 x_936 = lean_alloc_ctor(1, 2, 0);
} else {
 x_936 = x_935;
}
lean_ctor_set(x_936, 0, x_933);
lean_ctor_set(x_936, 1, x_934);
return x_936;
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
lean_object* x_937; 
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
x_937 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1(x_12, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_937;
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
