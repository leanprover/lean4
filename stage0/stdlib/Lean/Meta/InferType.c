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
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2;
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
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_outOfBounds___rarg(lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3;
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__11;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* l_Lean_Meta_getTransparency(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8___closed__1;
lean_object* lean_expr_consume_type_annotations(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__8___closed__1;
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
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_arrowDomainsN___lambda__2___closed__1;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwUnknownMVar___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp_infer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at_Lean_Meta_arrowDomainsN___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___rarg(lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__7;
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Meta_arrowDomainsN___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object*);
lean_object* l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ExprStructEq_instHashable;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1;
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
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__13;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__6;
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
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_404_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwIncorrectNumberOfLevels___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__3;
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
lean_object* l_instHashableNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__5;
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
x_735 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_404_(x_717, x_717);
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
x_758 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_404_(x_740, x_740);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_nat_dec_lt(x_8, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_7, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_28; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_7, x_20);
lean_dec(x_7);
x_28 = lean_ctor_get(x_10, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 7)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_ctor_get(x_28, 2);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_22 = x_32;
x_23 = x_15;
goto block_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_dec(x_10);
x_34 = l_Lean_Expr_instantiateBetaRevRange(x_28, x_33, x_8, x_2);
lean_dec(x_33);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_35 = lean_whnf(x_34, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 7)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 2);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_8);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_8);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_22 = x_40;
x_23 = x_37;
goto block_27;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_36);
lean_dec(x_21);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_dec(x_35);
x_42 = lean_nat_add(x_8, x_20);
lean_dec(x_8);
x_43 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_42, x_2, x_18, x_1);
lean_dec(x_42);
x_44 = l_Lean_Meta_throwFunctionExpected___rarg(x_43, x_11, x_12, x_13, x_14, x_41);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
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
uint8_t x_49; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_35);
if (x_49 == 0)
{
return x_35;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_35, 0);
x_51 = lean_ctor_get(x_35, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_35);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
block_27:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_nat_add(x_8, x_6);
lean_dec(x_8);
x_7 = x_21;
x_8 = x_25;
x_9 = lean_box(0);
x_10 = x_24;
x_15 = x_23;
goto _start;
}
}
else
{
lean_object* x_53; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_10);
lean_ctor_set(x_53, 1, x_15);
return x_53;
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
lean_inc(x_11);
x_16 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_2, x_14, x_12, x_11, x_13, x_11, x_12, lean_box(0), x_15, x_3, x_4, x_5, x_6, x_10);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
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
x_1 = lean_mk_string_unchecked(" from type ", 11, 11);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_10, x_7);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_9, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_30; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_9, x_22);
lean_dec(x_9);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_30 = lean_whnf(x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 7)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 2);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Expr_hasLooseBVars(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_33);
x_24 = x_35;
x_25 = x_32;
goto block_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc(x_3);
lean_inc(x_10);
lean_inc(x_1);
x_36 = l_Lean_Expr_proj___override(x_1, x_10, x_3);
x_37 = lean_expr_instantiate1(x_33, x_36);
lean_dec(x_36);
lean_dec(x_33);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_24 = x_38;
x_25 = x_32;
goto block_29;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_31);
lean_dec(x_23);
lean_dec(x_10);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_dec(x_30);
x_40 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_41 = l_Lean_indentExpr(x_40);
x_42 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_MessageData_ofExpr(x_4);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_49, x_13, x_14, x_15, x_16, x_39);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_30);
if (x_55 == 0)
{
return x_30;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_30, 0);
x_57 = lean_ctor_get(x_30, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_30);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
block_29:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_nat_add(x_10, x_8);
lean_dec(x_10);
x_9 = x_23;
x_10 = x_27;
x_11 = lean_box(0);
x_12 = x_26;
x_17 = x_25;
goto _start;
}
}
else
{
lean_object* x_59; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_12);
lean_ctor_set(x_59, 1, x_17);
return x_59;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
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
x_29 = l_Lean_MessageData_ofExpr(x_13);
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
x_42 = l_Lean_MessageData_ofExpr(x_13);
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
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_unsigned_to_nat(0u);
x_56 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_13, x_55);
x_57 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__1;
lean_inc(x_56);
x_58 = lean_mk_array(x_56, x_57);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_sub(x_56, x_59);
lean_dec(x_56);
lean_inc(x_13);
x_61 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_13, x_58, x_60);
x_62 = lean_ctor_get(x_35, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_35, 2);
lean_inc(x_63);
lean_dec(x_35);
x_64 = lean_nat_add(x_62, x_63);
lean_dec(x_63);
x_65 = lean_array_get_size(x_61);
x_66 = lean_nat_dec_eq(x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_54);
lean_dec(x_17);
x_67 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_68 = l_Lean_indentExpr(x_67);
x_69 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_68);
lean_ctor_set(x_36, 0, x_69);
x_70 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_70);
lean_ctor_set(x_18, 0, x_36);
x_71 = l_Lean_MessageData_ofExpr(x_13);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_18);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_74, x_4, x_5, x_6, x_7, x_53);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_54, 0);
lean_inc(x_76);
lean_dec(x_54);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_Lean_Expr_const___override(x_77, x_17);
x_79 = l_Array_toSubarray___rarg(x_61, x_55, x_62);
x_80 = l_Array_ofSubarray___rarg(x_79);
lean_dec(x_79);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_81 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_78, x_80, x_4, x_5, x_6, x_7, x_53);
lean_dec(x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_2);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_55);
lean_ctor_set(x_84, 1, x_2);
lean_ctor_set(x_84, 2, x_59);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_13);
lean_inc(x_3);
lean_inc_n(x_2, 2);
lean_inc(x_1);
x_85 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2(x_1, x_2, x_3, x_13, x_84, x_55, x_2, x_59, x_2, x_55, lean_box(0), x_82, x_4, x_5, x_6, x_7, x_83);
lean_dec(x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_88 = lean_whnf(x_86, x_4, x_5, x_6, x_7, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 7)
{
uint8_t x_90; 
lean_free_object(x_36);
lean_free_object(x_18);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_88, 0);
lean_dec(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_expr_consume_type_annotations(x_92);
lean_ctor_set(x_88, 0, x_93);
return x_88;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
lean_dec(x_88);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
lean_dec(x_89);
x_96 = lean_expr_consume_type_annotations(x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_89);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
lean_dec(x_88);
x_99 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_100 = l_Lean_indentExpr(x_99);
x_101 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_100);
lean_ctor_set(x_36, 0, x_101);
x_102 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_102);
lean_ctor_set(x_18, 0, x_36);
x_103 = l_Lean_MessageData_ofExpr(x_13);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_18);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_106, x_4, x_5, x_6, x_7, x_98);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_107;
}
}
else
{
uint8_t x_108; 
lean_free_object(x_36);
lean_free_object(x_18);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_88);
if (x_108 == 0)
{
return x_88;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_88, 0);
x_110 = lean_ctor_get(x_88, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_88);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_free_object(x_36);
lean_free_object(x_18);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_85);
if (x_112 == 0)
{
return x_85;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_85, 0);
x_114 = lean_ctor_get(x_85, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_85);
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
lean_free_object(x_36);
lean_free_object(x_18);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_81);
if (x_116 == 0)
{
return x_81;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_81, 0);
x_118 = lean_ctor_get(x_81, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_81);
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
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_52);
lean_dec(x_35);
lean_dec(x_17);
x_120 = lean_ctor_get(x_51, 1);
lean_inc(x_120);
lean_dec(x_51);
x_121 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_122 = l_Lean_indentExpr(x_121);
x_123 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_122);
lean_ctor_set(x_36, 0, x_123);
x_124 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_124);
lean_ctor_set(x_18, 0, x_36);
x_125 = l_Lean_MessageData_ofExpr(x_13);
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_18);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_128, x_4, x_5, x_6, x_7, x_120);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_129;
}
}
else
{
uint8_t x_130; 
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
x_130 = !lean_is_exclusive(x_51);
if (x_130 == 0)
{
return x_51;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_51, 0);
x_132 = lean_ctor_get(x_51, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_51);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_36, 0);
lean_inc(x_134);
lean_dec(x_36);
x_135 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_134, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 6)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_unsigned_to_nat(0u);
x_140 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_13, x_139);
x_141 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__1;
lean_inc(x_140);
x_142 = lean_mk_array(x_140, x_141);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_nat_sub(x_140, x_143);
lean_dec(x_140);
lean_inc(x_13);
x_145 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_13, x_142, x_144);
x_146 = lean_ctor_get(x_35, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_35, 2);
lean_inc(x_147);
lean_dec(x_35);
x_148 = lean_nat_add(x_146, x_147);
lean_dec(x_147);
x_149 = lean_array_get_size(x_145);
x_150 = lean_nat_dec_eq(x_148, x_149);
lean_dec(x_149);
lean_dec(x_148);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_138);
lean_dec(x_17);
x_151 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_152 = l_Lean_indentExpr(x_151);
x_153 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_155);
lean_ctor_set(x_18, 0, x_154);
x_156 = l_Lean_MessageData_ofExpr(x_13);
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_18);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_159, x_4, x_5, x_6, x_7, x_137);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_161 = lean_ctor_get(x_138, 0);
lean_inc(x_161);
lean_dec(x_138);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
lean_dec(x_161);
x_163 = l_Lean_Expr_const___override(x_162, x_17);
x_164 = l_Array_toSubarray___rarg(x_145, x_139, x_146);
x_165 = l_Array_ofSubarray___rarg(x_164);
lean_dec(x_164);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_166 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_163, x_165, x_4, x_5, x_6, x_7, x_137);
lean_dec(x_165);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
lean_inc(x_2);
x_169 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_169, 0, x_139);
lean_ctor_set(x_169, 1, x_2);
lean_ctor_set(x_169, 2, x_143);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_13);
lean_inc(x_3);
lean_inc_n(x_2, 2);
lean_inc(x_1);
x_170 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2(x_1, x_2, x_3, x_13, x_169, x_139, x_2, x_143, x_2, x_139, lean_box(0), x_167, x_4, x_5, x_6, x_7, x_168);
lean_dec(x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_173 = lean_whnf(x_171, x_4, x_5, x_6, x_7, x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
if (lean_obj_tag(x_174) == 7)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_free_object(x_18);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_176 = x_173;
} else {
 lean_dec_ref(x_173);
 x_176 = lean_box(0);
}
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
lean_dec(x_174);
x_178 = lean_expr_consume_type_annotations(x_177);
if (lean_is_scalar(x_176)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_176;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_175);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_174);
x_180 = lean_ctor_get(x_173, 1);
lean_inc(x_180);
lean_dec(x_173);
x_181 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_182 = l_Lean_indentExpr(x_181);
x_183 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_184 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
x_185 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_185);
lean_ctor_set(x_18, 0, x_184);
x_186 = l_Lean_MessageData_ofExpr(x_13);
x_187 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_187, 0, x_18);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_189 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
x_190 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_189, x_4, x_5, x_6, x_7, x_180);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_free_object(x_18);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_191 = lean_ctor_get(x_173, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_173, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_193 = x_173;
} else {
 lean_dec_ref(x_173);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_free_object(x_18);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_195 = lean_ctor_get(x_170, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_170, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_197 = x_170;
} else {
 lean_dec_ref(x_170);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_free_object(x_18);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_199 = lean_ctor_get(x_166, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_166, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_201 = x_166;
} else {
 lean_dec_ref(x_166);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_136);
lean_dec(x_35);
lean_dec(x_17);
x_203 = lean_ctor_get(x_135, 1);
lean_inc(x_203);
lean_dec(x_135);
x_204 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_205 = l_Lean_indentExpr(x_204);
x_206 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_207 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_205);
x_208 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_208);
lean_ctor_set(x_18, 0, x_207);
x_209 = l_Lean_MessageData_ofExpr(x_13);
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_18);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_212 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
x_213 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_212, x_4, x_5, x_6, x_7, x_203);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
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
x_214 = lean_ctor_get(x_135, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_135, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_216 = x_135;
} else {
 lean_dec_ref(x_135);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
}
else
{
uint8_t x_218; 
lean_dec(x_35);
lean_dec(x_17);
x_218 = !lean_is_exclusive(x_36);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_219 = lean_ctor_get(x_36, 1);
lean_dec(x_219);
x_220 = lean_ctor_get(x_36, 0);
lean_dec(x_220);
x_221 = !lean_is_exclusive(x_47);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_222 = lean_ctor_get(x_47, 1);
lean_dec(x_222);
x_223 = lean_ctor_get(x_47, 0);
lean_dec(x_223);
x_224 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_225 = l_Lean_indentExpr(x_224);
x_226 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_47, 7);
lean_ctor_set(x_47, 1, x_225);
lean_ctor_set(x_47, 0, x_226);
x_227 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_227);
lean_ctor_set(x_36, 0, x_47);
x_228 = l_Lean_MessageData_ofExpr(x_13);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_228);
lean_ctor_set(x_18, 0, x_36);
x_229 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_230 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_230, 0, x_18);
lean_ctor_set(x_230, 1, x_229);
x_231 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_230, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_47);
x_232 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_233 = l_Lean_indentExpr(x_232);
x_234 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_235 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_233);
x_236 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_236);
lean_ctor_set(x_36, 0, x_235);
x_237 = l_Lean_MessageData_ofExpr(x_13);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_237);
lean_ctor_set(x_18, 0, x_36);
x_238 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_239 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_239, 0, x_18);
lean_ctor_set(x_239, 1, x_238);
x_240 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_239, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_36);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_241 = x_47;
} else {
 lean_dec_ref(x_47);
 x_241 = lean_box(0);
}
x_242 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_243 = l_Lean_indentExpr(x_242);
x_244 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
if (lean_is_scalar(x_241)) {
 x_245 = lean_alloc_ctor(7, 2, 0);
} else {
 x_245 = x_241;
 lean_ctor_set_tag(x_245, 7);
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_243);
x_246 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_247 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = l_Lean_MessageData_ofExpr(x_13);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_248);
lean_ctor_set(x_18, 0, x_247);
x_249 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_250 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_250, 0, x_18);
lean_ctor_set(x_250, 1, x_249);
x_251 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_250, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_251;
}
}
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_34);
lean_dec(x_17);
x_252 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_253 = l_Lean_indentExpr(x_252);
x_254 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_253);
lean_ctor_set(x_18, 0, x_254);
x_255 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_256 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_256, 0, x_18);
lean_ctor_set(x_256, 1, x_255);
x_257 = l_Lean_MessageData_ofExpr(x_13);
x_258 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
x_259 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_260 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
x_261 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_260, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_261;
}
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_262 = lean_ctor_get(x_18, 0);
x_263 = lean_ctor_get(x_18, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_18);
x_264 = lean_ctor_get(x_262, 0);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_environment_find(x_264, x_16);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_17);
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
x_272 = l_Lean_MessageData_ofExpr(x_13);
x_273 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
x_274 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_275 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
x_276 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_275, x_4, x_5, x_6, x_7, x_263);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_276;
}
else
{
lean_object* x_277; 
x_277 = lean_ctor_get(x_265, 0);
lean_inc(x_277);
lean_dec(x_265);
if (lean_obj_tag(x_277) == 5)
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
lean_dec(x_277);
x_279 = lean_ctor_get(x_278, 4);
lean_inc(x_279);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_278);
lean_dec(x_17);
x_280 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_281 = l_Lean_indentExpr(x_280);
x_282 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_283 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_281);
x_284 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_285 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
x_286 = l_Lean_MessageData_ofExpr(x_13);
x_287 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
x_288 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_289 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
x_290 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_289, x_4, x_5, x_6, x_7, x_263);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_290;
}
else
{
lean_object* x_291; 
x_291 = lean_ctor_get(x_279, 1);
lean_inc(x_291);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_279, 0);
lean_inc(x_292);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_293 = x_279;
} else {
 lean_dec_ref(x_279);
 x_293 = lean_box(0);
}
x_294 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_292, x_4, x_5, x_6, x_7, x_263);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
if (lean_obj_tag(x_295) == 6)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
x_297 = lean_ctor_get(x_295, 0);
lean_inc(x_297);
lean_dec(x_295);
x_298 = lean_unsigned_to_nat(0u);
x_299 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_13, x_298);
x_300 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__1;
lean_inc(x_299);
x_301 = lean_mk_array(x_299, x_300);
x_302 = lean_unsigned_to_nat(1u);
x_303 = lean_nat_sub(x_299, x_302);
lean_dec(x_299);
lean_inc(x_13);
x_304 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_13, x_301, x_303);
x_305 = lean_ctor_get(x_278, 1);
lean_inc(x_305);
x_306 = lean_ctor_get(x_278, 2);
lean_inc(x_306);
lean_dec(x_278);
x_307 = lean_nat_add(x_305, x_306);
lean_dec(x_306);
x_308 = lean_array_get_size(x_304);
x_309 = lean_nat_dec_eq(x_307, x_308);
lean_dec(x_308);
lean_dec(x_307);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_297);
lean_dec(x_17);
x_310 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_311 = l_Lean_indentExpr(x_310);
x_312 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
if (lean_is_scalar(x_293)) {
 x_313 = lean_alloc_ctor(7, 2, 0);
} else {
 x_313 = x_293;
 lean_ctor_set_tag(x_313, 7);
}
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_311);
x_314 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_315 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
x_316 = l_Lean_MessageData_ofExpr(x_13);
x_317 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
x_318 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_319 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
x_320 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_319, x_4, x_5, x_6, x_7, x_296);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_320;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_321 = lean_ctor_get(x_297, 0);
lean_inc(x_321);
lean_dec(x_297);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
lean_dec(x_321);
x_323 = l_Lean_Expr_const___override(x_322, x_17);
x_324 = l_Array_toSubarray___rarg(x_304, x_298, x_305);
x_325 = l_Array_ofSubarray___rarg(x_324);
lean_dec(x_324);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_326 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_323, x_325, x_4, x_5, x_6, x_7, x_296);
lean_dec(x_325);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec(x_326);
lean_inc(x_2);
x_329 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_329, 0, x_298);
lean_ctor_set(x_329, 1, x_2);
lean_ctor_set(x_329, 2, x_302);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_13);
lean_inc(x_3);
lean_inc_n(x_2, 2);
lean_inc(x_1);
x_330 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2(x_1, x_2, x_3, x_13, x_329, x_298, x_2, x_302, x_2, x_298, lean_box(0), x_327, x_4, x_5, x_6, x_7, x_328);
lean_dec(x_329);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_333 = lean_whnf(x_331, x_4, x_5, x_6, x_7, x_332);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; 
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
if (lean_obj_tag(x_334) == 7)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_293);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_337 = lean_ctor_get(x_334, 1);
lean_inc(x_337);
lean_dec(x_334);
x_338 = lean_expr_consume_type_annotations(x_337);
if (lean_is_scalar(x_336)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_336;
}
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_335);
return x_339;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_334);
x_340 = lean_ctor_get(x_333, 1);
lean_inc(x_340);
lean_dec(x_333);
x_341 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_342 = l_Lean_indentExpr(x_341);
x_343 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
if (lean_is_scalar(x_293)) {
 x_344 = lean_alloc_ctor(7, 2, 0);
} else {
 x_344 = x_293;
 lean_ctor_set_tag(x_344, 7);
}
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_342);
x_345 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_346 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
x_347 = l_Lean_MessageData_ofExpr(x_13);
x_348 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
x_349 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_350 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
x_351 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_350, x_4, x_5, x_6, x_7, x_340);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_351;
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_293);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_352 = lean_ctor_get(x_333, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_333, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_354 = x_333;
} else {
 lean_dec_ref(x_333);
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
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_293);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_356 = lean_ctor_get(x_330, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_330, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_358 = x_330;
} else {
 lean_dec_ref(x_330);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_356);
lean_ctor_set(x_359, 1, x_357);
return x_359;
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_293);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_360 = lean_ctor_get(x_326, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_326, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_362 = x_326;
} else {
 lean_dec_ref(x_326);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_360);
lean_ctor_set(x_363, 1, x_361);
return x_363;
}
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_295);
lean_dec(x_278);
lean_dec(x_17);
x_364 = lean_ctor_get(x_294, 1);
lean_inc(x_364);
lean_dec(x_294);
x_365 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_366 = l_Lean_indentExpr(x_365);
x_367 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
if (lean_is_scalar(x_293)) {
 x_368 = lean_alloc_ctor(7, 2, 0);
} else {
 x_368 = x_293;
 lean_ctor_set_tag(x_368, 7);
}
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_366);
x_369 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_370 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
x_371 = l_Lean_MessageData_ofExpr(x_13);
x_372 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
x_373 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_374 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
x_375 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_374, x_4, x_5, x_6, x_7, x_364);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_375;
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_293);
lean_dec(x_278);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_376 = lean_ctor_get(x_294, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_294, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 x_378 = x_294;
} else {
 lean_dec_ref(x_294);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(1, 2, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_376);
lean_ctor_set(x_379, 1, x_377);
return x_379;
}
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_278);
lean_dec(x_17);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_380 = x_279;
} else {
 lean_dec_ref(x_279);
 x_380 = lean_box(0);
}
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_381 = x_291;
} else {
 lean_dec_ref(x_291);
 x_381 = lean_box(0);
}
x_382 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_383 = l_Lean_indentExpr(x_382);
x_384 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
if (lean_is_scalar(x_381)) {
 x_385 = lean_alloc_ctor(7, 2, 0);
} else {
 x_385 = x_381;
 lean_ctor_set_tag(x_385, 7);
}
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_383);
x_386 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
if (lean_is_scalar(x_380)) {
 x_387 = lean_alloc_ctor(7, 2, 0);
} else {
 x_387 = x_380;
 lean_ctor_set_tag(x_387, 7);
}
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
x_388 = l_Lean_MessageData_ofExpr(x_13);
x_389 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
x_390 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_391 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_390);
x_392 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_391, x_4, x_5, x_6, x_7, x_263);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_392;
}
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_277);
lean_dec(x_17);
x_393 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_394 = l_Lean_indentExpr(x_393);
x_395 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_396 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_394);
x_397 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_398 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_397);
x_399 = l_Lean_MessageData_ofExpr(x_13);
x_400 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
x_401 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_402 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_402, 0, x_400);
lean_ctor_set(x_402, 1, x_401);
x_403 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_402, x_4, x_5, x_6, x_7, x_263);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_403;
}
}
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_15);
x_404 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_405 = l_Lean_indentExpr(x_404);
x_406 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_407 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_405);
x_408 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__4;
x_409 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
x_410 = l_Lean_MessageData_ofExpr(x_13);
x_411 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
x_412 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_413 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
x_414 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_413, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_414;
}
}
else
{
uint8_t x_415; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_415 = !lean_is_exclusive(x_12);
if (x_415 == 0)
{
return x_12;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = lean_ctor_get(x_12, 0);
x_417 = lean_ctor_get(x_12, 1);
lean_inc(x_417);
lean_inc(x_416);
lean_dec(x_12);
x_418 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
return x_418;
}
}
}
else
{
uint8_t x_419; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_419 = !lean_is_exclusive(x_9);
if (x_419 == 0)
{
return x_9;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_420 = lean_ctor_get(x_9, 0);
x_421 = lean_ctor_get(x_9, 1);
lean_inc(x_421);
lean_inc(x_420);
lean_dec(x_9);
x_422 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_422, 0, x_420);
lean_ctor_set(x_422, 1, x_421);
return x_422;
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_18; 
x_18 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_18;
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
lean_dec(x_1);
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
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lambda__1), 7, 0);
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
x_7 = lean_ctor_get(x_2, 1);
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
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_expr_equal(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
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
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_expr_equal(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_usize_shift_right(x_2, x_6);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = 5;
x_22 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___closed__2;
x_23 = lean_usize_land(x_2, x_22);
x_24 = lean_usize_to_nat(x_23);
x_25 = lean_box(2);
x_26 = lean_array_get(x_25, x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_expr_equal(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_usize_shift_right(x_2, x_21);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__3(x_36, x_37, lean_box(0), x_38, x_3);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2(x_1, x_4, x_2);
return x_5;
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
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Expr_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
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
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_expr_equal(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
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
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_expr_equal(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_expr_equal(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___closed__2;
x_52 = lean_usize_land(x_2, x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_expr_equal(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__7(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5___closed__1;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__6(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__7(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5___closed__1;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__6(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Expr_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__8___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
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
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.InferType.0.Lean.Meta.checkInferTypeCache", 60, 60);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkInferTypeCache: transparency mode not default or all", 57, 57);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
x_2 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1;
x_3 = lean_unsigned_to_nat(185u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Meta_getTransparency(x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_4, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_17, x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_free_object(x_11);
lean_inc(x_4);
x_19 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = l_Lean_Expr_hasMVar(x_1);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Expr_hasMVar(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_free_object(x_19);
x_25 = lean_st_ref_take(x_4, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_26, 1);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_27, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_21);
x_36 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_35, x_1, x_21);
lean_ctor_set(x_28, 1, x_36);
x_37 = lean_st_ref_set(x_4, x_26, x_29);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_21);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_21);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_28, 0);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_28);
lean_inc(x_21);
x_44 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_43, x_1, x_21);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_27, 0, x_45);
x_46 = lean_st_ref_set(x_4, x_26, x_29);
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
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_50 = lean_ctor_get(x_27, 1);
x_51 = lean_ctor_get(x_27, 2);
x_52 = lean_ctor_get(x_27, 3);
x_53 = lean_ctor_get(x_27, 4);
x_54 = lean_ctor_get(x_27, 5);
x_55 = lean_ctor_get(x_27, 6);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_27);
x_56 = lean_ctor_get(x_28, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_28, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_58 = x_28;
} else {
 lean_dec_ref(x_28);
 x_58 = lean_box(0);
}
lean_inc(x_21);
x_59 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_57, x_1, x_21);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_50);
lean_ctor_set(x_61, 2, x_51);
lean_ctor_set(x_61, 3, x_52);
lean_ctor_set(x_61, 4, x_53);
lean_ctor_set(x_61, 5, x_54);
lean_ctor_set(x_61, 6, x_55);
lean_ctor_set(x_26, 1, x_61);
x_62 = lean_st_ref_set(x_4, x_26, x_29);
lean_dec(x_4);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_21);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_66 = lean_ctor_get(x_26, 0);
x_67 = lean_ctor_get(x_26, 2);
x_68 = lean_ctor_get(x_26, 3);
x_69 = lean_ctor_get(x_26, 4);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_26);
x_70 = lean_ctor_get(x_27, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_27, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_27, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_27, 4);
lean_inc(x_73);
x_74 = lean_ctor_get(x_27, 5);
lean_inc(x_74);
x_75 = lean_ctor_get(x_27, 6);
lean_inc(x_75);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 lean_ctor_release(x_27, 3);
 lean_ctor_release(x_27, 4);
 lean_ctor_release(x_27, 5);
 lean_ctor_release(x_27, 6);
 x_76 = x_27;
} else {
 lean_dec_ref(x_27);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_28, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_28, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_79 = x_28;
} else {
 lean_dec_ref(x_28);
 x_79 = lean_box(0);
}
lean_inc(x_21);
x_80 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_78, x_1, x_21);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_80);
if (lean_is_scalar(x_76)) {
 x_82 = lean_alloc_ctor(0, 7, 0);
} else {
 x_82 = x_76;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_70);
lean_ctor_set(x_82, 2, x_71);
lean_ctor_set(x_82, 3, x_72);
lean_ctor_set(x_82, 4, x_73);
lean_ctor_set(x_82, 5, x_74);
lean_ctor_set(x_82, 6, x_75);
x_83 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_83, 0, x_66);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_67);
lean_ctor_set(x_83, 3, x_68);
lean_ctor_set(x_83, 4, x_69);
x_84 = lean_st_ref_set(x_4, x_83, x_29);
lean_dec(x_4);
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
lean_ctor_set(x_87, 0, x_21);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_19;
}
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_19;
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_19, 0);
x_89 = lean_ctor_get(x_19, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_19);
x_90 = l_Lean_Expr_hasMVar(x_1);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = l_Lean_Expr_hasMVar(x_88);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_92 = lean_st_ref_take(x_4, x_89);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = lean_ctor_get(x_93, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_93, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_93, 3);
lean_inc(x_99);
x_100 = lean_ctor_get(x_93, 4);
lean_inc(x_100);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 lean_ctor_release(x_93, 2);
 lean_ctor_release(x_93, 3);
 lean_ctor_release(x_93, 4);
 x_101 = x_93;
} else {
 lean_dec_ref(x_93);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_94, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_94, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_94, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_94, 4);
lean_inc(x_105);
x_106 = lean_ctor_get(x_94, 5);
lean_inc(x_106);
x_107 = lean_ctor_get(x_94, 6);
lean_inc(x_107);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 lean_ctor_release(x_94, 2);
 lean_ctor_release(x_94, 3);
 lean_ctor_release(x_94, 4);
 lean_ctor_release(x_94, 5);
 lean_ctor_release(x_94, 6);
 x_108 = x_94;
} else {
 lean_dec_ref(x_94);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_95, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_95, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_111 = x_95;
} else {
 lean_dec_ref(x_95);
 x_111 = lean_box(0);
}
lean_inc(x_88);
x_112 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_110, x_1, x_88);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_109);
lean_ctor_set(x_113, 1, x_112);
if (lean_is_scalar(x_108)) {
 x_114 = lean_alloc_ctor(0, 7, 0);
} else {
 x_114 = x_108;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_102);
lean_ctor_set(x_114, 2, x_103);
lean_ctor_set(x_114, 3, x_104);
lean_ctor_set(x_114, 4, x_105);
lean_ctor_set(x_114, 5, x_106);
lean_ctor_set(x_114, 6, x_107);
if (lean_is_scalar(x_101)) {
 x_115 = lean_alloc_ctor(0, 5, 0);
} else {
 x_115 = x_101;
}
lean_ctor_set(x_115, 0, x_97);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_115, 2, x_98);
lean_ctor_set(x_115, 3, x_99);
lean_ctor_set(x_115, 4, x_100);
x_116 = lean_st_ref_set(x_4, x_115, x_96);
lean_dec(x_4);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_88);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
else
{
lean_object* x_120; 
lean_dec(x_4);
lean_dec(x_1);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_88);
lean_ctor_set(x_120, 1, x_89);
return x_120;
}
}
else
{
lean_object* x_121; 
lean_dec(x_4);
lean_dec(x_1);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_88);
lean_ctor_set(x_121, 1, x_89);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_4);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_19);
if (x_122 == 0)
{
return x_19;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_19, 0);
x_124 = lean_ctor_get(x_19, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_19);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
lean_object* x_126; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = lean_ctor_get(x_18, 0);
lean_inc(x_126);
lean_dec(x_18);
lean_ctor_set(x_11, 0, x_126);
return x_11;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_127 = lean_ctor_get(x_11, 0);
x_128 = lean_ctor_get(x_11, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_11);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_131, x_1);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
lean_inc(x_4);
x_133 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_128);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
x_137 = l_Lean_Expr_hasMVar(x_1);
if (x_137 == 0)
{
uint8_t x_138; 
x_138 = l_Lean_Expr_hasMVar(x_134);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_136);
x_139 = lean_st_ref_take(x_4, x_135);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
lean_dec(x_139);
x_144 = lean_ctor_get(x_140, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_140, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_140, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_140, 4);
lean_inc(x_147);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 lean_ctor_release(x_140, 2);
 lean_ctor_release(x_140, 3);
 lean_ctor_release(x_140, 4);
 x_148 = x_140;
} else {
 lean_dec_ref(x_140);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_141, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_141, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_141, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_141, 4);
lean_inc(x_152);
x_153 = lean_ctor_get(x_141, 5);
lean_inc(x_153);
x_154 = lean_ctor_get(x_141, 6);
lean_inc(x_154);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 lean_ctor_release(x_141, 2);
 lean_ctor_release(x_141, 3);
 lean_ctor_release(x_141, 4);
 lean_ctor_release(x_141, 5);
 lean_ctor_release(x_141, 6);
 x_155 = x_141;
} else {
 lean_dec_ref(x_141);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_142, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_142, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_158 = x_142;
} else {
 lean_dec_ref(x_142);
 x_158 = lean_box(0);
}
lean_inc(x_134);
x_159 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_157, x_1, x_134);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_156);
lean_ctor_set(x_160, 1, x_159);
if (lean_is_scalar(x_155)) {
 x_161 = lean_alloc_ctor(0, 7, 0);
} else {
 x_161 = x_155;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_149);
lean_ctor_set(x_161, 2, x_150);
lean_ctor_set(x_161, 3, x_151);
lean_ctor_set(x_161, 4, x_152);
lean_ctor_set(x_161, 5, x_153);
lean_ctor_set(x_161, 6, x_154);
if (lean_is_scalar(x_148)) {
 x_162 = lean_alloc_ctor(0, 5, 0);
} else {
 x_162 = x_148;
}
lean_ctor_set(x_162, 0, x_144);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set(x_162, 2, x_145);
lean_ctor_set(x_162, 3, x_146);
lean_ctor_set(x_162, 4, x_147);
x_163 = lean_st_ref_set(x_4, x_162, x_143);
lean_dec(x_4);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_165 = x_163;
} else {
 lean_dec_ref(x_163);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_134);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
else
{
lean_object* x_167; 
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_136)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_136;
}
lean_ctor_set(x_167, 0, x_134);
lean_ctor_set(x_167, 1, x_135);
return x_167;
}
}
else
{
lean_object* x_168; 
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_136)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_136;
}
lean_ctor_set(x_168, 0, x_134);
lean_ctor_set(x_168, 1, x_135);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_4);
lean_dec(x_1);
x_169 = lean_ctor_get(x_133, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_133, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_171 = x_133;
} else {
 lean_dec_ref(x_133);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_173 = lean_ctor_get(x_132, 0);
lean_inc(x_173);
lean_dec(x_132);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_128);
return x_174;
}
}
}
case 1:
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_175 = lean_ctor_get(x_8, 1);
lean_inc(x_175);
lean_dec(x_8);
x_176 = lean_st_ref_get(x_4, x_175);
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_178 = lean_ctor_get(x_176, 0);
x_179 = lean_ctor_get(x_176, 1);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec(x_180);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec(x_181);
x_183 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_182, x_1);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; 
lean_free_object(x_176);
lean_inc(x_4);
x_184 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_179);
if (lean_obj_tag(x_184) == 0)
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_186 = lean_ctor_get(x_184, 0);
x_187 = lean_ctor_get(x_184, 1);
x_188 = l_Lean_Expr_hasMVar(x_1);
if (x_188 == 0)
{
uint8_t x_189; 
x_189 = l_Lean_Expr_hasMVar(x_186);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
lean_free_object(x_184);
x_190 = lean_st_ref_take(x_4, x_187);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_190, 1);
lean_inc(x_194);
lean_dec(x_190);
x_195 = !lean_is_exclusive(x_191);
if (x_195 == 0)
{
lean_object* x_196; uint8_t x_197; 
x_196 = lean_ctor_get(x_191, 1);
lean_dec(x_196);
x_197 = !lean_is_exclusive(x_192);
if (x_197 == 0)
{
lean_object* x_198; uint8_t x_199; 
x_198 = lean_ctor_get(x_192, 0);
lean_dec(x_198);
x_199 = !lean_is_exclusive(x_193);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_200 = lean_ctor_get(x_193, 0);
lean_inc(x_186);
x_201 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_200, x_1, x_186);
lean_ctor_set(x_193, 0, x_201);
x_202 = lean_st_ref_set(x_4, x_191, x_194);
lean_dec(x_4);
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_202, 0);
lean_dec(x_204);
lean_ctor_set(x_202, 0, x_186);
return x_202;
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_dec(x_202);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_186);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_207 = lean_ctor_get(x_193, 0);
x_208 = lean_ctor_get(x_193, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_193);
lean_inc(x_186);
x_209 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_207, x_1, x_186);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
lean_ctor_set(x_192, 0, x_210);
x_211 = lean_st_ref_set(x_4, x_191, x_194);
lean_dec(x_4);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_213 = x_211;
} else {
 lean_dec_ref(x_211);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_186);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_215 = lean_ctor_get(x_192, 1);
x_216 = lean_ctor_get(x_192, 2);
x_217 = lean_ctor_get(x_192, 3);
x_218 = lean_ctor_get(x_192, 4);
x_219 = lean_ctor_get(x_192, 5);
x_220 = lean_ctor_get(x_192, 6);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_192);
x_221 = lean_ctor_get(x_193, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_193, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_223 = x_193;
} else {
 lean_dec_ref(x_193);
 x_223 = lean_box(0);
}
lean_inc(x_186);
x_224 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_221, x_1, x_186);
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_223;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_222);
x_226 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_215);
lean_ctor_set(x_226, 2, x_216);
lean_ctor_set(x_226, 3, x_217);
lean_ctor_set(x_226, 4, x_218);
lean_ctor_set(x_226, 5, x_219);
lean_ctor_set(x_226, 6, x_220);
lean_ctor_set(x_191, 1, x_226);
x_227 = lean_st_ref_set(x_4, x_191, x_194);
lean_dec(x_4);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_229 = x_227;
} else {
 lean_dec_ref(x_227);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_186);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_231 = lean_ctor_get(x_191, 0);
x_232 = lean_ctor_get(x_191, 2);
x_233 = lean_ctor_get(x_191, 3);
x_234 = lean_ctor_get(x_191, 4);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_191);
x_235 = lean_ctor_get(x_192, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_192, 2);
lean_inc(x_236);
x_237 = lean_ctor_get(x_192, 3);
lean_inc(x_237);
x_238 = lean_ctor_get(x_192, 4);
lean_inc(x_238);
x_239 = lean_ctor_get(x_192, 5);
lean_inc(x_239);
x_240 = lean_ctor_get(x_192, 6);
lean_inc(x_240);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 lean_ctor_release(x_192, 2);
 lean_ctor_release(x_192, 3);
 lean_ctor_release(x_192, 4);
 lean_ctor_release(x_192, 5);
 lean_ctor_release(x_192, 6);
 x_241 = x_192;
} else {
 lean_dec_ref(x_192);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_193, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_193, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_244 = x_193;
} else {
 lean_dec_ref(x_193);
 x_244 = lean_box(0);
}
lean_inc(x_186);
x_245 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_242, x_1, x_186);
if (lean_is_scalar(x_244)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_244;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_243);
if (lean_is_scalar(x_241)) {
 x_247 = lean_alloc_ctor(0, 7, 0);
} else {
 x_247 = x_241;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_235);
lean_ctor_set(x_247, 2, x_236);
lean_ctor_set(x_247, 3, x_237);
lean_ctor_set(x_247, 4, x_238);
lean_ctor_set(x_247, 5, x_239);
lean_ctor_set(x_247, 6, x_240);
x_248 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_248, 0, x_231);
lean_ctor_set(x_248, 1, x_247);
lean_ctor_set(x_248, 2, x_232);
lean_ctor_set(x_248, 3, x_233);
lean_ctor_set(x_248, 4, x_234);
x_249 = lean_st_ref_set(x_4, x_248, x_194);
lean_dec(x_4);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_251 = x_249;
} else {
 lean_dec_ref(x_249);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_186);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_184;
}
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_184;
}
}
else
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_253 = lean_ctor_get(x_184, 0);
x_254 = lean_ctor_get(x_184, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_184);
x_255 = l_Lean_Expr_hasMVar(x_1);
if (x_255 == 0)
{
uint8_t x_256; 
x_256 = l_Lean_Expr_hasMVar(x_253);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_257 = lean_st_ref_take(x_4, x_254);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_257, 1);
lean_inc(x_261);
lean_dec(x_257);
x_262 = lean_ctor_get(x_258, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_258, 2);
lean_inc(x_263);
x_264 = lean_ctor_get(x_258, 3);
lean_inc(x_264);
x_265 = lean_ctor_get(x_258, 4);
lean_inc(x_265);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 lean_ctor_release(x_258, 2);
 lean_ctor_release(x_258, 3);
 lean_ctor_release(x_258, 4);
 x_266 = x_258;
} else {
 lean_dec_ref(x_258);
 x_266 = lean_box(0);
}
x_267 = lean_ctor_get(x_259, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_259, 2);
lean_inc(x_268);
x_269 = lean_ctor_get(x_259, 3);
lean_inc(x_269);
x_270 = lean_ctor_get(x_259, 4);
lean_inc(x_270);
x_271 = lean_ctor_get(x_259, 5);
lean_inc(x_271);
x_272 = lean_ctor_get(x_259, 6);
lean_inc(x_272);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 lean_ctor_release(x_259, 2);
 lean_ctor_release(x_259, 3);
 lean_ctor_release(x_259, 4);
 lean_ctor_release(x_259, 5);
 lean_ctor_release(x_259, 6);
 x_273 = x_259;
} else {
 lean_dec_ref(x_259);
 x_273 = lean_box(0);
}
x_274 = lean_ctor_get(x_260, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_260, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_276 = x_260;
} else {
 lean_dec_ref(x_260);
 x_276 = lean_box(0);
}
lean_inc(x_253);
x_277 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_274, x_1, x_253);
if (lean_is_scalar(x_276)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_276;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_275);
if (lean_is_scalar(x_273)) {
 x_279 = lean_alloc_ctor(0, 7, 0);
} else {
 x_279 = x_273;
}
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_267);
lean_ctor_set(x_279, 2, x_268);
lean_ctor_set(x_279, 3, x_269);
lean_ctor_set(x_279, 4, x_270);
lean_ctor_set(x_279, 5, x_271);
lean_ctor_set(x_279, 6, x_272);
if (lean_is_scalar(x_266)) {
 x_280 = lean_alloc_ctor(0, 5, 0);
} else {
 x_280 = x_266;
}
lean_ctor_set(x_280, 0, x_262);
lean_ctor_set(x_280, 1, x_279);
lean_ctor_set(x_280, 2, x_263);
lean_ctor_set(x_280, 3, x_264);
lean_ctor_set(x_280, 4, x_265);
x_281 = lean_st_ref_set(x_4, x_280, x_261);
lean_dec(x_4);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_283 = x_281;
} else {
 lean_dec_ref(x_281);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_253);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
else
{
lean_object* x_285; 
lean_dec(x_4);
lean_dec(x_1);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_253);
lean_ctor_set(x_285, 1, x_254);
return x_285;
}
}
else
{
lean_object* x_286; 
lean_dec(x_4);
lean_dec(x_1);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_253);
lean_ctor_set(x_286, 1, x_254);
return x_286;
}
}
}
else
{
uint8_t x_287; 
lean_dec(x_4);
lean_dec(x_1);
x_287 = !lean_is_exclusive(x_184);
if (x_287 == 0)
{
return x_184;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_184, 0);
x_289 = lean_ctor_get(x_184, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_184);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
return x_290;
}
}
}
else
{
lean_object* x_291; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_291 = lean_ctor_get(x_183, 0);
lean_inc(x_291);
lean_dec(x_183);
lean_ctor_set(x_176, 0, x_291);
return x_176;
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_292 = lean_ctor_get(x_176, 0);
x_293 = lean_ctor_get(x_176, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_176);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
lean_dec(x_294);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
lean_dec(x_295);
x_297 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_296, x_1);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; 
lean_inc(x_4);
x_298 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_293);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_301 = x_298;
} else {
 lean_dec_ref(x_298);
 x_301 = lean_box(0);
}
x_302 = l_Lean_Expr_hasMVar(x_1);
if (x_302 == 0)
{
uint8_t x_303; 
x_303 = l_Lean_Expr_hasMVar(x_299);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_301);
x_304 = lean_st_ref_take(x_4, x_300);
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_305, 1);
lean_inc(x_306);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_304, 1);
lean_inc(x_308);
lean_dec(x_304);
x_309 = lean_ctor_get(x_305, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_305, 2);
lean_inc(x_310);
x_311 = lean_ctor_get(x_305, 3);
lean_inc(x_311);
x_312 = lean_ctor_get(x_305, 4);
lean_inc(x_312);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 lean_ctor_release(x_305, 2);
 lean_ctor_release(x_305, 3);
 lean_ctor_release(x_305, 4);
 x_313 = x_305;
} else {
 lean_dec_ref(x_305);
 x_313 = lean_box(0);
}
x_314 = lean_ctor_get(x_306, 1);
lean_inc(x_314);
x_315 = lean_ctor_get(x_306, 2);
lean_inc(x_315);
x_316 = lean_ctor_get(x_306, 3);
lean_inc(x_316);
x_317 = lean_ctor_get(x_306, 4);
lean_inc(x_317);
x_318 = lean_ctor_get(x_306, 5);
lean_inc(x_318);
x_319 = lean_ctor_get(x_306, 6);
lean_inc(x_319);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 lean_ctor_release(x_306, 2);
 lean_ctor_release(x_306, 3);
 lean_ctor_release(x_306, 4);
 lean_ctor_release(x_306, 5);
 lean_ctor_release(x_306, 6);
 x_320 = x_306;
} else {
 lean_dec_ref(x_306);
 x_320 = lean_box(0);
}
x_321 = lean_ctor_get(x_307, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_307, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_323 = x_307;
} else {
 lean_dec_ref(x_307);
 x_323 = lean_box(0);
}
lean_inc(x_299);
x_324 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_321, x_1, x_299);
if (lean_is_scalar(x_323)) {
 x_325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_325 = x_323;
}
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_322);
if (lean_is_scalar(x_320)) {
 x_326 = lean_alloc_ctor(0, 7, 0);
} else {
 x_326 = x_320;
}
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_314);
lean_ctor_set(x_326, 2, x_315);
lean_ctor_set(x_326, 3, x_316);
lean_ctor_set(x_326, 4, x_317);
lean_ctor_set(x_326, 5, x_318);
lean_ctor_set(x_326, 6, x_319);
if (lean_is_scalar(x_313)) {
 x_327 = lean_alloc_ctor(0, 5, 0);
} else {
 x_327 = x_313;
}
lean_ctor_set(x_327, 0, x_309);
lean_ctor_set(x_327, 1, x_326);
lean_ctor_set(x_327, 2, x_310);
lean_ctor_set(x_327, 3, x_311);
lean_ctor_set(x_327, 4, x_312);
x_328 = lean_st_ref_set(x_4, x_327, x_308);
lean_dec(x_4);
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_330 = x_328;
} else {
 lean_dec_ref(x_328);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(0, 2, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_299);
lean_ctor_set(x_331, 1, x_329);
return x_331;
}
else
{
lean_object* x_332; 
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_301)) {
 x_332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_332 = x_301;
}
lean_ctor_set(x_332, 0, x_299);
lean_ctor_set(x_332, 1, x_300);
return x_332;
}
}
else
{
lean_object* x_333; 
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_301)) {
 x_333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_333 = x_301;
}
lean_ctor_set(x_333, 0, x_299);
lean_ctor_set(x_333, 1, x_300);
return x_333;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_4);
lean_dec(x_1);
x_334 = lean_ctor_get(x_298, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_298, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_336 = x_298;
} else {
 lean_dec_ref(x_298);
 x_336 = lean_box(0);
}
if (lean_is_scalar(x_336)) {
 x_337 = lean_alloc_ctor(1, 2, 0);
} else {
 x_337 = x_336;
}
lean_ctor_set(x_337, 0, x_334);
lean_ctor_set(x_337, 1, x_335);
return x_337;
}
}
else
{
lean_object* x_338; lean_object* x_339; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_338 = lean_ctor_get(x_297, 0);
lean_inc(x_338);
lean_dec(x_297);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_293);
return x_339;
}
}
}
default: 
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_340 = lean_ctor_get(x_8, 1);
lean_inc(x_340);
lean_dec(x_8);
x_341 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3;
x_342 = l_panic___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__8(x_341, x_3, x_4, x_5, x_6, x_340);
return x_342;
}
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = l_Lean_Meta_getTransparency(x_2, x_3, x_4, x_5, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
switch (lean_obj_tag(x_29)) {
case 0:
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_ref_get(x_3, x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_37, x_1);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_free_object(x_31);
x_39 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_27, x_23, x_2, x_3, x_4, x_5, x_34);
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
x_43 = l_Lean_Expr_hasMVar(x_1);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = l_Lean_Expr_hasMVar(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_free_object(x_39);
x_45 = lean_st_ref_take(x_3, x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_46, 1);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_47, 0);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_41);
x_56 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_55, x_1, x_41);
lean_ctor_set(x_48, 1, x_56);
x_57 = lean_st_ref_set(x_3, x_46, x_49);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_41);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_48, 0);
x_63 = lean_ctor_get(x_48, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_48);
lean_inc(x_41);
x_64 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_63, x_1, x_41);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_47, 0, x_65);
x_66 = lean_st_ref_set(x_3, x_46, x_49);
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
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_70 = lean_ctor_get(x_47, 1);
x_71 = lean_ctor_get(x_47, 2);
x_72 = lean_ctor_get(x_47, 3);
x_73 = lean_ctor_get(x_47, 4);
x_74 = lean_ctor_get(x_47, 5);
x_75 = lean_ctor_get(x_47, 6);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_47);
x_76 = lean_ctor_get(x_48, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_48, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_78 = x_48;
} else {
 lean_dec_ref(x_48);
 x_78 = lean_box(0);
}
lean_inc(x_41);
x_79 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_77, x_1, x_41);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_70);
lean_ctor_set(x_81, 2, x_71);
lean_ctor_set(x_81, 3, x_72);
lean_ctor_set(x_81, 4, x_73);
lean_ctor_set(x_81, 5, x_74);
lean_ctor_set(x_81, 6, x_75);
lean_ctor_set(x_46, 1, x_81);
x_82 = lean_st_ref_set(x_3, x_46, x_49);
lean_dec(x_3);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_41);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_86 = lean_ctor_get(x_46, 0);
x_87 = lean_ctor_get(x_46, 2);
x_88 = lean_ctor_get(x_46, 3);
x_89 = lean_ctor_get(x_46, 4);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_46);
x_90 = lean_ctor_get(x_47, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_47, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_47, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_47, 4);
lean_inc(x_93);
x_94 = lean_ctor_get(x_47, 5);
lean_inc(x_94);
x_95 = lean_ctor_get(x_47, 6);
lean_inc(x_95);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 lean_ctor_release(x_47, 4);
 lean_ctor_release(x_47, 5);
 lean_ctor_release(x_47, 6);
 x_96 = x_47;
} else {
 lean_dec_ref(x_47);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_48, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_48, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_99 = x_48;
} else {
 lean_dec_ref(x_48);
 x_99 = lean_box(0);
}
lean_inc(x_41);
x_100 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_98, x_1, x_41);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_100);
if (lean_is_scalar(x_96)) {
 x_102 = lean_alloc_ctor(0, 7, 0);
} else {
 x_102 = x_96;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_90);
lean_ctor_set(x_102, 2, x_91);
lean_ctor_set(x_102, 3, x_92);
lean_ctor_set(x_102, 4, x_93);
lean_ctor_set(x_102, 5, x_94);
lean_ctor_set(x_102, 6, x_95);
x_103 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_103, 0, x_86);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_103, 2, x_87);
lean_ctor_set(x_103, 3, x_88);
lean_ctor_set(x_103, 4, x_89);
x_104 = lean_st_ref_set(x_3, x_103, x_49);
lean_dec(x_3);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_41);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_39;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_39;
}
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_39, 0);
x_109 = lean_ctor_get(x_39, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_39);
x_110 = l_Lean_Expr_hasMVar(x_1);
if (x_110 == 0)
{
uint8_t x_111; 
x_111 = l_Lean_Expr_hasMVar(x_108);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_112 = lean_st_ref_take(x_3, x_109);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
lean_dec(x_112);
x_117 = lean_ctor_get(x_113, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_113, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_113, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_113, 4);
lean_inc(x_120);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 lean_ctor_release(x_113, 4);
 x_121 = x_113;
} else {
 lean_dec_ref(x_113);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_114, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_114, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_114, 3);
lean_inc(x_124);
x_125 = lean_ctor_get(x_114, 4);
lean_inc(x_125);
x_126 = lean_ctor_get(x_114, 5);
lean_inc(x_126);
x_127 = lean_ctor_get(x_114, 6);
lean_inc(x_127);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 lean_ctor_release(x_114, 3);
 lean_ctor_release(x_114, 4);
 lean_ctor_release(x_114, 5);
 lean_ctor_release(x_114, 6);
 x_128 = x_114;
} else {
 lean_dec_ref(x_114);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_115, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_115, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_131 = x_115;
} else {
 lean_dec_ref(x_115);
 x_131 = lean_box(0);
}
lean_inc(x_108);
x_132 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_130, x_1, x_108);
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_129);
lean_ctor_set(x_133, 1, x_132);
if (lean_is_scalar(x_128)) {
 x_134 = lean_alloc_ctor(0, 7, 0);
} else {
 x_134 = x_128;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_122);
lean_ctor_set(x_134, 2, x_123);
lean_ctor_set(x_134, 3, x_124);
lean_ctor_set(x_134, 4, x_125);
lean_ctor_set(x_134, 5, x_126);
lean_ctor_set(x_134, 6, x_127);
if (lean_is_scalar(x_121)) {
 x_135 = lean_alloc_ctor(0, 5, 0);
} else {
 x_135 = x_121;
}
lean_ctor_set(x_135, 0, x_117);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set(x_135, 2, x_118);
lean_ctor_set(x_135, 3, x_119);
lean_ctor_set(x_135, 4, x_120);
x_136 = lean_st_ref_set(x_3, x_135, x_116);
lean_dec(x_3);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_108);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
else
{
lean_object* x_140; 
lean_dec(x_3);
lean_dec(x_1);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_108);
lean_ctor_set(x_140, 1, x_109);
return x_140;
}
}
else
{
lean_object* x_141; 
lean_dec(x_3);
lean_dec(x_1);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_108);
lean_ctor_set(x_141, 1, x_109);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_3);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_39);
if (x_142 == 0)
{
return x_39;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_39, 0);
x_144 = lean_ctor_get(x_39, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_39);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
lean_object* x_146; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_146 = lean_ctor_get(x_38, 0);
lean_inc(x_146);
lean_dec(x_38);
lean_ctor_set(x_31, 0, x_146);
return x_31;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_147 = lean_ctor_get(x_31, 0);
x_148 = lean_ctor_get(x_31, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_31);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_152 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_151, x_1);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; 
x_153 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_27, x_23, x_2, x_3, x_4, x_5, x_148);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
x_157 = l_Lean_Expr_hasMVar(x_1);
if (x_157 == 0)
{
uint8_t x_158; 
x_158 = l_Lean_Expr_hasMVar(x_154);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_156);
x_159 = lean_st_ref_take(x_3, x_155);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_159, 1);
lean_inc(x_163);
lean_dec(x_159);
x_164 = lean_ctor_get(x_160, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_160, 3);
lean_inc(x_166);
x_167 = lean_ctor_get(x_160, 4);
lean_inc(x_167);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 x_168 = x_160;
} else {
 lean_dec_ref(x_160);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_161, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_161, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_161, 3);
lean_inc(x_171);
x_172 = lean_ctor_get(x_161, 4);
lean_inc(x_172);
x_173 = lean_ctor_get(x_161, 5);
lean_inc(x_173);
x_174 = lean_ctor_get(x_161, 6);
lean_inc(x_174);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 lean_ctor_release(x_161, 2);
 lean_ctor_release(x_161, 3);
 lean_ctor_release(x_161, 4);
 lean_ctor_release(x_161, 5);
 lean_ctor_release(x_161, 6);
 x_175 = x_161;
} else {
 lean_dec_ref(x_161);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_162, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_162, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_178 = x_162;
} else {
 lean_dec_ref(x_162);
 x_178 = lean_box(0);
}
lean_inc(x_154);
x_179 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_177, x_1, x_154);
if (lean_is_scalar(x_178)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_178;
}
lean_ctor_set(x_180, 0, x_176);
lean_ctor_set(x_180, 1, x_179);
if (lean_is_scalar(x_175)) {
 x_181 = lean_alloc_ctor(0, 7, 0);
} else {
 x_181 = x_175;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_169);
lean_ctor_set(x_181, 2, x_170);
lean_ctor_set(x_181, 3, x_171);
lean_ctor_set(x_181, 4, x_172);
lean_ctor_set(x_181, 5, x_173);
lean_ctor_set(x_181, 6, x_174);
if (lean_is_scalar(x_168)) {
 x_182 = lean_alloc_ctor(0, 5, 0);
} else {
 x_182 = x_168;
}
lean_ctor_set(x_182, 0, x_164);
lean_ctor_set(x_182, 1, x_181);
lean_ctor_set(x_182, 2, x_165);
lean_ctor_set(x_182, 3, x_166);
lean_ctor_set(x_182, 4, x_167);
x_183 = lean_st_ref_set(x_3, x_182, x_163);
lean_dec(x_3);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_185 = x_183;
} else {
 lean_dec_ref(x_183);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_154);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
else
{
lean_object* x_187; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_156)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_156;
}
lean_ctor_set(x_187, 0, x_154);
lean_ctor_set(x_187, 1, x_155);
return x_187;
}
}
else
{
lean_object* x_188; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_156)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_156;
}
lean_ctor_set(x_188, 0, x_154);
lean_ctor_set(x_188, 1, x_155);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_3);
lean_dec(x_1);
x_189 = lean_ctor_get(x_153, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_153, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_191 = x_153;
} else {
 lean_dec_ref(x_153);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
else
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_193 = lean_ctor_get(x_152, 0);
lean_inc(x_193);
lean_dec(x_152);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_148);
return x_194;
}
}
}
case 1:
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_195 = lean_ctor_get(x_28, 1);
lean_inc(x_195);
lean_dec(x_28);
x_196 = lean_st_ref_get(x_3, x_195);
x_197 = !lean_is_exclusive(x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_198 = lean_ctor_get(x_196, 0);
x_199 = lean_ctor_get(x_196, 1);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec(x_200);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
lean_dec(x_201);
x_203 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_202, x_1);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; 
lean_free_object(x_196);
x_204 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_27, x_23, x_2, x_3, x_4, x_5, x_199);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_obj_tag(x_204) == 0)
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_206 = lean_ctor_get(x_204, 0);
x_207 = lean_ctor_get(x_204, 1);
x_208 = l_Lean_Expr_hasMVar(x_1);
if (x_208 == 0)
{
uint8_t x_209; 
x_209 = l_Lean_Expr_hasMVar(x_206);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
lean_free_object(x_204);
x_210 = lean_st_ref_take(x_3, x_207);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_210, 1);
lean_inc(x_214);
lean_dec(x_210);
x_215 = !lean_is_exclusive(x_211);
if (x_215 == 0)
{
lean_object* x_216; uint8_t x_217; 
x_216 = lean_ctor_get(x_211, 1);
lean_dec(x_216);
x_217 = !lean_is_exclusive(x_212);
if (x_217 == 0)
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_ctor_get(x_212, 0);
lean_dec(x_218);
x_219 = !lean_is_exclusive(x_213);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_220 = lean_ctor_get(x_213, 0);
lean_inc(x_206);
x_221 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_220, x_1, x_206);
lean_ctor_set(x_213, 0, x_221);
x_222 = lean_st_ref_set(x_3, x_211, x_214);
lean_dec(x_3);
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_222, 0);
lean_dec(x_224);
lean_ctor_set(x_222, 0, x_206);
return x_222;
}
else
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
lean_dec(x_222);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_206);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_227 = lean_ctor_get(x_213, 0);
x_228 = lean_ctor_get(x_213, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_213);
lean_inc(x_206);
x_229 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_227, x_1, x_206);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
lean_ctor_set(x_212, 0, x_230);
x_231 = lean_st_ref_set(x_3, x_211, x_214);
lean_dec(x_3);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_233 = x_231;
} else {
 lean_dec_ref(x_231);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_206);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_235 = lean_ctor_get(x_212, 1);
x_236 = lean_ctor_get(x_212, 2);
x_237 = lean_ctor_get(x_212, 3);
x_238 = lean_ctor_get(x_212, 4);
x_239 = lean_ctor_get(x_212, 5);
x_240 = lean_ctor_get(x_212, 6);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_212);
x_241 = lean_ctor_get(x_213, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_213, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_243 = x_213;
} else {
 lean_dec_ref(x_213);
 x_243 = lean_box(0);
}
lean_inc(x_206);
x_244 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_241, x_1, x_206);
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_242);
x_246 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_235);
lean_ctor_set(x_246, 2, x_236);
lean_ctor_set(x_246, 3, x_237);
lean_ctor_set(x_246, 4, x_238);
lean_ctor_set(x_246, 5, x_239);
lean_ctor_set(x_246, 6, x_240);
lean_ctor_set(x_211, 1, x_246);
x_247 = lean_st_ref_set(x_3, x_211, x_214);
lean_dec(x_3);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_249 = x_247;
} else {
 lean_dec_ref(x_247);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_206);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_251 = lean_ctor_get(x_211, 0);
x_252 = lean_ctor_get(x_211, 2);
x_253 = lean_ctor_get(x_211, 3);
x_254 = lean_ctor_get(x_211, 4);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_211);
x_255 = lean_ctor_get(x_212, 1);
lean_inc(x_255);
x_256 = lean_ctor_get(x_212, 2);
lean_inc(x_256);
x_257 = lean_ctor_get(x_212, 3);
lean_inc(x_257);
x_258 = lean_ctor_get(x_212, 4);
lean_inc(x_258);
x_259 = lean_ctor_get(x_212, 5);
lean_inc(x_259);
x_260 = lean_ctor_get(x_212, 6);
lean_inc(x_260);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 lean_ctor_release(x_212, 2);
 lean_ctor_release(x_212, 3);
 lean_ctor_release(x_212, 4);
 lean_ctor_release(x_212, 5);
 lean_ctor_release(x_212, 6);
 x_261 = x_212;
} else {
 lean_dec_ref(x_212);
 x_261 = lean_box(0);
}
x_262 = lean_ctor_get(x_213, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_213, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_264 = x_213;
} else {
 lean_dec_ref(x_213);
 x_264 = lean_box(0);
}
lean_inc(x_206);
x_265 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_262, x_1, x_206);
if (lean_is_scalar(x_264)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_264;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_263);
if (lean_is_scalar(x_261)) {
 x_267 = lean_alloc_ctor(0, 7, 0);
} else {
 x_267 = x_261;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_255);
lean_ctor_set(x_267, 2, x_256);
lean_ctor_set(x_267, 3, x_257);
lean_ctor_set(x_267, 4, x_258);
lean_ctor_set(x_267, 5, x_259);
lean_ctor_set(x_267, 6, x_260);
x_268 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_268, 0, x_251);
lean_ctor_set(x_268, 1, x_267);
lean_ctor_set(x_268, 2, x_252);
lean_ctor_set(x_268, 3, x_253);
lean_ctor_set(x_268, 4, x_254);
x_269 = lean_st_ref_set(x_3, x_268, x_214);
lean_dec(x_3);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_271 = x_269;
} else {
 lean_dec_ref(x_269);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_206);
lean_ctor_set(x_272, 1, x_270);
return x_272;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_204;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_204;
}
}
else
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_273 = lean_ctor_get(x_204, 0);
x_274 = lean_ctor_get(x_204, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_204);
x_275 = l_Lean_Expr_hasMVar(x_1);
if (x_275 == 0)
{
uint8_t x_276; 
x_276 = l_Lean_Expr_hasMVar(x_273);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_277 = lean_st_ref_take(x_3, x_274);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_277, 1);
lean_inc(x_281);
lean_dec(x_277);
x_282 = lean_ctor_get(x_278, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_278, 2);
lean_inc(x_283);
x_284 = lean_ctor_get(x_278, 3);
lean_inc(x_284);
x_285 = lean_ctor_get(x_278, 4);
lean_inc(x_285);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 lean_ctor_release(x_278, 2);
 lean_ctor_release(x_278, 3);
 lean_ctor_release(x_278, 4);
 x_286 = x_278;
} else {
 lean_dec_ref(x_278);
 x_286 = lean_box(0);
}
x_287 = lean_ctor_get(x_279, 1);
lean_inc(x_287);
x_288 = lean_ctor_get(x_279, 2);
lean_inc(x_288);
x_289 = lean_ctor_get(x_279, 3);
lean_inc(x_289);
x_290 = lean_ctor_get(x_279, 4);
lean_inc(x_290);
x_291 = lean_ctor_get(x_279, 5);
lean_inc(x_291);
x_292 = lean_ctor_get(x_279, 6);
lean_inc(x_292);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 lean_ctor_release(x_279, 2);
 lean_ctor_release(x_279, 3);
 lean_ctor_release(x_279, 4);
 lean_ctor_release(x_279, 5);
 lean_ctor_release(x_279, 6);
 x_293 = x_279;
} else {
 lean_dec_ref(x_279);
 x_293 = lean_box(0);
}
x_294 = lean_ctor_get(x_280, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_280, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_296 = x_280;
} else {
 lean_dec_ref(x_280);
 x_296 = lean_box(0);
}
lean_inc(x_273);
x_297 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_294, x_1, x_273);
if (lean_is_scalar(x_296)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_296;
}
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_295);
if (lean_is_scalar(x_293)) {
 x_299 = lean_alloc_ctor(0, 7, 0);
} else {
 x_299 = x_293;
}
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_287);
lean_ctor_set(x_299, 2, x_288);
lean_ctor_set(x_299, 3, x_289);
lean_ctor_set(x_299, 4, x_290);
lean_ctor_set(x_299, 5, x_291);
lean_ctor_set(x_299, 6, x_292);
if (lean_is_scalar(x_286)) {
 x_300 = lean_alloc_ctor(0, 5, 0);
} else {
 x_300 = x_286;
}
lean_ctor_set(x_300, 0, x_282);
lean_ctor_set(x_300, 1, x_299);
lean_ctor_set(x_300, 2, x_283);
lean_ctor_set(x_300, 3, x_284);
lean_ctor_set(x_300, 4, x_285);
x_301 = lean_st_ref_set(x_3, x_300, x_281);
lean_dec(x_3);
x_302 = lean_ctor_get(x_301, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_303 = x_301;
} else {
 lean_dec_ref(x_301);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_273);
lean_ctor_set(x_304, 1, x_302);
return x_304;
}
else
{
lean_object* x_305; 
lean_dec(x_3);
lean_dec(x_1);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_273);
lean_ctor_set(x_305, 1, x_274);
return x_305;
}
}
else
{
lean_object* x_306; 
lean_dec(x_3);
lean_dec(x_1);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_273);
lean_ctor_set(x_306, 1, x_274);
return x_306;
}
}
}
else
{
uint8_t x_307; 
lean_dec(x_3);
lean_dec(x_1);
x_307 = !lean_is_exclusive(x_204);
if (x_307 == 0)
{
return x_204;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_204, 0);
x_309 = lean_ctor_get(x_204, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_204);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
else
{
lean_object* x_311; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_311 = lean_ctor_get(x_203, 0);
lean_inc(x_311);
lean_dec(x_203);
lean_ctor_set(x_196, 0, x_311);
return x_196;
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_312 = lean_ctor_get(x_196, 0);
x_313 = lean_ctor_get(x_196, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_196);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
lean_dec(x_314);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
lean_dec(x_315);
x_317 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_316, x_1);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; 
x_318 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_27, x_23, x_2, x_3, x_4, x_5, x_313);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_321 = x_318;
} else {
 lean_dec_ref(x_318);
 x_321 = lean_box(0);
}
x_322 = l_Lean_Expr_hasMVar(x_1);
if (x_322 == 0)
{
uint8_t x_323; 
x_323 = l_Lean_Expr_hasMVar(x_319);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_321);
x_324 = lean_st_ref_take(x_3, x_320);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_325, 1);
lean_inc(x_326);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_324, 1);
lean_inc(x_328);
lean_dec(x_324);
x_329 = lean_ctor_get(x_325, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_325, 2);
lean_inc(x_330);
x_331 = lean_ctor_get(x_325, 3);
lean_inc(x_331);
x_332 = lean_ctor_get(x_325, 4);
lean_inc(x_332);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 lean_ctor_release(x_325, 2);
 lean_ctor_release(x_325, 3);
 lean_ctor_release(x_325, 4);
 x_333 = x_325;
} else {
 lean_dec_ref(x_325);
 x_333 = lean_box(0);
}
x_334 = lean_ctor_get(x_326, 1);
lean_inc(x_334);
x_335 = lean_ctor_get(x_326, 2);
lean_inc(x_335);
x_336 = lean_ctor_get(x_326, 3);
lean_inc(x_336);
x_337 = lean_ctor_get(x_326, 4);
lean_inc(x_337);
x_338 = lean_ctor_get(x_326, 5);
lean_inc(x_338);
x_339 = lean_ctor_get(x_326, 6);
lean_inc(x_339);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 lean_ctor_release(x_326, 4);
 lean_ctor_release(x_326, 5);
 lean_ctor_release(x_326, 6);
 x_340 = x_326;
} else {
 lean_dec_ref(x_326);
 x_340 = lean_box(0);
}
x_341 = lean_ctor_get(x_327, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_327, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_343 = x_327;
} else {
 lean_dec_ref(x_327);
 x_343 = lean_box(0);
}
lean_inc(x_319);
x_344 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_341, x_1, x_319);
if (lean_is_scalar(x_343)) {
 x_345 = lean_alloc_ctor(0, 2, 0);
} else {
 x_345 = x_343;
}
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_342);
if (lean_is_scalar(x_340)) {
 x_346 = lean_alloc_ctor(0, 7, 0);
} else {
 x_346 = x_340;
}
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_334);
lean_ctor_set(x_346, 2, x_335);
lean_ctor_set(x_346, 3, x_336);
lean_ctor_set(x_346, 4, x_337);
lean_ctor_set(x_346, 5, x_338);
lean_ctor_set(x_346, 6, x_339);
if (lean_is_scalar(x_333)) {
 x_347 = lean_alloc_ctor(0, 5, 0);
} else {
 x_347 = x_333;
}
lean_ctor_set(x_347, 0, x_329);
lean_ctor_set(x_347, 1, x_346);
lean_ctor_set(x_347, 2, x_330);
lean_ctor_set(x_347, 3, x_331);
lean_ctor_set(x_347, 4, x_332);
x_348 = lean_st_ref_set(x_3, x_347, x_328);
lean_dec(x_3);
x_349 = lean_ctor_get(x_348, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_350 = x_348;
} else {
 lean_dec_ref(x_348);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_319);
lean_ctor_set(x_351, 1, x_349);
return x_351;
}
else
{
lean_object* x_352; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_321)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_321;
}
lean_ctor_set(x_352, 0, x_319);
lean_ctor_set(x_352, 1, x_320);
return x_352;
}
}
else
{
lean_object* x_353; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_321)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_321;
}
lean_ctor_set(x_353, 0, x_319);
lean_ctor_set(x_353, 1, x_320);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_3);
lean_dec(x_1);
x_354 = lean_ctor_get(x_318, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_318, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_356 = x_318;
} else {
 lean_dec_ref(x_318);
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
lean_object* x_358; lean_object* x_359; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_358 = lean_ctor_get(x_317, 0);
lean_inc(x_358);
lean_dec(x_317);
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_313);
return x_359;
}
}
}
default: 
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_1);
x_360 = lean_ctor_get(x_28, 1);
lean_inc(x_360);
lean_dec(x_28);
x_361 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3;
x_362 = l_panic___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__8(x_361, x_2, x_3, x_4, x_5, x_360);
return x_362;
}
}
}
}
case 5:
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_363 = lean_ctor_get(x_1, 0);
lean_inc(x_363);
x_364 = l_Lean_Expr_getAppFn(x_363);
lean_dec(x_363);
x_365 = lean_unsigned_to_nat(0u);
x_366 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_365);
x_367 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__1;
lean_inc(x_366);
x_368 = lean_mk_array(x_366, x_367);
x_369 = lean_unsigned_to_nat(1u);
x_370 = lean_nat_sub(x_366, x_369);
lean_dec(x_366);
lean_inc(x_1);
x_371 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_368, x_370);
x_372 = l_Lean_Meta_getTransparency(x_2, x_3, x_4, x_5, x_6);
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
switch (lean_obj_tag(x_373)) {
case 0:
{
lean_object* x_374; lean_object* x_375; uint8_t x_376; 
x_374 = lean_ctor_get(x_372, 1);
lean_inc(x_374);
lean_dec(x_372);
x_375 = lean_st_ref_get(x_3, x_374);
x_376 = !lean_is_exclusive(x_375);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_377 = lean_ctor_get(x_375, 0);
x_378 = lean_ctor_get(x_375, 1);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
lean_dec(x_379);
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
lean_dec(x_380);
x_382 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_381, x_1);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; 
lean_free_object(x_375);
lean_inc(x_3);
x_383 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_364, x_371, x_2, x_3, x_4, x_5, x_378);
lean_dec(x_371);
if (lean_obj_tag(x_383) == 0)
{
uint8_t x_384; 
x_384 = !lean_is_exclusive(x_383);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; uint8_t x_387; 
x_385 = lean_ctor_get(x_383, 0);
x_386 = lean_ctor_get(x_383, 1);
x_387 = l_Lean_Expr_hasMVar(x_1);
if (x_387 == 0)
{
uint8_t x_388; 
x_388 = l_Lean_Expr_hasMVar(x_385);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; 
lean_free_object(x_383);
x_389 = lean_st_ref_take(x_3, x_386);
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_389, 1);
lean_inc(x_393);
lean_dec(x_389);
x_394 = !lean_is_exclusive(x_390);
if (x_394 == 0)
{
lean_object* x_395; uint8_t x_396; 
x_395 = lean_ctor_get(x_390, 1);
lean_dec(x_395);
x_396 = !lean_is_exclusive(x_391);
if (x_396 == 0)
{
lean_object* x_397; uint8_t x_398; 
x_397 = lean_ctor_get(x_391, 0);
lean_dec(x_397);
x_398 = !lean_is_exclusive(x_392);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; 
x_399 = lean_ctor_get(x_392, 1);
lean_inc(x_385);
x_400 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_399, x_1, x_385);
lean_ctor_set(x_392, 1, x_400);
x_401 = lean_st_ref_set(x_3, x_390, x_393);
lean_dec(x_3);
x_402 = !lean_is_exclusive(x_401);
if (x_402 == 0)
{
lean_object* x_403; 
x_403 = lean_ctor_get(x_401, 0);
lean_dec(x_403);
lean_ctor_set(x_401, 0, x_385);
return x_401;
}
else
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_401, 1);
lean_inc(x_404);
lean_dec(x_401);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_385);
lean_ctor_set(x_405, 1, x_404);
return x_405;
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_406 = lean_ctor_get(x_392, 0);
x_407 = lean_ctor_get(x_392, 1);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_392);
lean_inc(x_385);
x_408 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_407, x_1, x_385);
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_406);
lean_ctor_set(x_409, 1, x_408);
lean_ctor_set(x_391, 0, x_409);
x_410 = lean_st_ref_set(x_3, x_390, x_393);
lean_dec(x_3);
x_411 = lean_ctor_get(x_410, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_412 = x_410;
} else {
 lean_dec_ref(x_410);
 x_412 = lean_box(0);
}
if (lean_is_scalar(x_412)) {
 x_413 = lean_alloc_ctor(0, 2, 0);
} else {
 x_413 = x_412;
}
lean_ctor_set(x_413, 0, x_385);
lean_ctor_set(x_413, 1, x_411);
return x_413;
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_414 = lean_ctor_get(x_391, 1);
x_415 = lean_ctor_get(x_391, 2);
x_416 = lean_ctor_get(x_391, 3);
x_417 = lean_ctor_get(x_391, 4);
x_418 = lean_ctor_get(x_391, 5);
x_419 = lean_ctor_get(x_391, 6);
lean_inc(x_419);
lean_inc(x_418);
lean_inc(x_417);
lean_inc(x_416);
lean_inc(x_415);
lean_inc(x_414);
lean_dec(x_391);
x_420 = lean_ctor_get(x_392, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_392, 1);
lean_inc(x_421);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_422 = x_392;
} else {
 lean_dec_ref(x_392);
 x_422 = lean_box(0);
}
lean_inc(x_385);
x_423 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_421, x_1, x_385);
if (lean_is_scalar(x_422)) {
 x_424 = lean_alloc_ctor(0, 2, 0);
} else {
 x_424 = x_422;
}
lean_ctor_set(x_424, 0, x_420);
lean_ctor_set(x_424, 1, x_423);
x_425 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_414);
lean_ctor_set(x_425, 2, x_415);
lean_ctor_set(x_425, 3, x_416);
lean_ctor_set(x_425, 4, x_417);
lean_ctor_set(x_425, 5, x_418);
lean_ctor_set(x_425, 6, x_419);
lean_ctor_set(x_390, 1, x_425);
x_426 = lean_st_ref_set(x_3, x_390, x_393);
lean_dec(x_3);
x_427 = lean_ctor_get(x_426, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 x_428 = x_426;
} else {
 lean_dec_ref(x_426);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(0, 2, 0);
} else {
 x_429 = x_428;
}
lean_ctor_set(x_429, 0, x_385);
lean_ctor_set(x_429, 1, x_427);
return x_429;
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_430 = lean_ctor_get(x_390, 0);
x_431 = lean_ctor_get(x_390, 2);
x_432 = lean_ctor_get(x_390, 3);
x_433 = lean_ctor_get(x_390, 4);
lean_inc(x_433);
lean_inc(x_432);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_390);
x_434 = lean_ctor_get(x_391, 1);
lean_inc(x_434);
x_435 = lean_ctor_get(x_391, 2);
lean_inc(x_435);
x_436 = lean_ctor_get(x_391, 3);
lean_inc(x_436);
x_437 = lean_ctor_get(x_391, 4);
lean_inc(x_437);
x_438 = lean_ctor_get(x_391, 5);
lean_inc(x_438);
x_439 = lean_ctor_get(x_391, 6);
lean_inc(x_439);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 lean_ctor_release(x_391, 2);
 lean_ctor_release(x_391, 3);
 lean_ctor_release(x_391, 4);
 lean_ctor_release(x_391, 5);
 lean_ctor_release(x_391, 6);
 x_440 = x_391;
} else {
 lean_dec_ref(x_391);
 x_440 = lean_box(0);
}
x_441 = lean_ctor_get(x_392, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_392, 1);
lean_inc(x_442);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_443 = x_392;
} else {
 lean_dec_ref(x_392);
 x_443 = lean_box(0);
}
lean_inc(x_385);
x_444 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_442, x_1, x_385);
if (lean_is_scalar(x_443)) {
 x_445 = lean_alloc_ctor(0, 2, 0);
} else {
 x_445 = x_443;
}
lean_ctor_set(x_445, 0, x_441);
lean_ctor_set(x_445, 1, x_444);
if (lean_is_scalar(x_440)) {
 x_446 = lean_alloc_ctor(0, 7, 0);
} else {
 x_446 = x_440;
}
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_434);
lean_ctor_set(x_446, 2, x_435);
lean_ctor_set(x_446, 3, x_436);
lean_ctor_set(x_446, 4, x_437);
lean_ctor_set(x_446, 5, x_438);
lean_ctor_set(x_446, 6, x_439);
x_447 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_447, 0, x_430);
lean_ctor_set(x_447, 1, x_446);
lean_ctor_set(x_447, 2, x_431);
lean_ctor_set(x_447, 3, x_432);
lean_ctor_set(x_447, 4, x_433);
x_448 = lean_st_ref_set(x_3, x_447, x_393);
lean_dec(x_3);
x_449 = lean_ctor_get(x_448, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 lean_ctor_release(x_448, 1);
 x_450 = x_448;
} else {
 lean_dec_ref(x_448);
 x_450 = lean_box(0);
}
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(0, 2, 0);
} else {
 x_451 = x_450;
}
lean_ctor_set(x_451, 0, x_385);
lean_ctor_set(x_451, 1, x_449);
return x_451;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_383;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_383;
}
}
else
{
lean_object* x_452; lean_object* x_453; uint8_t x_454; 
x_452 = lean_ctor_get(x_383, 0);
x_453 = lean_ctor_get(x_383, 1);
lean_inc(x_453);
lean_inc(x_452);
lean_dec(x_383);
x_454 = l_Lean_Expr_hasMVar(x_1);
if (x_454 == 0)
{
uint8_t x_455; 
x_455 = l_Lean_Expr_hasMVar(x_452);
if (x_455 == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_456 = lean_st_ref_take(x_3, x_453);
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_457, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_456, 1);
lean_inc(x_460);
lean_dec(x_456);
x_461 = lean_ctor_get(x_457, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_457, 2);
lean_inc(x_462);
x_463 = lean_ctor_get(x_457, 3);
lean_inc(x_463);
x_464 = lean_ctor_get(x_457, 4);
lean_inc(x_464);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 lean_ctor_release(x_457, 1);
 lean_ctor_release(x_457, 2);
 lean_ctor_release(x_457, 3);
 lean_ctor_release(x_457, 4);
 x_465 = x_457;
} else {
 lean_dec_ref(x_457);
 x_465 = lean_box(0);
}
x_466 = lean_ctor_get(x_458, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_458, 2);
lean_inc(x_467);
x_468 = lean_ctor_get(x_458, 3);
lean_inc(x_468);
x_469 = lean_ctor_get(x_458, 4);
lean_inc(x_469);
x_470 = lean_ctor_get(x_458, 5);
lean_inc(x_470);
x_471 = lean_ctor_get(x_458, 6);
lean_inc(x_471);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 lean_ctor_release(x_458, 2);
 lean_ctor_release(x_458, 3);
 lean_ctor_release(x_458, 4);
 lean_ctor_release(x_458, 5);
 lean_ctor_release(x_458, 6);
 x_472 = x_458;
} else {
 lean_dec_ref(x_458);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_459, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_459, 1);
lean_inc(x_474);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 x_475 = x_459;
} else {
 lean_dec_ref(x_459);
 x_475 = lean_box(0);
}
lean_inc(x_452);
x_476 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_474, x_1, x_452);
if (lean_is_scalar(x_475)) {
 x_477 = lean_alloc_ctor(0, 2, 0);
} else {
 x_477 = x_475;
}
lean_ctor_set(x_477, 0, x_473);
lean_ctor_set(x_477, 1, x_476);
if (lean_is_scalar(x_472)) {
 x_478 = lean_alloc_ctor(0, 7, 0);
} else {
 x_478 = x_472;
}
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_478, 1, x_466);
lean_ctor_set(x_478, 2, x_467);
lean_ctor_set(x_478, 3, x_468);
lean_ctor_set(x_478, 4, x_469);
lean_ctor_set(x_478, 5, x_470);
lean_ctor_set(x_478, 6, x_471);
if (lean_is_scalar(x_465)) {
 x_479 = lean_alloc_ctor(0, 5, 0);
} else {
 x_479 = x_465;
}
lean_ctor_set(x_479, 0, x_461);
lean_ctor_set(x_479, 1, x_478);
lean_ctor_set(x_479, 2, x_462);
lean_ctor_set(x_479, 3, x_463);
lean_ctor_set(x_479, 4, x_464);
x_480 = lean_st_ref_set(x_3, x_479, x_460);
lean_dec(x_3);
x_481 = lean_ctor_get(x_480, 1);
lean_inc(x_481);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_482 = x_480;
} else {
 lean_dec_ref(x_480);
 x_482 = lean_box(0);
}
if (lean_is_scalar(x_482)) {
 x_483 = lean_alloc_ctor(0, 2, 0);
} else {
 x_483 = x_482;
}
lean_ctor_set(x_483, 0, x_452);
lean_ctor_set(x_483, 1, x_481);
return x_483;
}
else
{
lean_object* x_484; 
lean_dec(x_3);
lean_dec(x_1);
x_484 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_484, 0, x_452);
lean_ctor_set(x_484, 1, x_453);
return x_484;
}
}
else
{
lean_object* x_485; 
lean_dec(x_3);
lean_dec(x_1);
x_485 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_485, 0, x_452);
lean_ctor_set(x_485, 1, x_453);
return x_485;
}
}
}
else
{
uint8_t x_486; 
lean_dec(x_3);
lean_dec(x_1);
x_486 = !lean_is_exclusive(x_383);
if (x_486 == 0)
{
return x_383;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_487 = lean_ctor_get(x_383, 0);
x_488 = lean_ctor_get(x_383, 1);
lean_inc(x_488);
lean_inc(x_487);
lean_dec(x_383);
x_489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set(x_489, 1, x_488);
return x_489;
}
}
}
else
{
lean_object* x_490; 
lean_dec(x_371);
lean_dec(x_364);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_490 = lean_ctor_get(x_382, 0);
lean_inc(x_490);
lean_dec(x_382);
lean_ctor_set(x_375, 0, x_490);
return x_375;
}
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_491 = lean_ctor_get(x_375, 0);
x_492 = lean_ctor_get(x_375, 1);
lean_inc(x_492);
lean_inc(x_491);
lean_dec(x_375);
x_493 = lean_ctor_get(x_491, 1);
lean_inc(x_493);
lean_dec(x_491);
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
lean_dec(x_493);
x_495 = lean_ctor_get(x_494, 1);
lean_inc(x_495);
lean_dec(x_494);
x_496 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_495, x_1);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; 
lean_inc(x_3);
x_497 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_364, x_371, x_2, x_3, x_4, x_5, x_492);
lean_dec(x_371);
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; 
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
x_501 = l_Lean_Expr_hasMVar(x_1);
if (x_501 == 0)
{
uint8_t x_502; 
x_502 = l_Lean_Expr_hasMVar(x_498);
if (x_502 == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_500);
x_503 = lean_st_ref_take(x_3, x_499);
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_504, 1);
lean_inc(x_505);
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_503, 1);
lean_inc(x_507);
lean_dec(x_503);
x_508 = lean_ctor_get(x_504, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_504, 2);
lean_inc(x_509);
x_510 = lean_ctor_get(x_504, 3);
lean_inc(x_510);
x_511 = lean_ctor_get(x_504, 4);
lean_inc(x_511);
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 lean_ctor_release(x_504, 1);
 lean_ctor_release(x_504, 2);
 lean_ctor_release(x_504, 3);
 lean_ctor_release(x_504, 4);
 x_512 = x_504;
} else {
 lean_dec_ref(x_504);
 x_512 = lean_box(0);
}
x_513 = lean_ctor_get(x_505, 1);
lean_inc(x_513);
x_514 = lean_ctor_get(x_505, 2);
lean_inc(x_514);
x_515 = lean_ctor_get(x_505, 3);
lean_inc(x_515);
x_516 = lean_ctor_get(x_505, 4);
lean_inc(x_516);
x_517 = lean_ctor_get(x_505, 5);
lean_inc(x_517);
x_518 = lean_ctor_get(x_505, 6);
lean_inc(x_518);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 lean_ctor_release(x_505, 2);
 lean_ctor_release(x_505, 3);
 lean_ctor_release(x_505, 4);
 lean_ctor_release(x_505, 5);
 lean_ctor_release(x_505, 6);
 x_519 = x_505;
} else {
 lean_dec_ref(x_505);
 x_519 = lean_box(0);
}
x_520 = lean_ctor_get(x_506, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_506, 1);
lean_inc(x_521);
if (lean_is_exclusive(x_506)) {
 lean_ctor_release(x_506, 0);
 lean_ctor_release(x_506, 1);
 x_522 = x_506;
} else {
 lean_dec_ref(x_506);
 x_522 = lean_box(0);
}
lean_inc(x_498);
x_523 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_521, x_1, x_498);
if (lean_is_scalar(x_522)) {
 x_524 = lean_alloc_ctor(0, 2, 0);
} else {
 x_524 = x_522;
}
lean_ctor_set(x_524, 0, x_520);
lean_ctor_set(x_524, 1, x_523);
if (lean_is_scalar(x_519)) {
 x_525 = lean_alloc_ctor(0, 7, 0);
} else {
 x_525 = x_519;
}
lean_ctor_set(x_525, 0, x_524);
lean_ctor_set(x_525, 1, x_513);
lean_ctor_set(x_525, 2, x_514);
lean_ctor_set(x_525, 3, x_515);
lean_ctor_set(x_525, 4, x_516);
lean_ctor_set(x_525, 5, x_517);
lean_ctor_set(x_525, 6, x_518);
if (lean_is_scalar(x_512)) {
 x_526 = lean_alloc_ctor(0, 5, 0);
} else {
 x_526 = x_512;
}
lean_ctor_set(x_526, 0, x_508);
lean_ctor_set(x_526, 1, x_525);
lean_ctor_set(x_526, 2, x_509);
lean_ctor_set(x_526, 3, x_510);
lean_ctor_set(x_526, 4, x_511);
x_527 = lean_st_ref_set(x_3, x_526, x_507);
lean_dec(x_3);
x_528 = lean_ctor_get(x_527, 1);
lean_inc(x_528);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 lean_ctor_release(x_527, 1);
 x_529 = x_527;
} else {
 lean_dec_ref(x_527);
 x_529 = lean_box(0);
}
if (lean_is_scalar(x_529)) {
 x_530 = lean_alloc_ctor(0, 2, 0);
} else {
 x_530 = x_529;
}
lean_ctor_set(x_530, 0, x_498);
lean_ctor_set(x_530, 1, x_528);
return x_530;
}
else
{
lean_object* x_531; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_500)) {
 x_531 = lean_alloc_ctor(0, 2, 0);
} else {
 x_531 = x_500;
}
lean_ctor_set(x_531, 0, x_498);
lean_ctor_set(x_531, 1, x_499);
return x_531;
}
}
else
{
lean_object* x_532; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_500)) {
 x_532 = lean_alloc_ctor(0, 2, 0);
} else {
 x_532 = x_500;
}
lean_ctor_set(x_532, 0, x_498);
lean_ctor_set(x_532, 1, x_499);
return x_532;
}
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
lean_dec(x_3);
lean_dec(x_1);
x_533 = lean_ctor_get(x_497, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_497, 1);
lean_inc(x_534);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 x_535 = x_497;
} else {
 lean_dec_ref(x_497);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 2, 0);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_533);
lean_ctor_set(x_536, 1, x_534);
return x_536;
}
}
else
{
lean_object* x_537; lean_object* x_538; 
lean_dec(x_371);
lean_dec(x_364);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_537 = lean_ctor_get(x_496, 0);
lean_inc(x_537);
lean_dec(x_496);
x_538 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_538, 1, x_492);
return x_538;
}
}
}
case 1:
{
lean_object* x_539; lean_object* x_540; uint8_t x_541; 
x_539 = lean_ctor_get(x_372, 1);
lean_inc(x_539);
lean_dec(x_372);
x_540 = lean_st_ref_get(x_3, x_539);
x_541 = !lean_is_exclusive(x_540);
if (x_541 == 0)
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_542 = lean_ctor_get(x_540, 0);
x_543 = lean_ctor_get(x_540, 1);
x_544 = lean_ctor_get(x_542, 1);
lean_inc(x_544);
lean_dec(x_542);
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
lean_dec(x_544);
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
lean_dec(x_545);
x_547 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_546, x_1);
if (lean_obj_tag(x_547) == 0)
{
lean_object* x_548; 
lean_free_object(x_540);
lean_inc(x_3);
x_548 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_364, x_371, x_2, x_3, x_4, x_5, x_543);
lean_dec(x_371);
if (lean_obj_tag(x_548) == 0)
{
uint8_t x_549; 
x_549 = !lean_is_exclusive(x_548);
if (x_549 == 0)
{
lean_object* x_550; lean_object* x_551; uint8_t x_552; 
x_550 = lean_ctor_get(x_548, 0);
x_551 = lean_ctor_get(x_548, 1);
x_552 = l_Lean_Expr_hasMVar(x_1);
if (x_552 == 0)
{
uint8_t x_553; 
x_553 = l_Lean_Expr_hasMVar(x_550);
if (x_553 == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; 
lean_free_object(x_548);
x_554 = lean_st_ref_take(x_3, x_551);
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_555, 1);
lean_inc(x_556);
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_554, 1);
lean_inc(x_558);
lean_dec(x_554);
x_559 = !lean_is_exclusive(x_555);
if (x_559 == 0)
{
lean_object* x_560; uint8_t x_561; 
x_560 = lean_ctor_get(x_555, 1);
lean_dec(x_560);
x_561 = !lean_is_exclusive(x_556);
if (x_561 == 0)
{
lean_object* x_562; uint8_t x_563; 
x_562 = lean_ctor_get(x_556, 0);
lean_dec(x_562);
x_563 = !lean_is_exclusive(x_557);
if (x_563 == 0)
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; uint8_t x_567; 
x_564 = lean_ctor_get(x_557, 0);
lean_inc(x_550);
x_565 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_564, x_1, x_550);
lean_ctor_set(x_557, 0, x_565);
x_566 = lean_st_ref_set(x_3, x_555, x_558);
lean_dec(x_3);
x_567 = !lean_is_exclusive(x_566);
if (x_567 == 0)
{
lean_object* x_568; 
x_568 = lean_ctor_get(x_566, 0);
lean_dec(x_568);
lean_ctor_set(x_566, 0, x_550);
return x_566;
}
else
{
lean_object* x_569; lean_object* x_570; 
x_569 = lean_ctor_get(x_566, 1);
lean_inc(x_569);
lean_dec(x_566);
x_570 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_570, 0, x_550);
lean_ctor_set(x_570, 1, x_569);
return x_570;
}
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_571 = lean_ctor_get(x_557, 0);
x_572 = lean_ctor_get(x_557, 1);
lean_inc(x_572);
lean_inc(x_571);
lean_dec(x_557);
lean_inc(x_550);
x_573 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_571, x_1, x_550);
x_574 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_572);
lean_ctor_set(x_556, 0, x_574);
x_575 = lean_st_ref_set(x_3, x_555, x_558);
lean_dec(x_3);
x_576 = lean_ctor_get(x_575, 1);
lean_inc(x_576);
if (lean_is_exclusive(x_575)) {
 lean_ctor_release(x_575, 0);
 lean_ctor_release(x_575, 1);
 x_577 = x_575;
} else {
 lean_dec_ref(x_575);
 x_577 = lean_box(0);
}
if (lean_is_scalar(x_577)) {
 x_578 = lean_alloc_ctor(0, 2, 0);
} else {
 x_578 = x_577;
}
lean_ctor_set(x_578, 0, x_550);
lean_ctor_set(x_578, 1, x_576);
return x_578;
}
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_579 = lean_ctor_get(x_556, 1);
x_580 = lean_ctor_get(x_556, 2);
x_581 = lean_ctor_get(x_556, 3);
x_582 = lean_ctor_get(x_556, 4);
x_583 = lean_ctor_get(x_556, 5);
x_584 = lean_ctor_get(x_556, 6);
lean_inc(x_584);
lean_inc(x_583);
lean_inc(x_582);
lean_inc(x_581);
lean_inc(x_580);
lean_inc(x_579);
lean_dec(x_556);
x_585 = lean_ctor_get(x_557, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_557, 1);
lean_inc(x_586);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_587 = x_557;
} else {
 lean_dec_ref(x_557);
 x_587 = lean_box(0);
}
lean_inc(x_550);
x_588 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_585, x_1, x_550);
if (lean_is_scalar(x_587)) {
 x_589 = lean_alloc_ctor(0, 2, 0);
} else {
 x_589 = x_587;
}
lean_ctor_set(x_589, 0, x_588);
lean_ctor_set(x_589, 1, x_586);
x_590 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_579);
lean_ctor_set(x_590, 2, x_580);
lean_ctor_set(x_590, 3, x_581);
lean_ctor_set(x_590, 4, x_582);
lean_ctor_set(x_590, 5, x_583);
lean_ctor_set(x_590, 6, x_584);
lean_ctor_set(x_555, 1, x_590);
x_591 = lean_st_ref_set(x_3, x_555, x_558);
lean_dec(x_3);
x_592 = lean_ctor_get(x_591, 1);
lean_inc(x_592);
if (lean_is_exclusive(x_591)) {
 lean_ctor_release(x_591, 0);
 lean_ctor_release(x_591, 1);
 x_593 = x_591;
} else {
 lean_dec_ref(x_591);
 x_593 = lean_box(0);
}
if (lean_is_scalar(x_593)) {
 x_594 = lean_alloc_ctor(0, 2, 0);
} else {
 x_594 = x_593;
}
lean_ctor_set(x_594, 0, x_550);
lean_ctor_set(x_594, 1, x_592);
return x_594;
}
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_595 = lean_ctor_get(x_555, 0);
x_596 = lean_ctor_get(x_555, 2);
x_597 = lean_ctor_get(x_555, 3);
x_598 = lean_ctor_get(x_555, 4);
lean_inc(x_598);
lean_inc(x_597);
lean_inc(x_596);
lean_inc(x_595);
lean_dec(x_555);
x_599 = lean_ctor_get(x_556, 1);
lean_inc(x_599);
x_600 = lean_ctor_get(x_556, 2);
lean_inc(x_600);
x_601 = lean_ctor_get(x_556, 3);
lean_inc(x_601);
x_602 = lean_ctor_get(x_556, 4);
lean_inc(x_602);
x_603 = lean_ctor_get(x_556, 5);
lean_inc(x_603);
x_604 = lean_ctor_get(x_556, 6);
lean_inc(x_604);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 lean_ctor_release(x_556, 2);
 lean_ctor_release(x_556, 3);
 lean_ctor_release(x_556, 4);
 lean_ctor_release(x_556, 5);
 lean_ctor_release(x_556, 6);
 x_605 = x_556;
} else {
 lean_dec_ref(x_556);
 x_605 = lean_box(0);
}
x_606 = lean_ctor_get(x_557, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_557, 1);
lean_inc(x_607);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_608 = x_557;
} else {
 lean_dec_ref(x_557);
 x_608 = lean_box(0);
}
lean_inc(x_550);
x_609 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_606, x_1, x_550);
if (lean_is_scalar(x_608)) {
 x_610 = lean_alloc_ctor(0, 2, 0);
} else {
 x_610 = x_608;
}
lean_ctor_set(x_610, 0, x_609);
lean_ctor_set(x_610, 1, x_607);
if (lean_is_scalar(x_605)) {
 x_611 = lean_alloc_ctor(0, 7, 0);
} else {
 x_611 = x_605;
}
lean_ctor_set(x_611, 0, x_610);
lean_ctor_set(x_611, 1, x_599);
lean_ctor_set(x_611, 2, x_600);
lean_ctor_set(x_611, 3, x_601);
lean_ctor_set(x_611, 4, x_602);
lean_ctor_set(x_611, 5, x_603);
lean_ctor_set(x_611, 6, x_604);
x_612 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_612, 0, x_595);
lean_ctor_set(x_612, 1, x_611);
lean_ctor_set(x_612, 2, x_596);
lean_ctor_set(x_612, 3, x_597);
lean_ctor_set(x_612, 4, x_598);
x_613 = lean_st_ref_set(x_3, x_612, x_558);
lean_dec(x_3);
x_614 = lean_ctor_get(x_613, 1);
lean_inc(x_614);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 lean_ctor_release(x_613, 1);
 x_615 = x_613;
} else {
 lean_dec_ref(x_613);
 x_615 = lean_box(0);
}
if (lean_is_scalar(x_615)) {
 x_616 = lean_alloc_ctor(0, 2, 0);
} else {
 x_616 = x_615;
}
lean_ctor_set(x_616, 0, x_550);
lean_ctor_set(x_616, 1, x_614);
return x_616;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_548;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_548;
}
}
else
{
lean_object* x_617; lean_object* x_618; uint8_t x_619; 
x_617 = lean_ctor_get(x_548, 0);
x_618 = lean_ctor_get(x_548, 1);
lean_inc(x_618);
lean_inc(x_617);
lean_dec(x_548);
x_619 = l_Lean_Expr_hasMVar(x_1);
if (x_619 == 0)
{
uint8_t x_620; 
x_620 = l_Lean_Expr_hasMVar(x_617);
if (x_620 == 0)
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_621 = lean_st_ref_take(x_3, x_618);
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_622, 1);
lean_inc(x_623);
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_621, 1);
lean_inc(x_625);
lean_dec(x_621);
x_626 = lean_ctor_get(x_622, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_622, 2);
lean_inc(x_627);
x_628 = lean_ctor_get(x_622, 3);
lean_inc(x_628);
x_629 = lean_ctor_get(x_622, 4);
lean_inc(x_629);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 lean_ctor_release(x_622, 2);
 lean_ctor_release(x_622, 3);
 lean_ctor_release(x_622, 4);
 x_630 = x_622;
} else {
 lean_dec_ref(x_622);
 x_630 = lean_box(0);
}
x_631 = lean_ctor_get(x_623, 1);
lean_inc(x_631);
x_632 = lean_ctor_get(x_623, 2);
lean_inc(x_632);
x_633 = lean_ctor_get(x_623, 3);
lean_inc(x_633);
x_634 = lean_ctor_get(x_623, 4);
lean_inc(x_634);
x_635 = lean_ctor_get(x_623, 5);
lean_inc(x_635);
x_636 = lean_ctor_get(x_623, 6);
lean_inc(x_636);
if (lean_is_exclusive(x_623)) {
 lean_ctor_release(x_623, 0);
 lean_ctor_release(x_623, 1);
 lean_ctor_release(x_623, 2);
 lean_ctor_release(x_623, 3);
 lean_ctor_release(x_623, 4);
 lean_ctor_release(x_623, 5);
 lean_ctor_release(x_623, 6);
 x_637 = x_623;
} else {
 lean_dec_ref(x_623);
 x_637 = lean_box(0);
}
x_638 = lean_ctor_get(x_624, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_624, 1);
lean_inc(x_639);
if (lean_is_exclusive(x_624)) {
 lean_ctor_release(x_624, 0);
 lean_ctor_release(x_624, 1);
 x_640 = x_624;
} else {
 lean_dec_ref(x_624);
 x_640 = lean_box(0);
}
lean_inc(x_617);
x_641 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_638, x_1, x_617);
if (lean_is_scalar(x_640)) {
 x_642 = lean_alloc_ctor(0, 2, 0);
} else {
 x_642 = x_640;
}
lean_ctor_set(x_642, 0, x_641);
lean_ctor_set(x_642, 1, x_639);
if (lean_is_scalar(x_637)) {
 x_643 = lean_alloc_ctor(0, 7, 0);
} else {
 x_643 = x_637;
}
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_631);
lean_ctor_set(x_643, 2, x_632);
lean_ctor_set(x_643, 3, x_633);
lean_ctor_set(x_643, 4, x_634);
lean_ctor_set(x_643, 5, x_635);
lean_ctor_set(x_643, 6, x_636);
if (lean_is_scalar(x_630)) {
 x_644 = lean_alloc_ctor(0, 5, 0);
} else {
 x_644 = x_630;
}
lean_ctor_set(x_644, 0, x_626);
lean_ctor_set(x_644, 1, x_643);
lean_ctor_set(x_644, 2, x_627);
lean_ctor_set(x_644, 3, x_628);
lean_ctor_set(x_644, 4, x_629);
x_645 = lean_st_ref_set(x_3, x_644, x_625);
lean_dec(x_3);
x_646 = lean_ctor_get(x_645, 1);
lean_inc(x_646);
if (lean_is_exclusive(x_645)) {
 lean_ctor_release(x_645, 0);
 lean_ctor_release(x_645, 1);
 x_647 = x_645;
} else {
 lean_dec_ref(x_645);
 x_647 = lean_box(0);
}
if (lean_is_scalar(x_647)) {
 x_648 = lean_alloc_ctor(0, 2, 0);
} else {
 x_648 = x_647;
}
lean_ctor_set(x_648, 0, x_617);
lean_ctor_set(x_648, 1, x_646);
return x_648;
}
else
{
lean_object* x_649; 
lean_dec(x_3);
lean_dec(x_1);
x_649 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_649, 0, x_617);
lean_ctor_set(x_649, 1, x_618);
return x_649;
}
}
else
{
lean_object* x_650; 
lean_dec(x_3);
lean_dec(x_1);
x_650 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_650, 0, x_617);
lean_ctor_set(x_650, 1, x_618);
return x_650;
}
}
}
else
{
uint8_t x_651; 
lean_dec(x_3);
lean_dec(x_1);
x_651 = !lean_is_exclusive(x_548);
if (x_651 == 0)
{
return x_548;
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_652 = lean_ctor_get(x_548, 0);
x_653 = lean_ctor_get(x_548, 1);
lean_inc(x_653);
lean_inc(x_652);
lean_dec(x_548);
x_654 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_654, 0, x_652);
lean_ctor_set(x_654, 1, x_653);
return x_654;
}
}
}
else
{
lean_object* x_655; 
lean_dec(x_371);
lean_dec(x_364);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_655 = lean_ctor_get(x_547, 0);
lean_inc(x_655);
lean_dec(x_547);
lean_ctor_set(x_540, 0, x_655);
return x_540;
}
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_656 = lean_ctor_get(x_540, 0);
x_657 = lean_ctor_get(x_540, 1);
lean_inc(x_657);
lean_inc(x_656);
lean_dec(x_540);
x_658 = lean_ctor_get(x_656, 1);
lean_inc(x_658);
lean_dec(x_656);
x_659 = lean_ctor_get(x_658, 0);
lean_inc(x_659);
lean_dec(x_658);
x_660 = lean_ctor_get(x_659, 0);
lean_inc(x_660);
lean_dec(x_659);
x_661 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_660, x_1);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; 
lean_inc(x_3);
x_662 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_364, x_371, x_2, x_3, x_4, x_5, x_657);
lean_dec(x_371);
if (lean_obj_tag(x_662) == 0)
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; uint8_t x_666; 
x_663 = lean_ctor_get(x_662, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_662, 1);
lean_inc(x_664);
if (lean_is_exclusive(x_662)) {
 lean_ctor_release(x_662, 0);
 lean_ctor_release(x_662, 1);
 x_665 = x_662;
} else {
 lean_dec_ref(x_662);
 x_665 = lean_box(0);
}
x_666 = l_Lean_Expr_hasMVar(x_1);
if (x_666 == 0)
{
uint8_t x_667; 
x_667 = l_Lean_Expr_hasMVar(x_663);
if (x_667 == 0)
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
lean_dec(x_665);
x_668 = lean_st_ref_take(x_3, x_664);
x_669 = lean_ctor_get(x_668, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_669, 1);
lean_inc(x_670);
x_671 = lean_ctor_get(x_670, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_668, 1);
lean_inc(x_672);
lean_dec(x_668);
x_673 = lean_ctor_get(x_669, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_669, 2);
lean_inc(x_674);
x_675 = lean_ctor_get(x_669, 3);
lean_inc(x_675);
x_676 = lean_ctor_get(x_669, 4);
lean_inc(x_676);
if (lean_is_exclusive(x_669)) {
 lean_ctor_release(x_669, 0);
 lean_ctor_release(x_669, 1);
 lean_ctor_release(x_669, 2);
 lean_ctor_release(x_669, 3);
 lean_ctor_release(x_669, 4);
 x_677 = x_669;
} else {
 lean_dec_ref(x_669);
 x_677 = lean_box(0);
}
x_678 = lean_ctor_get(x_670, 1);
lean_inc(x_678);
x_679 = lean_ctor_get(x_670, 2);
lean_inc(x_679);
x_680 = lean_ctor_get(x_670, 3);
lean_inc(x_680);
x_681 = lean_ctor_get(x_670, 4);
lean_inc(x_681);
x_682 = lean_ctor_get(x_670, 5);
lean_inc(x_682);
x_683 = lean_ctor_get(x_670, 6);
lean_inc(x_683);
if (lean_is_exclusive(x_670)) {
 lean_ctor_release(x_670, 0);
 lean_ctor_release(x_670, 1);
 lean_ctor_release(x_670, 2);
 lean_ctor_release(x_670, 3);
 lean_ctor_release(x_670, 4);
 lean_ctor_release(x_670, 5);
 lean_ctor_release(x_670, 6);
 x_684 = x_670;
} else {
 lean_dec_ref(x_670);
 x_684 = lean_box(0);
}
x_685 = lean_ctor_get(x_671, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_671, 1);
lean_inc(x_686);
if (lean_is_exclusive(x_671)) {
 lean_ctor_release(x_671, 0);
 lean_ctor_release(x_671, 1);
 x_687 = x_671;
} else {
 lean_dec_ref(x_671);
 x_687 = lean_box(0);
}
lean_inc(x_663);
x_688 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_685, x_1, x_663);
if (lean_is_scalar(x_687)) {
 x_689 = lean_alloc_ctor(0, 2, 0);
} else {
 x_689 = x_687;
}
lean_ctor_set(x_689, 0, x_688);
lean_ctor_set(x_689, 1, x_686);
if (lean_is_scalar(x_684)) {
 x_690 = lean_alloc_ctor(0, 7, 0);
} else {
 x_690 = x_684;
}
lean_ctor_set(x_690, 0, x_689);
lean_ctor_set(x_690, 1, x_678);
lean_ctor_set(x_690, 2, x_679);
lean_ctor_set(x_690, 3, x_680);
lean_ctor_set(x_690, 4, x_681);
lean_ctor_set(x_690, 5, x_682);
lean_ctor_set(x_690, 6, x_683);
if (lean_is_scalar(x_677)) {
 x_691 = lean_alloc_ctor(0, 5, 0);
} else {
 x_691 = x_677;
}
lean_ctor_set(x_691, 0, x_673);
lean_ctor_set(x_691, 1, x_690);
lean_ctor_set(x_691, 2, x_674);
lean_ctor_set(x_691, 3, x_675);
lean_ctor_set(x_691, 4, x_676);
x_692 = lean_st_ref_set(x_3, x_691, x_672);
lean_dec(x_3);
x_693 = lean_ctor_get(x_692, 1);
lean_inc(x_693);
if (lean_is_exclusive(x_692)) {
 lean_ctor_release(x_692, 0);
 lean_ctor_release(x_692, 1);
 x_694 = x_692;
} else {
 lean_dec_ref(x_692);
 x_694 = lean_box(0);
}
if (lean_is_scalar(x_694)) {
 x_695 = lean_alloc_ctor(0, 2, 0);
} else {
 x_695 = x_694;
}
lean_ctor_set(x_695, 0, x_663);
lean_ctor_set(x_695, 1, x_693);
return x_695;
}
else
{
lean_object* x_696; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_665)) {
 x_696 = lean_alloc_ctor(0, 2, 0);
} else {
 x_696 = x_665;
}
lean_ctor_set(x_696, 0, x_663);
lean_ctor_set(x_696, 1, x_664);
return x_696;
}
}
else
{
lean_object* x_697; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_665)) {
 x_697 = lean_alloc_ctor(0, 2, 0);
} else {
 x_697 = x_665;
}
lean_ctor_set(x_697, 0, x_663);
lean_ctor_set(x_697, 1, x_664);
return x_697;
}
}
else
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; 
lean_dec(x_3);
lean_dec(x_1);
x_698 = lean_ctor_get(x_662, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_662, 1);
lean_inc(x_699);
if (lean_is_exclusive(x_662)) {
 lean_ctor_release(x_662, 0);
 lean_ctor_release(x_662, 1);
 x_700 = x_662;
} else {
 lean_dec_ref(x_662);
 x_700 = lean_box(0);
}
if (lean_is_scalar(x_700)) {
 x_701 = lean_alloc_ctor(1, 2, 0);
} else {
 x_701 = x_700;
}
lean_ctor_set(x_701, 0, x_698);
lean_ctor_set(x_701, 1, x_699);
return x_701;
}
}
else
{
lean_object* x_702; lean_object* x_703; 
lean_dec(x_371);
lean_dec(x_364);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_702 = lean_ctor_get(x_661, 0);
lean_inc(x_702);
lean_dec(x_661);
x_703 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_703, 0, x_702);
lean_ctor_set(x_703, 1, x_657);
return x_703;
}
}
}
default: 
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; 
lean_dec(x_373);
lean_dec(x_371);
lean_dec(x_364);
lean_dec(x_1);
x_704 = lean_ctor_get(x_372, 1);
lean_inc(x_704);
lean_dec(x_372);
x_705 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3;
x_706 = l_panic___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__8(x_705, x_2, x_3, x_4, x_5, x_704);
return x_706;
}
}
}
case 7:
{
lean_object* x_707; lean_object* x_708; 
x_707 = l_Lean_Meta_getTransparency(x_2, x_3, x_4, x_5, x_6);
x_708 = lean_ctor_get(x_707, 0);
lean_inc(x_708);
switch (lean_obj_tag(x_708)) {
case 0:
{
lean_object* x_709; lean_object* x_710; uint8_t x_711; 
x_709 = lean_ctor_get(x_707, 1);
lean_inc(x_709);
lean_dec(x_707);
x_710 = lean_st_ref_get(x_3, x_709);
x_711 = !lean_is_exclusive(x_710);
if (x_711 == 0)
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_712 = lean_ctor_get(x_710, 0);
x_713 = lean_ctor_get(x_710, 1);
x_714 = lean_ctor_get(x_712, 1);
lean_inc(x_714);
lean_dec(x_712);
x_715 = lean_ctor_get(x_714, 0);
lean_inc(x_715);
lean_dec(x_714);
x_716 = lean_ctor_get(x_715, 1);
lean_inc(x_716);
lean_dec(x_715);
x_717 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_716, x_1);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; uint8_t x_719; lean_object* x_720; 
lean_free_object(x_710);
x_718 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1;
x_719 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_720 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_1, x_718, x_719, x_2, x_3, x_4, x_5, x_713);
if (lean_obj_tag(x_720) == 0)
{
uint8_t x_721; 
x_721 = !lean_is_exclusive(x_720);
if (x_721 == 0)
{
lean_object* x_722; lean_object* x_723; uint8_t x_724; 
x_722 = lean_ctor_get(x_720, 0);
x_723 = lean_ctor_get(x_720, 1);
x_724 = l_Lean_Expr_hasMVar(x_1);
if (x_724 == 0)
{
uint8_t x_725; 
x_725 = l_Lean_Expr_hasMVar(x_722);
if (x_725 == 0)
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; uint8_t x_731; 
lean_free_object(x_720);
x_726 = lean_st_ref_take(x_3, x_723);
x_727 = lean_ctor_get(x_726, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_727, 1);
lean_inc(x_728);
x_729 = lean_ctor_get(x_728, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_726, 1);
lean_inc(x_730);
lean_dec(x_726);
x_731 = !lean_is_exclusive(x_727);
if (x_731 == 0)
{
lean_object* x_732; uint8_t x_733; 
x_732 = lean_ctor_get(x_727, 1);
lean_dec(x_732);
x_733 = !lean_is_exclusive(x_728);
if (x_733 == 0)
{
lean_object* x_734; uint8_t x_735; 
x_734 = lean_ctor_get(x_728, 0);
lean_dec(x_734);
x_735 = !lean_is_exclusive(x_729);
if (x_735 == 0)
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; uint8_t x_739; 
x_736 = lean_ctor_get(x_729, 1);
lean_inc(x_722);
x_737 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_736, x_1, x_722);
lean_ctor_set(x_729, 1, x_737);
x_738 = lean_st_ref_set(x_3, x_727, x_730);
lean_dec(x_3);
x_739 = !lean_is_exclusive(x_738);
if (x_739 == 0)
{
lean_object* x_740; 
x_740 = lean_ctor_get(x_738, 0);
lean_dec(x_740);
lean_ctor_set(x_738, 0, x_722);
return x_738;
}
else
{
lean_object* x_741; lean_object* x_742; 
x_741 = lean_ctor_get(x_738, 1);
lean_inc(x_741);
lean_dec(x_738);
x_742 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_742, 0, x_722);
lean_ctor_set(x_742, 1, x_741);
return x_742;
}
}
else
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_743 = lean_ctor_get(x_729, 0);
x_744 = lean_ctor_get(x_729, 1);
lean_inc(x_744);
lean_inc(x_743);
lean_dec(x_729);
lean_inc(x_722);
x_745 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_744, x_1, x_722);
x_746 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_746, 0, x_743);
lean_ctor_set(x_746, 1, x_745);
lean_ctor_set(x_728, 0, x_746);
x_747 = lean_st_ref_set(x_3, x_727, x_730);
lean_dec(x_3);
x_748 = lean_ctor_get(x_747, 1);
lean_inc(x_748);
if (lean_is_exclusive(x_747)) {
 lean_ctor_release(x_747, 0);
 lean_ctor_release(x_747, 1);
 x_749 = x_747;
} else {
 lean_dec_ref(x_747);
 x_749 = lean_box(0);
}
if (lean_is_scalar(x_749)) {
 x_750 = lean_alloc_ctor(0, 2, 0);
} else {
 x_750 = x_749;
}
lean_ctor_set(x_750, 0, x_722);
lean_ctor_set(x_750, 1, x_748);
return x_750;
}
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_751 = lean_ctor_get(x_728, 1);
x_752 = lean_ctor_get(x_728, 2);
x_753 = lean_ctor_get(x_728, 3);
x_754 = lean_ctor_get(x_728, 4);
x_755 = lean_ctor_get(x_728, 5);
x_756 = lean_ctor_get(x_728, 6);
lean_inc(x_756);
lean_inc(x_755);
lean_inc(x_754);
lean_inc(x_753);
lean_inc(x_752);
lean_inc(x_751);
lean_dec(x_728);
x_757 = lean_ctor_get(x_729, 0);
lean_inc(x_757);
x_758 = lean_ctor_get(x_729, 1);
lean_inc(x_758);
if (lean_is_exclusive(x_729)) {
 lean_ctor_release(x_729, 0);
 lean_ctor_release(x_729, 1);
 x_759 = x_729;
} else {
 lean_dec_ref(x_729);
 x_759 = lean_box(0);
}
lean_inc(x_722);
x_760 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_758, x_1, x_722);
if (lean_is_scalar(x_759)) {
 x_761 = lean_alloc_ctor(0, 2, 0);
} else {
 x_761 = x_759;
}
lean_ctor_set(x_761, 0, x_757);
lean_ctor_set(x_761, 1, x_760);
x_762 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_762, 0, x_761);
lean_ctor_set(x_762, 1, x_751);
lean_ctor_set(x_762, 2, x_752);
lean_ctor_set(x_762, 3, x_753);
lean_ctor_set(x_762, 4, x_754);
lean_ctor_set(x_762, 5, x_755);
lean_ctor_set(x_762, 6, x_756);
lean_ctor_set(x_727, 1, x_762);
x_763 = lean_st_ref_set(x_3, x_727, x_730);
lean_dec(x_3);
x_764 = lean_ctor_get(x_763, 1);
lean_inc(x_764);
if (lean_is_exclusive(x_763)) {
 lean_ctor_release(x_763, 0);
 lean_ctor_release(x_763, 1);
 x_765 = x_763;
} else {
 lean_dec_ref(x_763);
 x_765 = lean_box(0);
}
if (lean_is_scalar(x_765)) {
 x_766 = lean_alloc_ctor(0, 2, 0);
} else {
 x_766 = x_765;
}
lean_ctor_set(x_766, 0, x_722);
lean_ctor_set(x_766, 1, x_764);
return x_766;
}
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_767 = lean_ctor_get(x_727, 0);
x_768 = lean_ctor_get(x_727, 2);
x_769 = lean_ctor_get(x_727, 3);
x_770 = lean_ctor_get(x_727, 4);
lean_inc(x_770);
lean_inc(x_769);
lean_inc(x_768);
lean_inc(x_767);
lean_dec(x_727);
x_771 = lean_ctor_get(x_728, 1);
lean_inc(x_771);
x_772 = lean_ctor_get(x_728, 2);
lean_inc(x_772);
x_773 = lean_ctor_get(x_728, 3);
lean_inc(x_773);
x_774 = lean_ctor_get(x_728, 4);
lean_inc(x_774);
x_775 = lean_ctor_get(x_728, 5);
lean_inc(x_775);
x_776 = lean_ctor_get(x_728, 6);
lean_inc(x_776);
if (lean_is_exclusive(x_728)) {
 lean_ctor_release(x_728, 0);
 lean_ctor_release(x_728, 1);
 lean_ctor_release(x_728, 2);
 lean_ctor_release(x_728, 3);
 lean_ctor_release(x_728, 4);
 lean_ctor_release(x_728, 5);
 lean_ctor_release(x_728, 6);
 x_777 = x_728;
} else {
 lean_dec_ref(x_728);
 x_777 = lean_box(0);
}
x_778 = lean_ctor_get(x_729, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_729, 1);
lean_inc(x_779);
if (lean_is_exclusive(x_729)) {
 lean_ctor_release(x_729, 0);
 lean_ctor_release(x_729, 1);
 x_780 = x_729;
} else {
 lean_dec_ref(x_729);
 x_780 = lean_box(0);
}
lean_inc(x_722);
x_781 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_779, x_1, x_722);
if (lean_is_scalar(x_780)) {
 x_782 = lean_alloc_ctor(0, 2, 0);
} else {
 x_782 = x_780;
}
lean_ctor_set(x_782, 0, x_778);
lean_ctor_set(x_782, 1, x_781);
if (lean_is_scalar(x_777)) {
 x_783 = lean_alloc_ctor(0, 7, 0);
} else {
 x_783 = x_777;
}
lean_ctor_set(x_783, 0, x_782);
lean_ctor_set(x_783, 1, x_771);
lean_ctor_set(x_783, 2, x_772);
lean_ctor_set(x_783, 3, x_773);
lean_ctor_set(x_783, 4, x_774);
lean_ctor_set(x_783, 5, x_775);
lean_ctor_set(x_783, 6, x_776);
x_784 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_784, 0, x_767);
lean_ctor_set(x_784, 1, x_783);
lean_ctor_set(x_784, 2, x_768);
lean_ctor_set(x_784, 3, x_769);
lean_ctor_set(x_784, 4, x_770);
x_785 = lean_st_ref_set(x_3, x_784, x_730);
lean_dec(x_3);
x_786 = lean_ctor_get(x_785, 1);
lean_inc(x_786);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 lean_ctor_release(x_785, 1);
 x_787 = x_785;
} else {
 lean_dec_ref(x_785);
 x_787 = lean_box(0);
}
if (lean_is_scalar(x_787)) {
 x_788 = lean_alloc_ctor(0, 2, 0);
} else {
 x_788 = x_787;
}
lean_ctor_set(x_788, 0, x_722);
lean_ctor_set(x_788, 1, x_786);
return x_788;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_720;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_720;
}
}
else
{
lean_object* x_789; lean_object* x_790; uint8_t x_791; 
x_789 = lean_ctor_get(x_720, 0);
x_790 = lean_ctor_get(x_720, 1);
lean_inc(x_790);
lean_inc(x_789);
lean_dec(x_720);
x_791 = l_Lean_Expr_hasMVar(x_1);
if (x_791 == 0)
{
uint8_t x_792; 
x_792 = l_Lean_Expr_hasMVar(x_789);
if (x_792 == 0)
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; 
x_793 = lean_st_ref_take(x_3, x_790);
x_794 = lean_ctor_get(x_793, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_794, 1);
lean_inc(x_795);
x_796 = lean_ctor_get(x_795, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_793, 1);
lean_inc(x_797);
lean_dec(x_793);
x_798 = lean_ctor_get(x_794, 0);
lean_inc(x_798);
x_799 = lean_ctor_get(x_794, 2);
lean_inc(x_799);
x_800 = lean_ctor_get(x_794, 3);
lean_inc(x_800);
x_801 = lean_ctor_get(x_794, 4);
lean_inc(x_801);
if (lean_is_exclusive(x_794)) {
 lean_ctor_release(x_794, 0);
 lean_ctor_release(x_794, 1);
 lean_ctor_release(x_794, 2);
 lean_ctor_release(x_794, 3);
 lean_ctor_release(x_794, 4);
 x_802 = x_794;
} else {
 lean_dec_ref(x_794);
 x_802 = lean_box(0);
}
x_803 = lean_ctor_get(x_795, 1);
lean_inc(x_803);
x_804 = lean_ctor_get(x_795, 2);
lean_inc(x_804);
x_805 = lean_ctor_get(x_795, 3);
lean_inc(x_805);
x_806 = lean_ctor_get(x_795, 4);
lean_inc(x_806);
x_807 = lean_ctor_get(x_795, 5);
lean_inc(x_807);
x_808 = lean_ctor_get(x_795, 6);
lean_inc(x_808);
if (lean_is_exclusive(x_795)) {
 lean_ctor_release(x_795, 0);
 lean_ctor_release(x_795, 1);
 lean_ctor_release(x_795, 2);
 lean_ctor_release(x_795, 3);
 lean_ctor_release(x_795, 4);
 lean_ctor_release(x_795, 5);
 lean_ctor_release(x_795, 6);
 x_809 = x_795;
} else {
 lean_dec_ref(x_795);
 x_809 = lean_box(0);
}
x_810 = lean_ctor_get(x_796, 0);
lean_inc(x_810);
x_811 = lean_ctor_get(x_796, 1);
lean_inc(x_811);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 x_812 = x_796;
} else {
 lean_dec_ref(x_796);
 x_812 = lean_box(0);
}
lean_inc(x_789);
x_813 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_811, x_1, x_789);
if (lean_is_scalar(x_812)) {
 x_814 = lean_alloc_ctor(0, 2, 0);
} else {
 x_814 = x_812;
}
lean_ctor_set(x_814, 0, x_810);
lean_ctor_set(x_814, 1, x_813);
if (lean_is_scalar(x_809)) {
 x_815 = lean_alloc_ctor(0, 7, 0);
} else {
 x_815 = x_809;
}
lean_ctor_set(x_815, 0, x_814);
lean_ctor_set(x_815, 1, x_803);
lean_ctor_set(x_815, 2, x_804);
lean_ctor_set(x_815, 3, x_805);
lean_ctor_set(x_815, 4, x_806);
lean_ctor_set(x_815, 5, x_807);
lean_ctor_set(x_815, 6, x_808);
if (lean_is_scalar(x_802)) {
 x_816 = lean_alloc_ctor(0, 5, 0);
} else {
 x_816 = x_802;
}
lean_ctor_set(x_816, 0, x_798);
lean_ctor_set(x_816, 1, x_815);
lean_ctor_set(x_816, 2, x_799);
lean_ctor_set(x_816, 3, x_800);
lean_ctor_set(x_816, 4, x_801);
x_817 = lean_st_ref_set(x_3, x_816, x_797);
lean_dec(x_3);
x_818 = lean_ctor_get(x_817, 1);
lean_inc(x_818);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 lean_ctor_release(x_817, 1);
 x_819 = x_817;
} else {
 lean_dec_ref(x_817);
 x_819 = lean_box(0);
}
if (lean_is_scalar(x_819)) {
 x_820 = lean_alloc_ctor(0, 2, 0);
} else {
 x_820 = x_819;
}
lean_ctor_set(x_820, 0, x_789);
lean_ctor_set(x_820, 1, x_818);
return x_820;
}
else
{
lean_object* x_821; 
lean_dec(x_3);
lean_dec(x_1);
x_821 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_821, 0, x_789);
lean_ctor_set(x_821, 1, x_790);
return x_821;
}
}
else
{
lean_object* x_822; 
lean_dec(x_3);
lean_dec(x_1);
x_822 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_822, 0, x_789);
lean_ctor_set(x_822, 1, x_790);
return x_822;
}
}
}
else
{
uint8_t x_823; 
lean_dec(x_3);
lean_dec(x_1);
x_823 = !lean_is_exclusive(x_720);
if (x_823 == 0)
{
return x_720;
}
else
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; 
x_824 = lean_ctor_get(x_720, 0);
x_825 = lean_ctor_get(x_720, 1);
lean_inc(x_825);
lean_inc(x_824);
lean_dec(x_720);
x_826 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_826, 0, x_824);
lean_ctor_set(x_826, 1, x_825);
return x_826;
}
}
}
else
{
lean_object* x_827; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_827 = lean_ctor_get(x_717, 0);
lean_inc(x_827);
lean_dec(x_717);
lean_ctor_set(x_710, 0, x_827);
return x_710;
}
}
else
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_828 = lean_ctor_get(x_710, 0);
x_829 = lean_ctor_get(x_710, 1);
lean_inc(x_829);
lean_inc(x_828);
lean_dec(x_710);
x_830 = lean_ctor_get(x_828, 1);
lean_inc(x_830);
lean_dec(x_828);
x_831 = lean_ctor_get(x_830, 0);
lean_inc(x_831);
lean_dec(x_830);
x_832 = lean_ctor_get(x_831, 1);
lean_inc(x_832);
lean_dec(x_831);
x_833 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_832, x_1);
if (lean_obj_tag(x_833) == 0)
{
lean_object* x_834; uint8_t x_835; lean_object* x_836; 
x_834 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1;
x_835 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_836 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_1, x_834, x_835, x_2, x_3, x_4, x_5, x_829);
if (lean_obj_tag(x_836) == 0)
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; uint8_t x_840; 
x_837 = lean_ctor_get(x_836, 0);
lean_inc(x_837);
x_838 = lean_ctor_get(x_836, 1);
lean_inc(x_838);
if (lean_is_exclusive(x_836)) {
 lean_ctor_release(x_836, 0);
 lean_ctor_release(x_836, 1);
 x_839 = x_836;
} else {
 lean_dec_ref(x_836);
 x_839 = lean_box(0);
}
x_840 = l_Lean_Expr_hasMVar(x_1);
if (x_840 == 0)
{
uint8_t x_841; 
x_841 = l_Lean_Expr_hasMVar(x_837);
if (x_841 == 0)
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
lean_dec(x_839);
x_842 = lean_st_ref_take(x_3, x_838);
x_843 = lean_ctor_get(x_842, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_843, 1);
lean_inc(x_844);
x_845 = lean_ctor_get(x_844, 0);
lean_inc(x_845);
x_846 = lean_ctor_get(x_842, 1);
lean_inc(x_846);
lean_dec(x_842);
x_847 = lean_ctor_get(x_843, 0);
lean_inc(x_847);
x_848 = lean_ctor_get(x_843, 2);
lean_inc(x_848);
x_849 = lean_ctor_get(x_843, 3);
lean_inc(x_849);
x_850 = lean_ctor_get(x_843, 4);
lean_inc(x_850);
if (lean_is_exclusive(x_843)) {
 lean_ctor_release(x_843, 0);
 lean_ctor_release(x_843, 1);
 lean_ctor_release(x_843, 2);
 lean_ctor_release(x_843, 3);
 lean_ctor_release(x_843, 4);
 x_851 = x_843;
} else {
 lean_dec_ref(x_843);
 x_851 = lean_box(0);
}
x_852 = lean_ctor_get(x_844, 1);
lean_inc(x_852);
x_853 = lean_ctor_get(x_844, 2);
lean_inc(x_853);
x_854 = lean_ctor_get(x_844, 3);
lean_inc(x_854);
x_855 = lean_ctor_get(x_844, 4);
lean_inc(x_855);
x_856 = lean_ctor_get(x_844, 5);
lean_inc(x_856);
x_857 = lean_ctor_get(x_844, 6);
lean_inc(x_857);
if (lean_is_exclusive(x_844)) {
 lean_ctor_release(x_844, 0);
 lean_ctor_release(x_844, 1);
 lean_ctor_release(x_844, 2);
 lean_ctor_release(x_844, 3);
 lean_ctor_release(x_844, 4);
 lean_ctor_release(x_844, 5);
 lean_ctor_release(x_844, 6);
 x_858 = x_844;
} else {
 lean_dec_ref(x_844);
 x_858 = lean_box(0);
}
x_859 = lean_ctor_get(x_845, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_845, 1);
lean_inc(x_860);
if (lean_is_exclusive(x_845)) {
 lean_ctor_release(x_845, 0);
 lean_ctor_release(x_845, 1);
 x_861 = x_845;
} else {
 lean_dec_ref(x_845);
 x_861 = lean_box(0);
}
lean_inc(x_837);
x_862 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_860, x_1, x_837);
if (lean_is_scalar(x_861)) {
 x_863 = lean_alloc_ctor(0, 2, 0);
} else {
 x_863 = x_861;
}
lean_ctor_set(x_863, 0, x_859);
lean_ctor_set(x_863, 1, x_862);
if (lean_is_scalar(x_858)) {
 x_864 = lean_alloc_ctor(0, 7, 0);
} else {
 x_864 = x_858;
}
lean_ctor_set(x_864, 0, x_863);
lean_ctor_set(x_864, 1, x_852);
lean_ctor_set(x_864, 2, x_853);
lean_ctor_set(x_864, 3, x_854);
lean_ctor_set(x_864, 4, x_855);
lean_ctor_set(x_864, 5, x_856);
lean_ctor_set(x_864, 6, x_857);
if (lean_is_scalar(x_851)) {
 x_865 = lean_alloc_ctor(0, 5, 0);
} else {
 x_865 = x_851;
}
lean_ctor_set(x_865, 0, x_847);
lean_ctor_set(x_865, 1, x_864);
lean_ctor_set(x_865, 2, x_848);
lean_ctor_set(x_865, 3, x_849);
lean_ctor_set(x_865, 4, x_850);
x_866 = lean_st_ref_set(x_3, x_865, x_846);
lean_dec(x_3);
x_867 = lean_ctor_get(x_866, 1);
lean_inc(x_867);
if (lean_is_exclusive(x_866)) {
 lean_ctor_release(x_866, 0);
 lean_ctor_release(x_866, 1);
 x_868 = x_866;
} else {
 lean_dec_ref(x_866);
 x_868 = lean_box(0);
}
if (lean_is_scalar(x_868)) {
 x_869 = lean_alloc_ctor(0, 2, 0);
} else {
 x_869 = x_868;
}
lean_ctor_set(x_869, 0, x_837);
lean_ctor_set(x_869, 1, x_867);
return x_869;
}
else
{
lean_object* x_870; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_839)) {
 x_870 = lean_alloc_ctor(0, 2, 0);
} else {
 x_870 = x_839;
}
lean_ctor_set(x_870, 0, x_837);
lean_ctor_set(x_870, 1, x_838);
return x_870;
}
}
else
{
lean_object* x_871; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_839)) {
 x_871 = lean_alloc_ctor(0, 2, 0);
} else {
 x_871 = x_839;
}
lean_ctor_set(x_871, 0, x_837);
lean_ctor_set(x_871, 1, x_838);
return x_871;
}
}
else
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
lean_dec(x_3);
lean_dec(x_1);
x_872 = lean_ctor_get(x_836, 0);
lean_inc(x_872);
x_873 = lean_ctor_get(x_836, 1);
lean_inc(x_873);
if (lean_is_exclusive(x_836)) {
 lean_ctor_release(x_836, 0);
 lean_ctor_release(x_836, 1);
 x_874 = x_836;
} else {
 lean_dec_ref(x_836);
 x_874 = lean_box(0);
}
if (lean_is_scalar(x_874)) {
 x_875 = lean_alloc_ctor(1, 2, 0);
} else {
 x_875 = x_874;
}
lean_ctor_set(x_875, 0, x_872);
lean_ctor_set(x_875, 1, x_873);
return x_875;
}
}
else
{
lean_object* x_876; lean_object* x_877; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_876 = lean_ctor_get(x_833, 0);
lean_inc(x_876);
lean_dec(x_833);
x_877 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_877, 0, x_876);
lean_ctor_set(x_877, 1, x_829);
return x_877;
}
}
}
case 1:
{
lean_object* x_878; lean_object* x_879; uint8_t x_880; 
x_878 = lean_ctor_get(x_707, 1);
lean_inc(x_878);
lean_dec(x_707);
x_879 = lean_st_ref_get(x_3, x_878);
x_880 = !lean_is_exclusive(x_879);
if (x_880 == 0)
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; 
x_881 = lean_ctor_get(x_879, 0);
x_882 = lean_ctor_get(x_879, 1);
x_883 = lean_ctor_get(x_881, 1);
lean_inc(x_883);
lean_dec(x_881);
x_884 = lean_ctor_get(x_883, 0);
lean_inc(x_884);
lean_dec(x_883);
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
lean_dec(x_884);
x_886 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_885, x_1);
if (lean_obj_tag(x_886) == 0)
{
lean_object* x_887; uint8_t x_888; lean_object* x_889; 
lean_free_object(x_879);
x_887 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1;
x_888 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_889 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_1, x_887, x_888, x_2, x_3, x_4, x_5, x_882);
if (lean_obj_tag(x_889) == 0)
{
uint8_t x_890; 
x_890 = !lean_is_exclusive(x_889);
if (x_890 == 0)
{
lean_object* x_891; lean_object* x_892; uint8_t x_893; 
x_891 = lean_ctor_get(x_889, 0);
x_892 = lean_ctor_get(x_889, 1);
x_893 = l_Lean_Expr_hasMVar(x_1);
if (x_893 == 0)
{
uint8_t x_894; 
x_894 = l_Lean_Expr_hasMVar(x_891);
if (x_894 == 0)
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; uint8_t x_900; 
lean_free_object(x_889);
x_895 = lean_st_ref_take(x_3, x_892);
x_896 = lean_ctor_get(x_895, 0);
lean_inc(x_896);
x_897 = lean_ctor_get(x_896, 1);
lean_inc(x_897);
x_898 = lean_ctor_get(x_897, 0);
lean_inc(x_898);
x_899 = lean_ctor_get(x_895, 1);
lean_inc(x_899);
lean_dec(x_895);
x_900 = !lean_is_exclusive(x_896);
if (x_900 == 0)
{
lean_object* x_901; uint8_t x_902; 
x_901 = lean_ctor_get(x_896, 1);
lean_dec(x_901);
x_902 = !lean_is_exclusive(x_897);
if (x_902 == 0)
{
lean_object* x_903; uint8_t x_904; 
x_903 = lean_ctor_get(x_897, 0);
lean_dec(x_903);
x_904 = !lean_is_exclusive(x_898);
if (x_904 == 0)
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; uint8_t x_908; 
x_905 = lean_ctor_get(x_898, 0);
lean_inc(x_891);
x_906 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_905, x_1, x_891);
lean_ctor_set(x_898, 0, x_906);
x_907 = lean_st_ref_set(x_3, x_896, x_899);
lean_dec(x_3);
x_908 = !lean_is_exclusive(x_907);
if (x_908 == 0)
{
lean_object* x_909; 
x_909 = lean_ctor_get(x_907, 0);
lean_dec(x_909);
lean_ctor_set(x_907, 0, x_891);
return x_907;
}
else
{
lean_object* x_910; lean_object* x_911; 
x_910 = lean_ctor_get(x_907, 1);
lean_inc(x_910);
lean_dec(x_907);
x_911 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_911, 0, x_891);
lean_ctor_set(x_911, 1, x_910);
return x_911;
}
}
else
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; 
x_912 = lean_ctor_get(x_898, 0);
x_913 = lean_ctor_get(x_898, 1);
lean_inc(x_913);
lean_inc(x_912);
lean_dec(x_898);
lean_inc(x_891);
x_914 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_912, x_1, x_891);
x_915 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_915, 0, x_914);
lean_ctor_set(x_915, 1, x_913);
lean_ctor_set(x_897, 0, x_915);
x_916 = lean_st_ref_set(x_3, x_896, x_899);
lean_dec(x_3);
x_917 = lean_ctor_get(x_916, 1);
lean_inc(x_917);
if (lean_is_exclusive(x_916)) {
 lean_ctor_release(x_916, 0);
 lean_ctor_release(x_916, 1);
 x_918 = x_916;
} else {
 lean_dec_ref(x_916);
 x_918 = lean_box(0);
}
if (lean_is_scalar(x_918)) {
 x_919 = lean_alloc_ctor(0, 2, 0);
} else {
 x_919 = x_918;
}
lean_ctor_set(x_919, 0, x_891);
lean_ctor_set(x_919, 1, x_917);
return x_919;
}
}
else
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; 
x_920 = lean_ctor_get(x_897, 1);
x_921 = lean_ctor_get(x_897, 2);
x_922 = lean_ctor_get(x_897, 3);
x_923 = lean_ctor_get(x_897, 4);
x_924 = lean_ctor_get(x_897, 5);
x_925 = lean_ctor_get(x_897, 6);
lean_inc(x_925);
lean_inc(x_924);
lean_inc(x_923);
lean_inc(x_922);
lean_inc(x_921);
lean_inc(x_920);
lean_dec(x_897);
x_926 = lean_ctor_get(x_898, 0);
lean_inc(x_926);
x_927 = lean_ctor_get(x_898, 1);
lean_inc(x_927);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 lean_ctor_release(x_898, 1);
 x_928 = x_898;
} else {
 lean_dec_ref(x_898);
 x_928 = lean_box(0);
}
lean_inc(x_891);
x_929 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_926, x_1, x_891);
if (lean_is_scalar(x_928)) {
 x_930 = lean_alloc_ctor(0, 2, 0);
} else {
 x_930 = x_928;
}
lean_ctor_set(x_930, 0, x_929);
lean_ctor_set(x_930, 1, x_927);
x_931 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_931, 0, x_930);
lean_ctor_set(x_931, 1, x_920);
lean_ctor_set(x_931, 2, x_921);
lean_ctor_set(x_931, 3, x_922);
lean_ctor_set(x_931, 4, x_923);
lean_ctor_set(x_931, 5, x_924);
lean_ctor_set(x_931, 6, x_925);
lean_ctor_set(x_896, 1, x_931);
x_932 = lean_st_ref_set(x_3, x_896, x_899);
lean_dec(x_3);
x_933 = lean_ctor_get(x_932, 1);
lean_inc(x_933);
if (lean_is_exclusive(x_932)) {
 lean_ctor_release(x_932, 0);
 lean_ctor_release(x_932, 1);
 x_934 = x_932;
} else {
 lean_dec_ref(x_932);
 x_934 = lean_box(0);
}
if (lean_is_scalar(x_934)) {
 x_935 = lean_alloc_ctor(0, 2, 0);
} else {
 x_935 = x_934;
}
lean_ctor_set(x_935, 0, x_891);
lean_ctor_set(x_935, 1, x_933);
return x_935;
}
}
else
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; 
x_936 = lean_ctor_get(x_896, 0);
x_937 = lean_ctor_get(x_896, 2);
x_938 = lean_ctor_get(x_896, 3);
x_939 = lean_ctor_get(x_896, 4);
lean_inc(x_939);
lean_inc(x_938);
lean_inc(x_937);
lean_inc(x_936);
lean_dec(x_896);
x_940 = lean_ctor_get(x_897, 1);
lean_inc(x_940);
x_941 = lean_ctor_get(x_897, 2);
lean_inc(x_941);
x_942 = lean_ctor_get(x_897, 3);
lean_inc(x_942);
x_943 = lean_ctor_get(x_897, 4);
lean_inc(x_943);
x_944 = lean_ctor_get(x_897, 5);
lean_inc(x_944);
x_945 = lean_ctor_get(x_897, 6);
lean_inc(x_945);
if (lean_is_exclusive(x_897)) {
 lean_ctor_release(x_897, 0);
 lean_ctor_release(x_897, 1);
 lean_ctor_release(x_897, 2);
 lean_ctor_release(x_897, 3);
 lean_ctor_release(x_897, 4);
 lean_ctor_release(x_897, 5);
 lean_ctor_release(x_897, 6);
 x_946 = x_897;
} else {
 lean_dec_ref(x_897);
 x_946 = lean_box(0);
}
x_947 = lean_ctor_get(x_898, 0);
lean_inc(x_947);
x_948 = lean_ctor_get(x_898, 1);
lean_inc(x_948);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 lean_ctor_release(x_898, 1);
 x_949 = x_898;
} else {
 lean_dec_ref(x_898);
 x_949 = lean_box(0);
}
lean_inc(x_891);
x_950 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_947, x_1, x_891);
if (lean_is_scalar(x_949)) {
 x_951 = lean_alloc_ctor(0, 2, 0);
} else {
 x_951 = x_949;
}
lean_ctor_set(x_951, 0, x_950);
lean_ctor_set(x_951, 1, x_948);
if (lean_is_scalar(x_946)) {
 x_952 = lean_alloc_ctor(0, 7, 0);
} else {
 x_952 = x_946;
}
lean_ctor_set(x_952, 0, x_951);
lean_ctor_set(x_952, 1, x_940);
lean_ctor_set(x_952, 2, x_941);
lean_ctor_set(x_952, 3, x_942);
lean_ctor_set(x_952, 4, x_943);
lean_ctor_set(x_952, 5, x_944);
lean_ctor_set(x_952, 6, x_945);
x_953 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_953, 0, x_936);
lean_ctor_set(x_953, 1, x_952);
lean_ctor_set(x_953, 2, x_937);
lean_ctor_set(x_953, 3, x_938);
lean_ctor_set(x_953, 4, x_939);
x_954 = lean_st_ref_set(x_3, x_953, x_899);
lean_dec(x_3);
x_955 = lean_ctor_get(x_954, 1);
lean_inc(x_955);
if (lean_is_exclusive(x_954)) {
 lean_ctor_release(x_954, 0);
 lean_ctor_release(x_954, 1);
 x_956 = x_954;
} else {
 lean_dec_ref(x_954);
 x_956 = lean_box(0);
}
if (lean_is_scalar(x_956)) {
 x_957 = lean_alloc_ctor(0, 2, 0);
} else {
 x_957 = x_956;
}
lean_ctor_set(x_957, 0, x_891);
lean_ctor_set(x_957, 1, x_955);
return x_957;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_889;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_889;
}
}
else
{
lean_object* x_958; lean_object* x_959; uint8_t x_960; 
x_958 = lean_ctor_get(x_889, 0);
x_959 = lean_ctor_get(x_889, 1);
lean_inc(x_959);
lean_inc(x_958);
lean_dec(x_889);
x_960 = l_Lean_Expr_hasMVar(x_1);
if (x_960 == 0)
{
uint8_t x_961; 
x_961 = l_Lean_Expr_hasMVar(x_958);
if (x_961 == 0)
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; 
x_962 = lean_st_ref_take(x_3, x_959);
x_963 = lean_ctor_get(x_962, 0);
lean_inc(x_963);
x_964 = lean_ctor_get(x_963, 1);
lean_inc(x_964);
x_965 = lean_ctor_get(x_964, 0);
lean_inc(x_965);
x_966 = lean_ctor_get(x_962, 1);
lean_inc(x_966);
lean_dec(x_962);
x_967 = lean_ctor_get(x_963, 0);
lean_inc(x_967);
x_968 = lean_ctor_get(x_963, 2);
lean_inc(x_968);
x_969 = lean_ctor_get(x_963, 3);
lean_inc(x_969);
x_970 = lean_ctor_get(x_963, 4);
lean_inc(x_970);
if (lean_is_exclusive(x_963)) {
 lean_ctor_release(x_963, 0);
 lean_ctor_release(x_963, 1);
 lean_ctor_release(x_963, 2);
 lean_ctor_release(x_963, 3);
 lean_ctor_release(x_963, 4);
 x_971 = x_963;
} else {
 lean_dec_ref(x_963);
 x_971 = lean_box(0);
}
x_972 = lean_ctor_get(x_964, 1);
lean_inc(x_972);
x_973 = lean_ctor_get(x_964, 2);
lean_inc(x_973);
x_974 = lean_ctor_get(x_964, 3);
lean_inc(x_974);
x_975 = lean_ctor_get(x_964, 4);
lean_inc(x_975);
x_976 = lean_ctor_get(x_964, 5);
lean_inc(x_976);
x_977 = lean_ctor_get(x_964, 6);
lean_inc(x_977);
if (lean_is_exclusive(x_964)) {
 lean_ctor_release(x_964, 0);
 lean_ctor_release(x_964, 1);
 lean_ctor_release(x_964, 2);
 lean_ctor_release(x_964, 3);
 lean_ctor_release(x_964, 4);
 lean_ctor_release(x_964, 5);
 lean_ctor_release(x_964, 6);
 x_978 = x_964;
} else {
 lean_dec_ref(x_964);
 x_978 = lean_box(0);
}
x_979 = lean_ctor_get(x_965, 0);
lean_inc(x_979);
x_980 = lean_ctor_get(x_965, 1);
lean_inc(x_980);
if (lean_is_exclusive(x_965)) {
 lean_ctor_release(x_965, 0);
 lean_ctor_release(x_965, 1);
 x_981 = x_965;
} else {
 lean_dec_ref(x_965);
 x_981 = lean_box(0);
}
lean_inc(x_958);
x_982 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_979, x_1, x_958);
if (lean_is_scalar(x_981)) {
 x_983 = lean_alloc_ctor(0, 2, 0);
} else {
 x_983 = x_981;
}
lean_ctor_set(x_983, 0, x_982);
lean_ctor_set(x_983, 1, x_980);
if (lean_is_scalar(x_978)) {
 x_984 = lean_alloc_ctor(0, 7, 0);
} else {
 x_984 = x_978;
}
lean_ctor_set(x_984, 0, x_983);
lean_ctor_set(x_984, 1, x_972);
lean_ctor_set(x_984, 2, x_973);
lean_ctor_set(x_984, 3, x_974);
lean_ctor_set(x_984, 4, x_975);
lean_ctor_set(x_984, 5, x_976);
lean_ctor_set(x_984, 6, x_977);
if (lean_is_scalar(x_971)) {
 x_985 = lean_alloc_ctor(0, 5, 0);
} else {
 x_985 = x_971;
}
lean_ctor_set(x_985, 0, x_967);
lean_ctor_set(x_985, 1, x_984);
lean_ctor_set(x_985, 2, x_968);
lean_ctor_set(x_985, 3, x_969);
lean_ctor_set(x_985, 4, x_970);
x_986 = lean_st_ref_set(x_3, x_985, x_966);
lean_dec(x_3);
x_987 = lean_ctor_get(x_986, 1);
lean_inc(x_987);
if (lean_is_exclusive(x_986)) {
 lean_ctor_release(x_986, 0);
 lean_ctor_release(x_986, 1);
 x_988 = x_986;
} else {
 lean_dec_ref(x_986);
 x_988 = lean_box(0);
}
if (lean_is_scalar(x_988)) {
 x_989 = lean_alloc_ctor(0, 2, 0);
} else {
 x_989 = x_988;
}
lean_ctor_set(x_989, 0, x_958);
lean_ctor_set(x_989, 1, x_987);
return x_989;
}
else
{
lean_object* x_990; 
lean_dec(x_3);
lean_dec(x_1);
x_990 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_990, 0, x_958);
lean_ctor_set(x_990, 1, x_959);
return x_990;
}
}
else
{
lean_object* x_991; 
lean_dec(x_3);
lean_dec(x_1);
x_991 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_991, 0, x_958);
lean_ctor_set(x_991, 1, x_959);
return x_991;
}
}
}
else
{
uint8_t x_992; 
lean_dec(x_3);
lean_dec(x_1);
x_992 = !lean_is_exclusive(x_889);
if (x_992 == 0)
{
return x_889;
}
else
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; 
x_993 = lean_ctor_get(x_889, 0);
x_994 = lean_ctor_get(x_889, 1);
lean_inc(x_994);
lean_inc(x_993);
lean_dec(x_889);
x_995 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_995, 0, x_993);
lean_ctor_set(x_995, 1, x_994);
return x_995;
}
}
}
else
{
lean_object* x_996; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_996 = lean_ctor_get(x_886, 0);
lean_inc(x_996);
lean_dec(x_886);
lean_ctor_set(x_879, 0, x_996);
return x_879;
}
}
else
{
lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
x_997 = lean_ctor_get(x_879, 0);
x_998 = lean_ctor_get(x_879, 1);
lean_inc(x_998);
lean_inc(x_997);
lean_dec(x_879);
x_999 = lean_ctor_get(x_997, 1);
lean_inc(x_999);
lean_dec(x_997);
x_1000 = lean_ctor_get(x_999, 0);
lean_inc(x_1000);
lean_dec(x_999);
x_1001 = lean_ctor_get(x_1000, 0);
lean_inc(x_1001);
lean_dec(x_1000);
x_1002 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_1001, x_1);
if (lean_obj_tag(x_1002) == 0)
{
lean_object* x_1003; uint8_t x_1004; lean_object* x_1005; 
x_1003 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1;
x_1004 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_1005 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_1, x_1003, x_1004, x_2, x_3, x_4, x_5, x_998);
if (lean_obj_tag(x_1005) == 0)
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; uint8_t x_1009; 
x_1006 = lean_ctor_get(x_1005, 0);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_1005, 1);
lean_inc(x_1007);
if (lean_is_exclusive(x_1005)) {
 lean_ctor_release(x_1005, 0);
 lean_ctor_release(x_1005, 1);
 x_1008 = x_1005;
} else {
 lean_dec_ref(x_1005);
 x_1008 = lean_box(0);
}
x_1009 = l_Lean_Expr_hasMVar(x_1);
if (x_1009 == 0)
{
uint8_t x_1010; 
x_1010 = l_Lean_Expr_hasMVar(x_1006);
if (x_1010 == 0)
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
lean_dec(x_1008);
x_1011 = lean_st_ref_take(x_3, x_1007);
x_1012 = lean_ctor_get(x_1011, 0);
lean_inc(x_1012);
x_1013 = lean_ctor_get(x_1012, 1);
lean_inc(x_1013);
x_1014 = lean_ctor_get(x_1013, 0);
lean_inc(x_1014);
x_1015 = lean_ctor_get(x_1011, 1);
lean_inc(x_1015);
lean_dec(x_1011);
x_1016 = lean_ctor_get(x_1012, 0);
lean_inc(x_1016);
x_1017 = lean_ctor_get(x_1012, 2);
lean_inc(x_1017);
x_1018 = lean_ctor_get(x_1012, 3);
lean_inc(x_1018);
x_1019 = lean_ctor_get(x_1012, 4);
lean_inc(x_1019);
if (lean_is_exclusive(x_1012)) {
 lean_ctor_release(x_1012, 0);
 lean_ctor_release(x_1012, 1);
 lean_ctor_release(x_1012, 2);
 lean_ctor_release(x_1012, 3);
 lean_ctor_release(x_1012, 4);
 x_1020 = x_1012;
} else {
 lean_dec_ref(x_1012);
 x_1020 = lean_box(0);
}
x_1021 = lean_ctor_get(x_1013, 1);
lean_inc(x_1021);
x_1022 = lean_ctor_get(x_1013, 2);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_1013, 3);
lean_inc(x_1023);
x_1024 = lean_ctor_get(x_1013, 4);
lean_inc(x_1024);
x_1025 = lean_ctor_get(x_1013, 5);
lean_inc(x_1025);
x_1026 = lean_ctor_get(x_1013, 6);
lean_inc(x_1026);
if (lean_is_exclusive(x_1013)) {
 lean_ctor_release(x_1013, 0);
 lean_ctor_release(x_1013, 1);
 lean_ctor_release(x_1013, 2);
 lean_ctor_release(x_1013, 3);
 lean_ctor_release(x_1013, 4);
 lean_ctor_release(x_1013, 5);
 lean_ctor_release(x_1013, 6);
 x_1027 = x_1013;
} else {
 lean_dec_ref(x_1013);
 x_1027 = lean_box(0);
}
x_1028 = lean_ctor_get(x_1014, 0);
lean_inc(x_1028);
x_1029 = lean_ctor_get(x_1014, 1);
lean_inc(x_1029);
if (lean_is_exclusive(x_1014)) {
 lean_ctor_release(x_1014, 0);
 lean_ctor_release(x_1014, 1);
 x_1030 = x_1014;
} else {
 lean_dec_ref(x_1014);
 x_1030 = lean_box(0);
}
lean_inc(x_1006);
x_1031 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1028, x_1, x_1006);
if (lean_is_scalar(x_1030)) {
 x_1032 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1032 = x_1030;
}
lean_ctor_set(x_1032, 0, x_1031);
lean_ctor_set(x_1032, 1, x_1029);
if (lean_is_scalar(x_1027)) {
 x_1033 = lean_alloc_ctor(0, 7, 0);
} else {
 x_1033 = x_1027;
}
lean_ctor_set(x_1033, 0, x_1032);
lean_ctor_set(x_1033, 1, x_1021);
lean_ctor_set(x_1033, 2, x_1022);
lean_ctor_set(x_1033, 3, x_1023);
lean_ctor_set(x_1033, 4, x_1024);
lean_ctor_set(x_1033, 5, x_1025);
lean_ctor_set(x_1033, 6, x_1026);
if (lean_is_scalar(x_1020)) {
 x_1034 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1034 = x_1020;
}
lean_ctor_set(x_1034, 0, x_1016);
lean_ctor_set(x_1034, 1, x_1033);
lean_ctor_set(x_1034, 2, x_1017);
lean_ctor_set(x_1034, 3, x_1018);
lean_ctor_set(x_1034, 4, x_1019);
x_1035 = lean_st_ref_set(x_3, x_1034, x_1015);
lean_dec(x_3);
x_1036 = lean_ctor_get(x_1035, 1);
lean_inc(x_1036);
if (lean_is_exclusive(x_1035)) {
 lean_ctor_release(x_1035, 0);
 lean_ctor_release(x_1035, 1);
 x_1037 = x_1035;
} else {
 lean_dec_ref(x_1035);
 x_1037 = lean_box(0);
}
if (lean_is_scalar(x_1037)) {
 x_1038 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1038 = x_1037;
}
lean_ctor_set(x_1038, 0, x_1006);
lean_ctor_set(x_1038, 1, x_1036);
return x_1038;
}
else
{
lean_object* x_1039; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_1008)) {
 x_1039 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1039 = x_1008;
}
lean_ctor_set(x_1039, 0, x_1006);
lean_ctor_set(x_1039, 1, x_1007);
return x_1039;
}
}
else
{
lean_object* x_1040; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_1008)) {
 x_1040 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1040 = x_1008;
}
lean_ctor_set(x_1040, 0, x_1006);
lean_ctor_set(x_1040, 1, x_1007);
return x_1040;
}
}
else
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
lean_dec(x_3);
lean_dec(x_1);
x_1041 = lean_ctor_get(x_1005, 0);
lean_inc(x_1041);
x_1042 = lean_ctor_get(x_1005, 1);
lean_inc(x_1042);
if (lean_is_exclusive(x_1005)) {
 lean_ctor_release(x_1005, 0);
 lean_ctor_release(x_1005, 1);
 x_1043 = x_1005;
} else {
 lean_dec_ref(x_1005);
 x_1043 = lean_box(0);
}
if (lean_is_scalar(x_1043)) {
 x_1044 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1044 = x_1043;
}
lean_ctor_set(x_1044, 0, x_1041);
lean_ctor_set(x_1044, 1, x_1042);
return x_1044;
}
}
else
{
lean_object* x_1045; lean_object* x_1046; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1045 = lean_ctor_get(x_1002, 0);
lean_inc(x_1045);
lean_dec(x_1002);
x_1046 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1046, 0, x_1045);
lean_ctor_set(x_1046, 1, x_998);
return x_1046;
}
}
}
default: 
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; 
lean_dec(x_708);
lean_dec(x_1);
x_1047 = lean_ctor_get(x_707, 1);
lean_inc(x_1047);
lean_dec(x_707);
x_1048 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3;
x_1049 = l_panic___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__8(x_1048, x_2, x_3, x_4, x_5, x_1047);
return x_1049;
}
}
}
case 9:
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1050 = lean_ctor_get(x_1, 0);
lean_inc(x_1050);
lean_dec(x_1);
x_1051 = l_Lean_Literal_type(x_1050);
lean_dec(x_1050);
x_1052 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1052, 0, x_1051);
lean_ctor_set(x_1052, 1, x_6);
return x_1052;
}
case 10:
{
lean_object* x_1053; 
x_1053 = lean_ctor_get(x_1, 1);
lean_inc(x_1053);
lean_dec(x_1);
x_1 = x_1053;
goto _start;
}
case 11:
{
lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; 
x_1055 = lean_ctor_get(x_1, 0);
lean_inc(x_1055);
x_1056 = lean_ctor_get(x_1, 1);
lean_inc(x_1056);
x_1057 = lean_ctor_get(x_1, 2);
lean_inc(x_1057);
x_1058 = l_Lean_Meta_getTransparency(x_2, x_3, x_4, x_5, x_6);
x_1059 = lean_ctor_get(x_1058, 0);
lean_inc(x_1059);
switch (lean_obj_tag(x_1059)) {
case 0:
{
lean_object* x_1060; lean_object* x_1061; uint8_t x_1062; 
x_1060 = lean_ctor_get(x_1058, 1);
lean_inc(x_1060);
lean_dec(x_1058);
x_1061 = lean_st_ref_get(x_3, x_1060);
x_1062 = !lean_is_exclusive(x_1061);
if (x_1062 == 0)
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; 
x_1063 = lean_ctor_get(x_1061, 0);
x_1064 = lean_ctor_get(x_1061, 1);
x_1065 = lean_ctor_get(x_1063, 1);
lean_inc(x_1065);
lean_dec(x_1063);
x_1066 = lean_ctor_get(x_1065, 0);
lean_inc(x_1066);
lean_dec(x_1065);
x_1067 = lean_ctor_get(x_1066, 1);
lean_inc(x_1067);
lean_dec(x_1066);
x_1068 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_1067, x_1);
if (lean_obj_tag(x_1068) == 0)
{
lean_object* x_1069; 
lean_free_object(x_1061);
lean_inc(x_3);
x_1069 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(x_1055, x_1056, x_1057, x_2, x_3, x_4, x_5, x_1064);
if (lean_obj_tag(x_1069) == 0)
{
uint8_t x_1070; 
x_1070 = !lean_is_exclusive(x_1069);
if (x_1070 == 0)
{
lean_object* x_1071; lean_object* x_1072; uint8_t x_1073; 
x_1071 = lean_ctor_get(x_1069, 0);
x_1072 = lean_ctor_get(x_1069, 1);
x_1073 = l_Lean_Expr_hasMVar(x_1);
if (x_1073 == 0)
{
uint8_t x_1074; 
x_1074 = l_Lean_Expr_hasMVar(x_1071);
if (x_1074 == 0)
{
lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; uint8_t x_1080; 
lean_free_object(x_1069);
x_1075 = lean_st_ref_take(x_3, x_1072);
x_1076 = lean_ctor_get(x_1075, 0);
lean_inc(x_1076);
x_1077 = lean_ctor_get(x_1076, 1);
lean_inc(x_1077);
x_1078 = lean_ctor_get(x_1077, 0);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1075, 1);
lean_inc(x_1079);
lean_dec(x_1075);
x_1080 = !lean_is_exclusive(x_1076);
if (x_1080 == 0)
{
lean_object* x_1081; uint8_t x_1082; 
x_1081 = lean_ctor_get(x_1076, 1);
lean_dec(x_1081);
x_1082 = !lean_is_exclusive(x_1077);
if (x_1082 == 0)
{
lean_object* x_1083; uint8_t x_1084; 
x_1083 = lean_ctor_get(x_1077, 0);
lean_dec(x_1083);
x_1084 = !lean_is_exclusive(x_1078);
if (x_1084 == 0)
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; uint8_t x_1088; 
x_1085 = lean_ctor_get(x_1078, 1);
lean_inc(x_1071);
x_1086 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1085, x_1, x_1071);
lean_ctor_set(x_1078, 1, x_1086);
x_1087 = lean_st_ref_set(x_3, x_1076, x_1079);
lean_dec(x_3);
x_1088 = !lean_is_exclusive(x_1087);
if (x_1088 == 0)
{
lean_object* x_1089; 
x_1089 = lean_ctor_get(x_1087, 0);
lean_dec(x_1089);
lean_ctor_set(x_1087, 0, x_1071);
return x_1087;
}
else
{
lean_object* x_1090; lean_object* x_1091; 
x_1090 = lean_ctor_get(x_1087, 1);
lean_inc(x_1090);
lean_dec(x_1087);
x_1091 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1091, 0, x_1071);
lean_ctor_set(x_1091, 1, x_1090);
return x_1091;
}
}
else
{
lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; 
x_1092 = lean_ctor_get(x_1078, 0);
x_1093 = lean_ctor_get(x_1078, 1);
lean_inc(x_1093);
lean_inc(x_1092);
lean_dec(x_1078);
lean_inc(x_1071);
x_1094 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1093, x_1, x_1071);
x_1095 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1095, 0, x_1092);
lean_ctor_set(x_1095, 1, x_1094);
lean_ctor_set(x_1077, 0, x_1095);
x_1096 = lean_st_ref_set(x_3, x_1076, x_1079);
lean_dec(x_3);
x_1097 = lean_ctor_get(x_1096, 1);
lean_inc(x_1097);
if (lean_is_exclusive(x_1096)) {
 lean_ctor_release(x_1096, 0);
 lean_ctor_release(x_1096, 1);
 x_1098 = x_1096;
} else {
 lean_dec_ref(x_1096);
 x_1098 = lean_box(0);
}
if (lean_is_scalar(x_1098)) {
 x_1099 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1099 = x_1098;
}
lean_ctor_set(x_1099, 0, x_1071);
lean_ctor_set(x_1099, 1, x_1097);
return x_1099;
}
}
else
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; 
x_1100 = lean_ctor_get(x_1077, 1);
x_1101 = lean_ctor_get(x_1077, 2);
x_1102 = lean_ctor_get(x_1077, 3);
x_1103 = lean_ctor_get(x_1077, 4);
x_1104 = lean_ctor_get(x_1077, 5);
x_1105 = lean_ctor_get(x_1077, 6);
lean_inc(x_1105);
lean_inc(x_1104);
lean_inc(x_1103);
lean_inc(x_1102);
lean_inc(x_1101);
lean_inc(x_1100);
lean_dec(x_1077);
x_1106 = lean_ctor_get(x_1078, 0);
lean_inc(x_1106);
x_1107 = lean_ctor_get(x_1078, 1);
lean_inc(x_1107);
if (lean_is_exclusive(x_1078)) {
 lean_ctor_release(x_1078, 0);
 lean_ctor_release(x_1078, 1);
 x_1108 = x_1078;
} else {
 lean_dec_ref(x_1078);
 x_1108 = lean_box(0);
}
lean_inc(x_1071);
x_1109 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1107, x_1, x_1071);
if (lean_is_scalar(x_1108)) {
 x_1110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1110 = x_1108;
}
lean_ctor_set(x_1110, 0, x_1106);
lean_ctor_set(x_1110, 1, x_1109);
x_1111 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_1111, 0, x_1110);
lean_ctor_set(x_1111, 1, x_1100);
lean_ctor_set(x_1111, 2, x_1101);
lean_ctor_set(x_1111, 3, x_1102);
lean_ctor_set(x_1111, 4, x_1103);
lean_ctor_set(x_1111, 5, x_1104);
lean_ctor_set(x_1111, 6, x_1105);
lean_ctor_set(x_1076, 1, x_1111);
x_1112 = lean_st_ref_set(x_3, x_1076, x_1079);
lean_dec(x_3);
x_1113 = lean_ctor_get(x_1112, 1);
lean_inc(x_1113);
if (lean_is_exclusive(x_1112)) {
 lean_ctor_release(x_1112, 0);
 lean_ctor_release(x_1112, 1);
 x_1114 = x_1112;
} else {
 lean_dec_ref(x_1112);
 x_1114 = lean_box(0);
}
if (lean_is_scalar(x_1114)) {
 x_1115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1115 = x_1114;
}
lean_ctor_set(x_1115, 0, x_1071);
lean_ctor_set(x_1115, 1, x_1113);
return x_1115;
}
}
else
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; 
x_1116 = lean_ctor_get(x_1076, 0);
x_1117 = lean_ctor_get(x_1076, 2);
x_1118 = lean_ctor_get(x_1076, 3);
x_1119 = lean_ctor_get(x_1076, 4);
lean_inc(x_1119);
lean_inc(x_1118);
lean_inc(x_1117);
lean_inc(x_1116);
lean_dec(x_1076);
x_1120 = lean_ctor_get(x_1077, 1);
lean_inc(x_1120);
x_1121 = lean_ctor_get(x_1077, 2);
lean_inc(x_1121);
x_1122 = lean_ctor_get(x_1077, 3);
lean_inc(x_1122);
x_1123 = lean_ctor_get(x_1077, 4);
lean_inc(x_1123);
x_1124 = lean_ctor_get(x_1077, 5);
lean_inc(x_1124);
x_1125 = lean_ctor_get(x_1077, 6);
lean_inc(x_1125);
if (lean_is_exclusive(x_1077)) {
 lean_ctor_release(x_1077, 0);
 lean_ctor_release(x_1077, 1);
 lean_ctor_release(x_1077, 2);
 lean_ctor_release(x_1077, 3);
 lean_ctor_release(x_1077, 4);
 lean_ctor_release(x_1077, 5);
 lean_ctor_release(x_1077, 6);
 x_1126 = x_1077;
} else {
 lean_dec_ref(x_1077);
 x_1126 = lean_box(0);
}
x_1127 = lean_ctor_get(x_1078, 0);
lean_inc(x_1127);
x_1128 = lean_ctor_get(x_1078, 1);
lean_inc(x_1128);
if (lean_is_exclusive(x_1078)) {
 lean_ctor_release(x_1078, 0);
 lean_ctor_release(x_1078, 1);
 x_1129 = x_1078;
} else {
 lean_dec_ref(x_1078);
 x_1129 = lean_box(0);
}
lean_inc(x_1071);
x_1130 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1128, x_1, x_1071);
if (lean_is_scalar(x_1129)) {
 x_1131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1131 = x_1129;
}
lean_ctor_set(x_1131, 0, x_1127);
lean_ctor_set(x_1131, 1, x_1130);
if (lean_is_scalar(x_1126)) {
 x_1132 = lean_alloc_ctor(0, 7, 0);
} else {
 x_1132 = x_1126;
}
lean_ctor_set(x_1132, 0, x_1131);
lean_ctor_set(x_1132, 1, x_1120);
lean_ctor_set(x_1132, 2, x_1121);
lean_ctor_set(x_1132, 3, x_1122);
lean_ctor_set(x_1132, 4, x_1123);
lean_ctor_set(x_1132, 5, x_1124);
lean_ctor_set(x_1132, 6, x_1125);
x_1133 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1133, 0, x_1116);
lean_ctor_set(x_1133, 1, x_1132);
lean_ctor_set(x_1133, 2, x_1117);
lean_ctor_set(x_1133, 3, x_1118);
lean_ctor_set(x_1133, 4, x_1119);
x_1134 = lean_st_ref_set(x_3, x_1133, x_1079);
lean_dec(x_3);
x_1135 = lean_ctor_get(x_1134, 1);
lean_inc(x_1135);
if (lean_is_exclusive(x_1134)) {
 lean_ctor_release(x_1134, 0);
 lean_ctor_release(x_1134, 1);
 x_1136 = x_1134;
} else {
 lean_dec_ref(x_1134);
 x_1136 = lean_box(0);
}
if (lean_is_scalar(x_1136)) {
 x_1137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1137 = x_1136;
}
lean_ctor_set(x_1137, 0, x_1071);
lean_ctor_set(x_1137, 1, x_1135);
return x_1137;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_1069;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_1069;
}
}
else
{
lean_object* x_1138; lean_object* x_1139; uint8_t x_1140; 
x_1138 = lean_ctor_get(x_1069, 0);
x_1139 = lean_ctor_get(x_1069, 1);
lean_inc(x_1139);
lean_inc(x_1138);
lean_dec(x_1069);
x_1140 = l_Lean_Expr_hasMVar(x_1);
if (x_1140 == 0)
{
uint8_t x_1141; 
x_1141 = l_Lean_Expr_hasMVar(x_1138);
if (x_1141 == 0)
{
lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; 
x_1142 = lean_st_ref_take(x_3, x_1139);
x_1143 = lean_ctor_get(x_1142, 0);
lean_inc(x_1143);
x_1144 = lean_ctor_get(x_1143, 1);
lean_inc(x_1144);
x_1145 = lean_ctor_get(x_1144, 0);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_1142, 1);
lean_inc(x_1146);
lean_dec(x_1142);
x_1147 = lean_ctor_get(x_1143, 0);
lean_inc(x_1147);
x_1148 = lean_ctor_get(x_1143, 2);
lean_inc(x_1148);
x_1149 = lean_ctor_get(x_1143, 3);
lean_inc(x_1149);
x_1150 = lean_ctor_get(x_1143, 4);
lean_inc(x_1150);
if (lean_is_exclusive(x_1143)) {
 lean_ctor_release(x_1143, 0);
 lean_ctor_release(x_1143, 1);
 lean_ctor_release(x_1143, 2);
 lean_ctor_release(x_1143, 3);
 lean_ctor_release(x_1143, 4);
 x_1151 = x_1143;
} else {
 lean_dec_ref(x_1143);
 x_1151 = lean_box(0);
}
x_1152 = lean_ctor_get(x_1144, 1);
lean_inc(x_1152);
x_1153 = lean_ctor_get(x_1144, 2);
lean_inc(x_1153);
x_1154 = lean_ctor_get(x_1144, 3);
lean_inc(x_1154);
x_1155 = lean_ctor_get(x_1144, 4);
lean_inc(x_1155);
x_1156 = lean_ctor_get(x_1144, 5);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1144, 6);
lean_inc(x_1157);
if (lean_is_exclusive(x_1144)) {
 lean_ctor_release(x_1144, 0);
 lean_ctor_release(x_1144, 1);
 lean_ctor_release(x_1144, 2);
 lean_ctor_release(x_1144, 3);
 lean_ctor_release(x_1144, 4);
 lean_ctor_release(x_1144, 5);
 lean_ctor_release(x_1144, 6);
 x_1158 = x_1144;
} else {
 lean_dec_ref(x_1144);
 x_1158 = lean_box(0);
}
x_1159 = lean_ctor_get(x_1145, 0);
lean_inc(x_1159);
x_1160 = lean_ctor_get(x_1145, 1);
lean_inc(x_1160);
if (lean_is_exclusive(x_1145)) {
 lean_ctor_release(x_1145, 0);
 lean_ctor_release(x_1145, 1);
 x_1161 = x_1145;
} else {
 lean_dec_ref(x_1145);
 x_1161 = lean_box(0);
}
lean_inc(x_1138);
x_1162 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1160, x_1, x_1138);
if (lean_is_scalar(x_1161)) {
 x_1163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1163 = x_1161;
}
lean_ctor_set(x_1163, 0, x_1159);
lean_ctor_set(x_1163, 1, x_1162);
if (lean_is_scalar(x_1158)) {
 x_1164 = lean_alloc_ctor(0, 7, 0);
} else {
 x_1164 = x_1158;
}
lean_ctor_set(x_1164, 0, x_1163);
lean_ctor_set(x_1164, 1, x_1152);
lean_ctor_set(x_1164, 2, x_1153);
lean_ctor_set(x_1164, 3, x_1154);
lean_ctor_set(x_1164, 4, x_1155);
lean_ctor_set(x_1164, 5, x_1156);
lean_ctor_set(x_1164, 6, x_1157);
if (lean_is_scalar(x_1151)) {
 x_1165 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1165 = x_1151;
}
lean_ctor_set(x_1165, 0, x_1147);
lean_ctor_set(x_1165, 1, x_1164);
lean_ctor_set(x_1165, 2, x_1148);
lean_ctor_set(x_1165, 3, x_1149);
lean_ctor_set(x_1165, 4, x_1150);
x_1166 = lean_st_ref_set(x_3, x_1165, x_1146);
lean_dec(x_3);
x_1167 = lean_ctor_get(x_1166, 1);
lean_inc(x_1167);
if (lean_is_exclusive(x_1166)) {
 lean_ctor_release(x_1166, 0);
 lean_ctor_release(x_1166, 1);
 x_1168 = x_1166;
} else {
 lean_dec_ref(x_1166);
 x_1168 = lean_box(0);
}
if (lean_is_scalar(x_1168)) {
 x_1169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1169 = x_1168;
}
lean_ctor_set(x_1169, 0, x_1138);
lean_ctor_set(x_1169, 1, x_1167);
return x_1169;
}
else
{
lean_object* x_1170; 
lean_dec(x_3);
lean_dec(x_1);
x_1170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1170, 0, x_1138);
lean_ctor_set(x_1170, 1, x_1139);
return x_1170;
}
}
else
{
lean_object* x_1171; 
lean_dec(x_3);
lean_dec(x_1);
x_1171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1171, 0, x_1138);
lean_ctor_set(x_1171, 1, x_1139);
return x_1171;
}
}
}
else
{
uint8_t x_1172; 
lean_dec(x_3);
lean_dec(x_1);
x_1172 = !lean_is_exclusive(x_1069);
if (x_1172 == 0)
{
return x_1069;
}
else
{
lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; 
x_1173 = lean_ctor_get(x_1069, 0);
x_1174 = lean_ctor_get(x_1069, 1);
lean_inc(x_1174);
lean_inc(x_1173);
lean_dec(x_1069);
x_1175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1175, 0, x_1173);
lean_ctor_set(x_1175, 1, x_1174);
return x_1175;
}
}
}
else
{
lean_object* x_1176; 
lean_dec(x_1057);
lean_dec(x_1056);
lean_dec(x_1055);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1176 = lean_ctor_get(x_1068, 0);
lean_inc(x_1176);
lean_dec(x_1068);
lean_ctor_set(x_1061, 0, x_1176);
return x_1061;
}
}
else
{
lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; 
x_1177 = lean_ctor_get(x_1061, 0);
x_1178 = lean_ctor_get(x_1061, 1);
lean_inc(x_1178);
lean_inc(x_1177);
lean_dec(x_1061);
x_1179 = lean_ctor_get(x_1177, 1);
lean_inc(x_1179);
lean_dec(x_1177);
x_1180 = lean_ctor_get(x_1179, 0);
lean_inc(x_1180);
lean_dec(x_1179);
x_1181 = lean_ctor_get(x_1180, 1);
lean_inc(x_1181);
lean_dec(x_1180);
x_1182 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_1181, x_1);
if (lean_obj_tag(x_1182) == 0)
{
lean_object* x_1183; 
lean_inc(x_3);
x_1183 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(x_1055, x_1056, x_1057, x_2, x_3, x_4, x_5, x_1178);
if (lean_obj_tag(x_1183) == 0)
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; uint8_t x_1187; 
x_1184 = lean_ctor_get(x_1183, 0);
lean_inc(x_1184);
x_1185 = lean_ctor_get(x_1183, 1);
lean_inc(x_1185);
if (lean_is_exclusive(x_1183)) {
 lean_ctor_release(x_1183, 0);
 lean_ctor_release(x_1183, 1);
 x_1186 = x_1183;
} else {
 lean_dec_ref(x_1183);
 x_1186 = lean_box(0);
}
x_1187 = l_Lean_Expr_hasMVar(x_1);
if (x_1187 == 0)
{
uint8_t x_1188; 
x_1188 = l_Lean_Expr_hasMVar(x_1184);
if (x_1188 == 0)
{
lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; 
lean_dec(x_1186);
x_1189 = lean_st_ref_take(x_3, x_1185);
x_1190 = lean_ctor_get(x_1189, 0);
lean_inc(x_1190);
x_1191 = lean_ctor_get(x_1190, 1);
lean_inc(x_1191);
x_1192 = lean_ctor_get(x_1191, 0);
lean_inc(x_1192);
x_1193 = lean_ctor_get(x_1189, 1);
lean_inc(x_1193);
lean_dec(x_1189);
x_1194 = lean_ctor_get(x_1190, 0);
lean_inc(x_1194);
x_1195 = lean_ctor_get(x_1190, 2);
lean_inc(x_1195);
x_1196 = lean_ctor_get(x_1190, 3);
lean_inc(x_1196);
x_1197 = lean_ctor_get(x_1190, 4);
lean_inc(x_1197);
if (lean_is_exclusive(x_1190)) {
 lean_ctor_release(x_1190, 0);
 lean_ctor_release(x_1190, 1);
 lean_ctor_release(x_1190, 2);
 lean_ctor_release(x_1190, 3);
 lean_ctor_release(x_1190, 4);
 x_1198 = x_1190;
} else {
 lean_dec_ref(x_1190);
 x_1198 = lean_box(0);
}
x_1199 = lean_ctor_get(x_1191, 1);
lean_inc(x_1199);
x_1200 = lean_ctor_get(x_1191, 2);
lean_inc(x_1200);
x_1201 = lean_ctor_get(x_1191, 3);
lean_inc(x_1201);
x_1202 = lean_ctor_get(x_1191, 4);
lean_inc(x_1202);
x_1203 = lean_ctor_get(x_1191, 5);
lean_inc(x_1203);
x_1204 = lean_ctor_get(x_1191, 6);
lean_inc(x_1204);
if (lean_is_exclusive(x_1191)) {
 lean_ctor_release(x_1191, 0);
 lean_ctor_release(x_1191, 1);
 lean_ctor_release(x_1191, 2);
 lean_ctor_release(x_1191, 3);
 lean_ctor_release(x_1191, 4);
 lean_ctor_release(x_1191, 5);
 lean_ctor_release(x_1191, 6);
 x_1205 = x_1191;
} else {
 lean_dec_ref(x_1191);
 x_1205 = lean_box(0);
}
x_1206 = lean_ctor_get(x_1192, 0);
lean_inc(x_1206);
x_1207 = lean_ctor_get(x_1192, 1);
lean_inc(x_1207);
if (lean_is_exclusive(x_1192)) {
 lean_ctor_release(x_1192, 0);
 lean_ctor_release(x_1192, 1);
 x_1208 = x_1192;
} else {
 lean_dec_ref(x_1192);
 x_1208 = lean_box(0);
}
lean_inc(x_1184);
x_1209 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1207, x_1, x_1184);
if (lean_is_scalar(x_1208)) {
 x_1210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1210 = x_1208;
}
lean_ctor_set(x_1210, 0, x_1206);
lean_ctor_set(x_1210, 1, x_1209);
if (lean_is_scalar(x_1205)) {
 x_1211 = lean_alloc_ctor(0, 7, 0);
} else {
 x_1211 = x_1205;
}
lean_ctor_set(x_1211, 0, x_1210);
lean_ctor_set(x_1211, 1, x_1199);
lean_ctor_set(x_1211, 2, x_1200);
lean_ctor_set(x_1211, 3, x_1201);
lean_ctor_set(x_1211, 4, x_1202);
lean_ctor_set(x_1211, 5, x_1203);
lean_ctor_set(x_1211, 6, x_1204);
if (lean_is_scalar(x_1198)) {
 x_1212 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1212 = x_1198;
}
lean_ctor_set(x_1212, 0, x_1194);
lean_ctor_set(x_1212, 1, x_1211);
lean_ctor_set(x_1212, 2, x_1195);
lean_ctor_set(x_1212, 3, x_1196);
lean_ctor_set(x_1212, 4, x_1197);
x_1213 = lean_st_ref_set(x_3, x_1212, x_1193);
lean_dec(x_3);
x_1214 = lean_ctor_get(x_1213, 1);
lean_inc(x_1214);
if (lean_is_exclusive(x_1213)) {
 lean_ctor_release(x_1213, 0);
 lean_ctor_release(x_1213, 1);
 x_1215 = x_1213;
} else {
 lean_dec_ref(x_1213);
 x_1215 = lean_box(0);
}
if (lean_is_scalar(x_1215)) {
 x_1216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1216 = x_1215;
}
lean_ctor_set(x_1216, 0, x_1184);
lean_ctor_set(x_1216, 1, x_1214);
return x_1216;
}
else
{
lean_object* x_1217; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_1186)) {
 x_1217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1217 = x_1186;
}
lean_ctor_set(x_1217, 0, x_1184);
lean_ctor_set(x_1217, 1, x_1185);
return x_1217;
}
}
else
{
lean_object* x_1218; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_1186)) {
 x_1218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1218 = x_1186;
}
lean_ctor_set(x_1218, 0, x_1184);
lean_ctor_set(x_1218, 1, x_1185);
return x_1218;
}
}
else
{
lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; 
lean_dec(x_3);
lean_dec(x_1);
x_1219 = lean_ctor_get(x_1183, 0);
lean_inc(x_1219);
x_1220 = lean_ctor_get(x_1183, 1);
lean_inc(x_1220);
if (lean_is_exclusive(x_1183)) {
 lean_ctor_release(x_1183, 0);
 lean_ctor_release(x_1183, 1);
 x_1221 = x_1183;
} else {
 lean_dec_ref(x_1183);
 x_1221 = lean_box(0);
}
if (lean_is_scalar(x_1221)) {
 x_1222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1222 = x_1221;
}
lean_ctor_set(x_1222, 0, x_1219);
lean_ctor_set(x_1222, 1, x_1220);
return x_1222;
}
}
else
{
lean_object* x_1223; lean_object* x_1224; 
lean_dec(x_1057);
lean_dec(x_1056);
lean_dec(x_1055);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1223 = lean_ctor_get(x_1182, 0);
lean_inc(x_1223);
lean_dec(x_1182);
x_1224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1224, 0, x_1223);
lean_ctor_set(x_1224, 1, x_1178);
return x_1224;
}
}
}
case 1:
{
lean_object* x_1225; lean_object* x_1226; uint8_t x_1227; 
x_1225 = lean_ctor_get(x_1058, 1);
lean_inc(x_1225);
lean_dec(x_1058);
x_1226 = lean_st_ref_get(x_3, x_1225);
x_1227 = !lean_is_exclusive(x_1226);
if (x_1227 == 0)
{
lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; 
x_1228 = lean_ctor_get(x_1226, 0);
x_1229 = lean_ctor_get(x_1226, 1);
x_1230 = lean_ctor_get(x_1228, 1);
lean_inc(x_1230);
lean_dec(x_1228);
x_1231 = lean_ctor_get(x_1230, 0);
lean_inc(x_1231);
lean_dec(x_1230);
x_1232 = lean_ctor_get(x_1231, 0);
lean_inc(x_1232);
lean_dec(x_1231);
x_1233 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_1232, x_1);
if (lean_obj_tag(x_1233) == 0)
{
lean_object* x_1234; 
lean_free_object(x_1226);
lean_inc(x_3);
x_1234 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(x_1055, x_1056, x_1057, x_2, x_3, x_4, x_5, x_1229);
if (lean_obj_tag(x_1234) == 0)
{
uint8_t x_1235; 
x_1235 = !lean_is_exclusive(x_1234);
if (x_1235 == 0)
{
lean_object* x_1236; lean_object* x_1237; uint8_t x_1238; 
x_1236 = lean_ctor_get(x_1234, 0);
x_1237 = lean_ctor_get(x_1234, 1);
x_1238 = l_Lean_Expr_hasMVar(x_1);
if (x_1238 == 0)
{
uint8_t x_1239; 
x_1239 = l_Lean_Expr_hasMVar(x_1236);
if (x_1239 == 0)
{
lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; uint8_t x_1245; 
lean_free_object(x_1234);
x_1240 = lean_st_ref_take(x_3, x_1237);
x_1241 = lean_ctor_get(x_1240, 0);
lean_inc(x_1241);
x_1242 = lean_ctor_get(x_1241, 1);
lean_inc(x_1242);
x_1243 = lean_ctor_get(x_1242, 0);
lean_inc(x_1243);
x_1244 = lean_ctor_get(x_1240, 1);
lean_inc(x_1244);
lean_dec(x_1240);
x_1245 = !lean_is_exclusive(x_1241);
if (x_1245 == 0)
{
lean_object* x_1246; uint8_t x_1247; 
x_1246 = lean_ctor_get(x_1241, 1);
lean_dec(x_1246);
x_1247 = !lean_is_exclusive(x_1242);
if (x_1247 == 0)
{
lean_object* x_1248; uint8_t x_1249; 
x_1248 = lean_ctor_get(x_1242, 0);
lean_dec(x_1248);
x_1249 = !lean_is_exclusive(x_1243);
if (x_1249 == 0)
{
lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; uint8_t x_1253; 
x_1250 = lean_ctor_get(x_1243, 0);
lean_inc(x_1236);
x_1251 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1250, x_1, x_1236);
lean_ctor_set(x_1243, 0, x_1251);
x_1252 = lean_st_ref_set(x_3, x_1241, x_1244);
lean_dec(x_3);
x_1253 = !lean_is_exclusive(x_1252);
if (x_1253 == 0)
{
lean_object* x_1254; 
x_1254 = lean_ctor_get(x_1252, 0);
lean_dec(x_1254);
lean_ctor_set(x_1252, 0, x_1236);
return x_1252;
}
else
{
lean_object* x_1255; lean_object* x_1256; 
x_1255 = lean_ctor_get(x_1252, 1);
lean_inc(x_1255);
lean_dec(x_1252);
x_1256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1256, 0, x_1236);
lean_ctor_set(x_1256, 1, x_1255);
return x_1256;
}
}
else
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; 
x_1257 = lean_ctor_get(x_1243, 0);
x_1258 = lean_ctor_get(x_1243, 1);
lean_inc(x_1258);
lean_inc(x_1257);
lean_dec(x_1243);
lean_inc(x_1236);
x_1259 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1257, x_1, x_1236);
x_1260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1260, 0, x_1259);
lean_ctor_set(x_1260, 1, x_1258);
lean_ctor_set(x_1242, 0, x_1260);
x_1261 = lean_st_ref_set(x_3, x_1241, x_1244);
lean_dec(x_3);
x_1262 = lean_ctor_get(x_1261, 1);
lean_inc(x_1262);
if (lean_is_exclusive(x_1261)) {
 lean_ctor_release(x_1261, 0);
 lean_ctor_release(x_1261, 1);
 x_1263 = x_1261;
} else {
 lean_dec_ref(x_1261);
 x_1263 = lean_box(0);
}
if (lean_is_scalar(x_1263)) {
 x_1264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1264 = x_1263;
}
lean_ctor_set(x_1264, 0, x_1236);
lean_ctor_set(x_1264, 1, x_1262);
return x_1264;
}
}
else
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; 
x_1265 = lean_ctor_get(x_1242, 1);
x_1266 = lean_ctor_get(x_1242, 2);
x_1267 = lean_ctor_get(x_1242, 3);
x_1268 = lean_ctor_get(x_1242, 4);
x_1269 = lean_ctor_get(x_1242, 5);
x_1270 = lean_ctor_get(x_1242, 6);
lean_inc(x_1270);
lean_inc(x_1269);
lean_inc(x_1268);
lean_inc(x_1267);
lean_inc(x_1266);
lean_inc(x_1265);
lean_dec(x_1242);
x_1271 = lean_ctor_get(x_1243, 0);
lean_inc(x_1271);
x_1272 = lean_ctor_get(x_1243, 1);
lean_inc(x_1272);
if (lean_is_exclusive(x_1243)) {
 lean_ctor_release(x_1243, 0);
 lean_ctor_release(x_1243, 1);
 x_1273 = x_1243;
} else {
 lean_dec_ref(x_1243);
 x_1273 = lean_box(0);
}
lean_inc(x_1236);
x_1274 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1271, x_1, x_1236);
if (lean_is_scalar(x_1273)) {
 x_1275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1275 = x_1273;
}
lean_ctor_set(x_1275, 0, x_1274);
lean_ctor_set(x_1275, 1, x_1272);
x_1276 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_1276, 0, x_1275);
lean_ctor_set(x_1276, 1, x_1265);
lean_ctor_set(x_1276, 2, x_1266);
lean_ctor_set(x_1276, 3, x_1267);
lean_ctor_set(x_1276, 4, x_1268);
lean_ctor_set(x_1276, 5, x_1269);
lean_ctor_set(x_1276, 6, x_1270);
lean_ctor_set(x_1241, 1, x_1276);
x_1277 = lean_st_ref_set(x_3, x_1241, x_1244);
lean_dec(x_3);
x_1278 = lean_ctor_get(x_1277, 1);
lean_inc(x_1278);
if (lean_is_exclusive(x_1277)) {
 lean_ctor_release(x_1277, 0);
 lean_ctor_release(x_1277, 1);
 x_1279 = x_1277;
} else {
 lean_dec_ref(x_1277);
 x_1279 = lean_box(0);
}
if (lean_is_scalar(x_1279)) {
 x_1280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1280 = x_1279;
}
lean_ctor_set(x_1280, 0, x_1236);
lean_ctor_set(x_1280, 1, x_1278);
return x_1280;
}
}
else
{
lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; 
x_1281 = lean_ctor_get(x_1241, 0);
x_1282 = lean_ctor_get(x_1241, 2);
x_1283 = lean_ctor_get(x_1241, 3);
x_1284 = lean_ctor_get(x_1241, 4);
lean_inc(x_1284);
lean_inc(x_1283);
lean_inc(x_1282);
lean_inc(x_1281);
lean_dec(x_1241);
x_1285 = lean_ctor_get(x_1242, 1);
lean_inc(x_1285);
x_1286 = lean_ctor_get(x_1242, 2);
lean_inc(x_1286);
x_1287 = lean_ctor_get(x_1242, 3);
lean_inc(x_1287);
x_1288 = lean_ctor_get(x_1242, 4);
lean_inc(x_1288);
x_1289 = lean_ctor_get(x_1242, 5);
lean_inc(x_1289);
x_1290 = lean_ctor_get(x_1242, 6);
lean_inc(x_1290);
if (lean_is_exclusive(x_1242)) {
 lean_ctor_release(x_1242, 0);
 lean_ctor_release(x_1242, 1);
 lean_ctor_release(x_1242, 2);
 lean_ctor_release(x_1242, 3);
 lean_ctor_release(x_1242, 4);
 lean_ctor_release(x_1242, 5);
 lean_ctor_release(x_1242, 6);
 x_1291 = x_1242;
} else {
 lean_dec_ref(x_1242);
 x_1291 = lean_box(0);
}
x_1292 = lean_ctor_get(x_1243, 0);
lean_inc(x_1292);
x_1293 = lean_ctor_get(x_1243, 1);
lean_inc(x_1293);
if (lean_is_exclusive(x_1243)) {
 lean_ctor_release(x_1243, 0);
 lean_ctor_release(x_1243, 1);
 x_1294 = x_1243;
} else {
 lean_dec_ref(x_1243);
 x_1294 = lean_box(0);
}
lean_inc(x_1236);
x_1295 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1292, x_1, x_1236);
if (lean_is_scalar(x_1294)) {
 x_1296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1296 = x_1294;
}
lean_ctor_set(x_1296, 0, x_1295);
lean_ctor_set(x_1296, 1, x_1293);
if (lean_is_scalar(x_1291)) {
 x_1297 = lean_alloc_ctor(0, 7, 0);
} else {
 x_1297 = x_1291;
}
lean_ctor_set(x_1297, 0, x_1296);
lean_ctor_set(x_1297, 1, x_1285);
lean_ctor_set(x_1297, 2, x_1286);
lean_ctor_set(x_1297, 3, x_1287);
lean_ctor_set(x_1297, 4, x_1288);
lean_ctor_set(x_1297, 5, x_1289);
lean_ctor_set(x_1297, 6, x_1290);
x_1298 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1298, 0, x_1281);
lean_ctor_set(x_1298, 1, x_1297);
lean_ctor_set(x_1298, 2, x_1282);
lean_ctor_set(x_1298, 3, x_1283);
lean_ctor_set(x_1298, 4, x_1284);
x_1299 = lean_st_ref_set(x_3, x_1298, x_1244);
lean_dec(x_3);
x_1300 = lean_ctor_get(x_1299, 1);
lean_inc(x_1300);
if (lean_is_exclusive(x_1299)) {
 lean_ctor_release(x_1299, 0);
 lean_ctor_release(x_1299, 1);
 x_1301 = x_1299;
} else {
 lean_dec_ref(x_1299);
 x_1301 = lean_box(0);
}
if (lean_is_scalar(x_1301)) {
 x_1302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1302 = x_1301;
}
lean_ctor_set(x_1302, 0, x_1236);
lean_ctor_set(x_1302, 1, x_1300);
return x_1302;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_1234;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_1234;
}
}
else
{
lean_object* x_1303; lean_object* x_1304; uint8_t x_1305; 
x_1303 = lean_ctor_get(x_1234, 0);
x_1304 = lean_ctor_get(x_1234, 1);
lean_inc(x_1304);
lean_inc(x_1303);
lean_dec(x_1234);
x_1305 = l_Lean_Expr_hasMVar(x_1);
if (x_1305 == 0)
{
uint8_t x_1306; 
x_1306 = l_Lean_Expr_hasMVar(x_1303);
if (x_1306 == 0)
{
lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; 
x_1307 = lean_st_ref_take(x_3, x_1304);
x_1308 = lean_ctor_get(x_1307, 0);
lean_inc(x_1308);
x_1309 = lean_ctor_get(x_1308, 1);
lean_inc(x_1309);
x_1310 = lean_ctor_get(x_1309, 0);
lean_inc(x_1310);
x_1311 = lean_ctor_get(x_1307, 1);
lean_inc(x_1311);
lean_dec(x_1307);
x_1312 = lean_ctor_get(x_1308, 0);
lean_inc(x_1312);
x_1313 = lean_ctor_get(x_1308, 2);
lean_inc(x_1313);
x_1314 = lean_ctor_get(x_1308, 3);
lean_inc(x_1314);
x_1315 = lean_ctor_get(x_1308, 4);
lean_inc(x_1315);
if (lean_is_exclusive(x_1308)) {
 lean_ctor_release(x_1308, 0);
 lean_ctor_release(x_1308, 1);
 lean_ctor_release(x_1308, 2);
 lean_ctor_release(x_1308, 3);
 lean_ctor_release(x_1308, 4);
 x_1316 = x_1308;
} else {
 lean_dec_ref(x_1308);
 x_1316 = lean_box(0);
}
x_1317 = lean_ctor_get(x_1309, 1);
lean_inc(x_1317);
x_1318 = lean_ctor_get(x_1309, 2);
lean_inc(x_1318);
x_1319 = lean_ctor_get(x_1309, 3);
lean_inc(x_1319);
x_1320 = lean_ctor_get(x_1309, 4);
lean_inc(x_1320);
x_1321 = lean_ctor_get(x_1309, 5);
lean_inc(x_1321);
x_1322 = lean_ctor_get(x_1309, 6);
lean_inc(x_1322);
if (lean_is_exclusive(x_1309)) {
 lean_ctor_release(x_1309, 0);
 lean_ctor_release(x_1309, 1);
 lean_ctor_release(x_1309, 2);
 lean_ctor_release(x_1309, 3);
 lean_ctor_release(x_1309, 4);
 lean_ctor_release(x_1309, 5);
 lean_ctor_release(x_1309, 6);
 x_1323 = x_1309;
} else {
 lean_dec_ref(x_1309);
 x_1323 = lean_box(0);
}
x_1324 = lean_ctor_get(x_1310, 0);
lean_inc(x_1324);
x_1325 = lean_ctor_get(x_1310, 1);
lean_inc(x_1325);
if (lean_is_exclusive(x_1310)) {
 lean_ctor_release(x_1310, 0);
 lean_ctor_release(x_1310, 1);
 x_1326 = x_1310;
} else {
 lean_dec_ref(x_1310);
 x_1326 = lean_box(0);
}
lean_inc(x_1303);
x_1327 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1324, x_1, x_1303);
if (lean_is_scalar(x_1326)) {
 x_1328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1328 = x_1326;
}
lean_ctor_set(x_1328, 0, x_1327);
lean_ctor_set(x_1328, 1, x_1325);
if (lean_is_scalar(x_1323)) {
 x_1329 = lean_alloc_ctor(0, 7, 0);
} else {
 x_1329 = x_1323;
}
lean_ctor_set(x_1329, 0, x_1328);
lean_ctor_set(x_1329, 1, x_1317);
lean_ctor_set(x_1329, 2, x_1318);
lean_ctor_set(x_1329, 3, x_1319);
lean_ctor_set(x_1329, 4, x_1320);
lean_ctor_set(x_1329, 5, x_1321);
lean_ctor_set(x_1329, 6, x_1322);
if (lean_is_scalar(x_1316)) {
 x_1330 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1330 = x_1316;
}
lean_ctor_set(x_1330, 0, x_1312);
lean_ctor_set(x_1330, 1, x_1329);
lean_ctor_set(x_1330, 2, x_1313);
lean_ctor_set(x_1330, 3, x_1314);
lean_ctor_set(x_1330, 4, x_1315);
x_1331 = lean_st_ref_set(x_3, x_1330, x_1311);
lean_dec(x_3);
x_1332 = lean_ctor_get(x_1331, 1);
lean_inc(x_1332);
if (lean_is_exclusive(x_1331)) {
 lean_ctor_release(x_1331, 0);
 lean_ctor_release(x_1331, 1);
 x_1333 = x_1331;
} else {
 lean_dec_ref(x_1331);
 x_1333 = lean_box(0);
}
if (lean_is_scalar(x_1333)) {
 x_1334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1334 = x_1333;
}
lean_ctor_set(x_1334, 0, x_1303);
lean_ctor_set(x_1334, 1, x_1332);
return x_1334;
}
else
{
lean_object* x_1335; 
lean_dec(x_3);
lean_dec(x_1);
x_1335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1335, 0, x_1303);
lean_ctor_set(x_1335, 1, x_1304);
return x_1335;
}
}
else
{
lean_object* x_1336; 
lean_dec(x_3);
lean_dec(x_1);
x_1336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1336, 0, x_1303);
lean_ctor_set(x_1336, 1, x_1304);
return x_1336;
}
}
}
else
{
uint8_t x_1337; 
lean_dec(x_3);
lean_dec(x_1);
x_1337 = !lean_is_exclusive(x_1234);
if (x_1337 == 0)
{
return x_1234;
}
else
{
lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; 
x_1338 = lean_ctor_get(x_1234, 0);
x_1339 = lean_ctor_get(x_1234, 1);
lean_inc(x_1339);
lean_inc(x_1338);
lean_dec(x_1234);
x_1340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1340, 0, x_1338);
lean_ctor_set(x_1340, 1, x_1339);
return x_1340;
}
}
}
else
{
lean_object* x_1341; 
lean_dec(x_1057);
lean_dec(x_1056);
lean_dec(x_1055);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1341 = lean_ctor_get(x_1233, 0);
lean_inc(x_1341);
lean_dec(x_1233);
lean_ctor_set(x_1226, 0, x_1341);
return x_1226;
}
}
else
{
lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; 
x_1342 = lean_ctor_get(x_1226, 0);
x_1343 = lean_ctor_get(x_1226, 1);
lean_inc(x_1343);
lean_inc(x_1342);
lean_dec(x_1226);
x_1344 = lean_ctor_get(x_1342, 1);
lean_inc(x_1344);
lean_dec(x_1342);
x_1345 = lean_ctor_get(x_1344, 0);
lean_inc(x_1345);
lean_dec(x_1344);
x_1346 = lean_ctor_get(x_1345, 0);
lean_inc(x_1346);
lean_dec(x_1345);
x_1347 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_1346, x_1);
if (lean_obj_tag(x_1347) == 0)
{
lean_object* x_1348; 
lean_inc(x_3);
x_1348 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(x_1055, x_1056, x_1057, x_2, x_3, x_4, x_5, x_1343);
if (lean_obj_tag(x_1348) == 0)
{
lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; uint8_t x_1352; 
x_1349 = lean_ctor_get(x_1348, 0);
lean_inc(x_1349);
x_1350 = lean_ctor_get(x_1348, 1);
lean_inc(x_1350);
if (lean_is_exclusive(x_1348)) {
 lean_ctor_release(x_1348, 0);
 lean_ctor_release(x_1348, 1);
 x_1351 = x_1348;
} else {
 lean_dec_ref(x_1348);
 x_1351 = lean_box(0);
}
x_1352 = l_Lean_Expr_hasMVar(x_1);
if (x_1352 == 0)
{
uint8_t x_1353; 
x_1353 = l_Lean_Expr_hasMVar(x_1349);
if (x_1353 == 0)
{
lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; 
lean_dec(x_1351);
x_1354 = lean_st_ref_take(x_3, x_1350);
x_1355 = lean_ctor_get(x_1354, 0);
lean_inc(x_1355);
x_1356 = lean_ctor_get(x_1355, 1);
lean_inc(x_1356);
x_1357 = lean_ctor_get(x_1356, 0);
lean_inc(x_1357);
x_1358 = lean_ctor_get(x_1354, 1);
lean_inc(x_1358);
lean_dec(x_1354);
x_1359 = lean_ctor_get(x_1355, 0);
lean_inc(x_1359);
x_1360 = lean_ctor_get(x_1355, 2);
lean_inc(x_1360);
x_1361 = lean_ctor_get(x_1355, 3);
lean_inc(x_1361);
x_1362 = lean_ctor_get(x_1355, 4);
lean_inc(x_1362);
if (lean_is_exclusive(x_1355)) {
 lean_ctor_release(x_1355, 0);
 lean_ctor_release(x_1355, 1);
 lean_ctor_release(x_1355, 2);
 lean_ctor_release(x_1355, 3);
 lean_ctor_release(x_1355, 4);
 x_1363 = x_1355;
} else {
 lean_dec_ref(x_1355);
 x_1363 = lean_box(0);
}
x_1364 = lean_ctor_get(x_1356, 1);
lean_inc(x_1364);
x_1365 = lean_ctor_get(x_1356, 2);
lean_inc(x_1365);
x_1366 = lean_ctor_get(x_1356, 3);
lean_inc(x_1366);
x_1367 = lean_ctor_get(x_1356, 4);
lean_inc(x_1367);
x_1368 = lean_ctor_get(x_1356, 5);
lean_inc(x_1368);
x_1369 = lean_ctor_get(x_1356, 6);
lean_inc(x_1369);
if (lean_is_exclusive(x_1356)) {
 lean_ctor_release(x_1356, 0);
 lean_ctor_release(x_1356, 1);
 lean_ctor_release(x_1356, 2);
 lean_ctor_release(x_1356, 3);
 lean_ctor_release(x_1356, 4);
 lean_ctor_release(x_1356, 5);
 lean_ctor_release(x_1356, 6);
 x_1370 = x_1356;
} else {
 lean_dec_ref(x_1356);
 x_1370 = lean_box(0);
}
x_1371 = lean_ctor_get(x_1357, 0);
lean_inc(x_1371);
x_1372 = lean_ctor_get(x_1357, 1);
lean_inc(x_1372);
if (lean_is_exclusive(x_1357)) {
 lean_ctor_release(x_1357, 0);
 lean_ctor_release(x_1357, 1);
 x_1373 = x_1357;
} else {
 lean_dec_ref(x_1357);
 x_1373 = lean_box(0);
}
lean_inc(x_1349);
x_1374 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1371, x_1, x_1349);
if (lean_is_scalar(x_1373)) {
 x_1375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1375 = x_1373;
}
lean_ctor_set(x_1375, 0, x_1374);
lean_ctor_set(x_1375, 1, x_1372);
if (lean_is_scalar(x_1370)) {
 x_1376 = lean_alloc_ctor(0, 7, 0);
} else {
 x_1376 = x_1370;
}
lean_ctor_set(x_1376, 0, x_1375);
lean_ctor_set(x_1376, 1, x_1364);
lean_ctor_set(x_1376, 2, x_1365);
lean_ctor_set(x_1376, 3, x_1366);
lean_ctor_set(x_1376, 4, x_1367);
lean_ctor_set(x_1376, 5, x_1368);
lean_ctor_set(x_1376, 6, x_1369);
if (lean_is_scalar(x_1363)) {
 x_1377 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1377 = x_1363;
}
lean_ctor_set(x_1377, 0, x_1359);
lean_ctor_set(x_1377, 1, x_1376);
lean_ctor_set(x_1377, 2, x_1360);
lean_ctor_set(x_1377, 3, x_1361);
lean_ctor_set(x_1377, 4, x_1362);
x_1378 = lean_st_ref_set(x_3, x_1377, x_1358);
lean_dec(x_3);
x_1379 = lean_ctor_get(x_1378, 1);
lean_inc(x_1379);
if (lean_is_exclusive(x_1378)) {
 lean_ctor_release(x_1378, 0);
 lean_ctor_release(x_1378, 1);
 x_1380 = x_1378;
} else {
 lean_dec_ref(x_1378);
 x_1380 = lean_box(0);
}
if (lean_is_scalar(x_1380)) {
 x_1381 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1381 = x_1380;
}
lean_ctor_set(x_1381, 0, x_1349);
lean_ctor_set(x_1381, 1, x_1379);
return x_1381;
}
else
{
lean_object* x_1382; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_1351)) {
 x_1382 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1382 = x_1351;
}
lean_ctor_set(x_1382, 0, x_1349);
lean_ctor_set(x_1382, 1, x_1350);
return x_1382;
}
}
else
{
lean_object* x_1383; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_1351)) {
 x_1383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1383 = x_1351;
}
lean_ctor_set(x_1383, 0, x_1349);
lean_ctor_set(x_1383, 1, x_1350);
return x_1383;
}
}
else
{
lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; 
lean_dec(x_3);
lean_dec(x_1);
x_1384 = lean_ctor_get(x_1348, 0);
lean_inc(x_1384);
x_1385 = lean_ctor_get(x_1348, 1);
lean_inc(x_1385);
if (lean_is_exclusive(x_1348)) {
 lean_ctor_release(x_1348, 0);
 lean_ctor_release(x_1348, 1);
 x_1386 = x_1348;
} else {
 lean_dec_ref(x_1348);
 x_1386 = lean_box(0);
}
if (lean_is_scalar(x_1386)) {
 x_1387 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1387 = x_1386;
}
lean_ctor_set(x_1387, 0, x_1384);
lean_ctor_set(x_1387, 1, x_1385);
return x_1387;
}
}
else
{
lean_object* x_1388; lean_object* x_1389; 
lean_dec(x_1057);
lean_dec(x_1056);
lean_dec(x_1055);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1388 = lean_ctor_get(x_1347, 0);
lean_inc(x_1388);
lean_dec(x_1347);
x_1389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1389, 0, x_1388);
lean_ctor_set(x_1389, 1, x_1343);
return x_1389;
}
}
}
default: 
{
lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; 
lean_dec(x_1059);
lean_dec(x_1057);
lean_dec(x_1056);
lean_dec(x_1055);
lean_dec(x_1);
x_1390 = lean_ctor_get(x_1058, 1);
lean_inc(x_1390);
lean_dec(x_1058);
x_1391 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3;
x_1392 = l_panic___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__8(x_1391, x_2, x_3, x_4, x_5, x_1390);
return x_1392;
}
}
}
default: 
{
lean_object* x_1393; lean_object* x_1394; 
x_1393 = l_Lean_Meta_getTransparency(x_2, x_3, x_4, x_5, x_6);
x_1394 = lean_ctor_get(x_1393, 0);
lean_inc(x_1394);
switch (lean_obj_tag(x_1394)) {
case 0:
{
lean_object* x_1395; lean_object* x_1396; uint8_t x_1397; 
x_1395 = lean_ctor_get(x_1393, 1);
lean_inc(x_1395);
lean_dec(x_1393);
x_1396 = lean_st_ref_get(x_3, x_1395);
x_1397 = !lean_is_exclusive(x_1396);
if (x_1397 == 0)
{
lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
x_1398 = lean_ctor_get(x_1396, 0);
x_1399 = lean_ctor_get(x_1396, 1);
x_1400 = lean_ctor_get(x_1398, 1);
lean_inc(x_1400);
lean_dec(x_1398);
x_1401 = lean_ctor_get(x_1400, 0);
lean_inc(x_1401);
lean_dec(x_1400);
x_1402 = lean_ctor_get(x_1401, 1);
lean_inc(x_1402);
lean_dec(x_1401);
x_1403 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_1402, x_1);
if (lean_obj_tag(x_1403) == 0)
{
lean_object* x_1404; uint8_t x_1405; lean_object* x_1406; 
lean_free_object(x_1396);
x_1404 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1;
x_1405 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_1406 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_1, x_1404, x_1405, x_2, x_3, x_4, x_5, x_1399);
if (lean_obj_tag(x_1406) == 0)
{
uint8_t x_1407; 
x_1407 = !lean_is_exclusive(x_1406);
if (x_1407 == 0)
{
lean_object* x_1408; lean_object* x_1409; uint8_t x_1410; 
x_1408 = lean_ctor_get(x_1406, 0);
x_1409 = lean_ctor_get(x_1406, 1);
x_1410 = l_Lean_Expr_hasMVar(x_1);
if (x_1410 == 0)
{
uint8_t x_1411; 
x_1411 = l_Lean_Expr_hasMVar(x_1408);
if (x_1411 == 0)
{
lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; uint8_t x_1417; 
lean_free_object(x_1406);
x_1412 = lean_st_ref_take(x_3, x_1409);
x_1413 = lean_ctor_get(x_1412, 0);
lean_inc(x_1413);
x_1414 = lean_ctor_get(x_1413, 1);
lean_inc(x_1414);
x_1415 = lean_ctor_get(x_1414, 0);
lean_inc(x_1415);
x_1416 = lean_ctor_get(x_1412, 1);
lean_inc(x_1416);
lean_dec(x_1412);
x_1417 = !lean_is_exclusive(x_1413);
if (x_1417 == 0)
{
lean_object* x_1418; uint8_t x_1419; 
x_1418 = lean_ctor_get(x_1413, 1);
lean_dec(x_1418);
x_1419 = !lean_is_exclusive(x_1414);
if (x_1419 == 0)
{
lean_object* x_1420; uint8_t x_1421; 
x_1420 = lean_ctor_get(x_1414, 0);
lean_dec(x_1420);
x_1421 = !lean_is_exclusive(x_1415);
if (x_1421 == 0)
{
lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; uint8_t x_1425; 
x_1422 = lean_ctor_get(x_1415, 1);
lean_inc(x_1408);
x_1423 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1422, x_1, x_1408);
lean_ctor_set(x_1415, 1, x_1423);
x_1424 = lean_st_ref_set(x_3, x_1413, x_1416);
lean_dec(x_3);
x_1425 = !lean_is_exclusive(x_1424);
if (x_1425 == 0)
{
lean_object* x_1426; 
x_1426 = lean_ctor_get(x_1424, 0);
lean_dec(x_1426);
lean_ctor_set(x_1424, 0, x_1408);
return x_1424;
}
else
{
lean_object* x_1427; lean_object* x_1428; 
x_1427 = lean_ctor_get(x_1424, 1);
lean_inc(x_1427);
lean_dec(x_1424);
x_1428 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1428, 0, x_1408);
lean_ctor_set(x_1428, 1, x_1427);
return x_1428;
}
}
else
{
lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; 
x_1429 = lean_ctor_get(x_1415, 0);
x_1430 = lean_ctor_get(x_1415, 1);
lean_inc(x_1430);
lean_inc(x_1429);
lean_dec(x_1415);
lean_inc(x_1408);
x_1431 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1430, x_1, x_1408);
x_1432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1432, 0, x_1429);
lean_ctor_set(x_1432, 1, x_1431);
lean_ctor_set(x_1414, 0, x_1432);
x_1433 = lean_st_ref_set(x_3, x_1413, x_1416);
lean_dec(x_3);
x_1434 = lean_ctor_get(x_1433, 1);
lean_inc(x_1434);
if (lean_is_exclusive(x_1433)) {
 lean_ctor_release(x_1433, 0);
 lean_ctor_release(x_1433, 1);
 x_1435 = x_1433;
} else {
 lean_dec_ref(x_1433);
 x_1435 = lean_box(0);
}
if (lean_is_scalar(x_1435)) {
 x_1436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1436 = x_1435;
}
lean_ctor_set(x_1436, 0, x_1408);
lean_ctor_set(x_1436, 1, x_1434);
return x_1436;
}
}
else
{
lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; 
x_1437 = lean_ctor_get(x_1414, 1);
x_1438 = lean_ctor_get(x_1414, 2);
x_1439 = lean_ctor_get(x_1414, 3);
x_1440 = lean_ctor_get(x_1414, 4);
x_1441 = lean_ctor_get(x_1414, 5);
x_1442 = lean_ctor_get(x_1414, 6);
lean_inc(x_1442);
lean_inc(x_1441);
lean_inc(x_1440);
lean_inc(x_1439);
lean_inc(x_1438);
lean_inc(x_1437);
lean_dec(x_1414);
x_1443 = lean_ctor_get(x_1415, 0);
lean_inc(x_1443);
x_1444 = lean_ctor_get(x_1415, 1);
lean_inc(x_1444);
if (lean_is_exclusive(x_1415)) {
 lean_ctor_release(x_1415, 0);
 lean_ctor_release(x_1415, 1);
 x_1445 = x_1415;
} else {
 lean_dec_ref(x_1415);
 x_1445 = lean_box(0);
}
lean_inc(x_1408);
x_1446 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1444, x_1, x_1408);
if (lean_is_scalar(x_1445)) {
 x_1447 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1447 = x_1445;
}
lean_ctor_set(x_1447, 0, x_1443);
lean_ctor_set(x_1447, 1, x_1446);
x_1448 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_1448, 0, x_1447);
lean_ctor_set(x_1448, 1, x_1437);
lean_ctor_set(x_1448, 2, x_1438);
lean_ctor_set(x_1448, 3, x_1439);
lean_ctor_set(x_1448, 4, x_1440);
lean_ctor_set(x_1448, 5, x_1441);
lean_ctor_set(x_1448, 6, x_1442);
lean_ctor_set(x_1413, 1, x_1448);
x_1449 = lean_st_ref_set(x_3, x_1413, x_1416);
lean_dec(x_3);
x_1450 = lean_ctor_get(x_1449, 1);
lean_inc(x_1450);
if (lean_is_exclusive(x_1449)) {
 lean_ctor_release(x_1449, 0);
 lean_ctor_release(x_1449, 1);
 x_1451 = x_1449;
} else {
 lean_dec_ref(x_1449);
 x_1451 = lean_box(0);
}
if (lean_is_scalar(x_1451)) {
 x_1452 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1452 = x_1451;
}
lean_ctor_set(x_1452, 0, x_1408);
lean_ctor_set(x_1452, 1, x_1450);
return x_1452;
}
}
else
{
lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; 
x_1453 = lean_ctor_get(x_1413, 0);
x_1454 = lean_ctor_get(x_1413, 2);
x_1455 = lean_ctor_get(x_1413, 3);
x_1456 = lean_ctor_get(x_1413, 4);
lean_inc(x_1456);
lean_inc(x_1455);
lean_inc(x_1454);
lean_inc(x_1453);
lean_dec(x_1413);
x_1457 = lean_ctor_get(x_1414, 1);
lean_inc(x_1457);
x_1458 = lean_ctor_get(x_1414, 2);
lean_inc(x_1458);
x_1459 = lean_ctor_get(x_1414, 3);
lean_inc(x_1459);
x_1460 = lean_ctor_get(x_1414, 4);
lean_inc(x_1460);
x_1461 = lean_ctor_get(x_1414, 5);
lean_inc(x_1461);
x_1462 = lean_ctor_get(x_1414, 6);
lean_inc(x_1462);
if (lean_is_exclusive(x_1414)) {
 lean_ctor_release(x_1414, 0);
 lean_ctor_release(x_1414, 1);
 lean_ctor_release(x_1414, 2);
 lean_ctor_release(x_1414, 3);
 lean_ctor_release(x_1414, 4);
 lean_ctor_release(x_1414, 5);
 lean_ctor_release(x_1414, 6);
 x_1463 = x_1414;
} else {
 lean_dec_ref(x_1414);
 x_1463 = lean_box(0);
}
x_1464 = lean_ctor_get(x_1415, 0);
lean_inc(x_1464);
x_1465 = lean_ctor_get(x_1415, 1);
lean_inc(x_1465);
if (lean_is_exclusive(x_1415)) {
 lean_ctor_release(x_1415, 0);
 lean_ctor_release(x_1415, 1);
 x_1466 = x_1415;
} else {
 lean_dec_ref(x_1415);
 x_1466 = lean_box(0);
}
lean_inc(x_1408);
x_1467 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1465, x_1, x_1408);
if (lean_is_scalar(x_1466)) {
 x_1468 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1468 = x_1466;
}
lean_ctor_set(x_1468, 0, x_1464);
lean_ctor_set(x_1468, 1, x_1467);
if (lean_is_scalar(x_1463)) {
 x_1469 = lean_alloc_ctor(0, 7, 0);
} else {
 x_1469 = x_1463;
}
lean_ctor_set(x_1469, 0, x_1468);
lean_ctor_set(x_1469, 1, x_1457);
lean_ctor_set(x_1469, 2, x_1458);
lean_ctor_set(x_1469, 3, x_1459);
lean_ctor_set(x_1469, 4, x_1460);
lean_ctor_set(x_1469, 5, x_1461);
lean_ctor_set(x_1469, 6, x_1462);
x_1470 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1470, 0, x_1453);
lean_ctor_set(x_1470, 1, x_1469);
lean_ctor_set(x_1470, 2, x_1454);
lean_ctor_set(x_1470, 3, x_1455);
lean_ctor_set(x_1470, 4, x_1456);
x_1471 = lean_st_ref_set(x_3, x_1470, x_1416);
lean_dec(x_3);
x_1472 = lean_ctor_get(x_1471, 1);
lean_inc(x_1472);
if (lean_is_exclusive(x_1471)) {
 lean_ctor_release(x_1471, 0);
 lean_ctor_release(x_1471, 1);
 x_1473 = x_1471;
} else {
 lean_dec_ref(x_1471);
 x_1473 = lean_box(0);
}
if (lean_is_scalar(x_1473)) {
 x_1474 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1474 = x_1473;
}
lean_ctor_set(x_1474, 0, x_1408);
lean_ctor_set(x_1474, 1, x_1472);
return x_1474;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_1406;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_1406;
}
}
else
{
lean_object* x_1475; lean_object* x_1476; uint8_t x_1477; 
x_1475 = lean_ctor_get(x_1406, 0);
x_1476 = lean_ctor_get(x_1406, 1);
lean_inc(x_1476);
lean_inc(x_1475);
lean_dec(x_1406);
x_1477 = l_Lean_Expr_hasMVar(x_1);
if (x_1477 == 0)
{
uint8_t x_1478; 
x_1478 = l_Lean_Expr_hasMVar(x_1475);
if (x_1478 == 0)
{
lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; 
x_1479 = lean_st_ref_take(x_3, x_1476);
x_1480 = lean_ctor_get(x_1479, 0);
lean_inc(x_1480);
x_1481 = lean_ctor_get(x_1480, 1);
lean_inc(x_1481);
x_1482 = lean_ctor_get(x_1481, 0);
lean_inc(x_1482);
x_1483 = lean_ctor_get(x_1479, 1);
lean_inc(x_1483);
lean_dec(x_1479);
x_1484 = lean_ctor_get(x_1480, 0);
lean_inc(x_1484);
x_1485 = lean_ctor_get(x_1480, 2);
lean_inc(x_1485);
x_1486 = lean_ctor_get(x_1480, 3);
lean_inc(x_1486);
x_1487 = lean_ctor_get(x_1480, 4);
lean_inc(x_1487);
if (lean_is_exclusive(x_1480)) {
 lean_ctor_release(x_1480, 0);
 lean_ctor_release(x_1480, 1);
 lean_ctor_release(x_1480, 2);
 lean_ctor_release(x_1480, 3);
 lean_ctor_release(x_1480, 4);
 x_1488 = x_1480;
} else {
 lean_dec_ref(x_1480);
 x_1488 = lean_box(0);
}
x_1489 = lean_ctor_get(x_1481, 1);
lean_inc(x_1489);
x_1490 = lean_ctor_get(x_1481, 2);
lean_inc(x_1490);
x_1491 = lean_ctor_get(x_1481, 3);
lean_inc(x_1491);
x_1492 = lean_ctor_get(x_1481, 4);
lean_inc(x_1492);
x_1493 = lean_ctor_get(x_1481, 5);
lean_inc(x_1493);
x_1494 = lean_ctor_get(x_1481, 6);
lean_inc(x_1494);
if (lean_is_exclusive(x_1481)) {
 lean_ctor_release(x_1481, 0);
 lean_ctor_release(x_1481, 1);
 lean_ctor_release(x_1481, 2);
 lean_ctor_release(x_1481, 3);
 lean_ctor_release(x_1481, 4);
 lean_ctor_release(x_1481, 5);
 lean_ctor_release(x_1481, 6);
 x_1495 = x_1481;
} else {
 lean_dec_ref(x_1481);
 x_1495 = lean_box(0);
}
x_1496 = lean_ctor_get(x_1482, 0);
lean_inc(x_1496);
x_1497 = lean_ctor_get(x_1482, 1);
lean_inc(x_1497);
if (lean_is_exclusive(x_1482)) {
 lean_ctor_release(x_1482, 0);
 lean_ctor_release(x_1482, 1);
 x_1498 = x_1482;
} else {
 lean_dec_ref(x_1482);
 x_1498 = lean_box(0);
}
lean_inc(x_1475);
x_1499 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1497, x_1, x_1475);
if (lean_is_scalar(x_1498)) {
 x_1500 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1500 = x_1498;
}
lean_ctor_set(x_1500, 0, x_1496);
lean_ctor_set(x_1500, 1, x_1499);
if (lean_is_scalar(x_1495)) {
 x_1501 = lean_alloc_ctor(0, 7, 0);
} else {
 x_1501 = x_1495;
}
lean_ctor_set(x_1501, 0, x_1500);
lean_ctor_set(x_1501, 1, x_1489);
lean_ctor_set(x_1501, 2, x_1490);
lean_ctor_set(x_1501, 3, x_1491);
lean_ctor_set(x_1501, 4, x_1492);
lean_ctor_set(x_1501, 5, x_1493);
lean_ctor_set(x_1501, 6, x_1494);
if (lean_is_scalar(x_1488)) {
 x_1502 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1502 = x_1488;
}
lean_ctor_set(x_1502, 0, x_1484);
lean_ctor_set(x_1502, 1, x_1501);
lean_ctor_set(x_1502, 2, x_1485);
lean_ctor_set(x_1502, 3, x_1486);
lean_ctor_set(x_1502, 4, x_1487);
x_1503 = lean_st_ref_set(x_3, x_1502, x_1483);
lean_dec(x_3);
x_1504 = lean_ctor_get(x_1503, 1);
lean_inc(x_1504);
if (lean_is_exclusive(x_1503)) {
 lean_ctor_release(x_1503, 0);
 lean_ctor_release(x_1503, 1);
 x_1505 = x_1503;
} else {
 lean_dec_ref(x_1503);
 x_1505 = lean_box(0);
}
if (lean_is_scalar(x_1505)) {
 x_1506 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1506 = x_1505;
}
lean_ctor_set(x_1506, 0, x_1475);
lean_ctor_set(x_1506, 1, x_1504);
return x_1506;
}
else
{
lean_object* x_1507; 
lean_dec(x_3);
lean_dec(x_1);
x_1507 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1507, 0, x_1475);
lean_ctor_set(x_1507, 1, x_1476);
return x_1507;
}
}
else
{
lean_object* x_1508; 
lean_dec(x_3);
lean_dec(x_1);
x_1508 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1508, 0, x_1475);
lean_ctor_set(x_1508, 1, x_1476);
return x_1508;
}
}
}
else
{
uint8_t x_1509; 
lean_dec(x_3);
lean_dec(x_1);
x_1509 = !lean_is_exclusive(x_1406);
if (x_1509 == 0)
{
return x_1406;
}
else
{
lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; 
x_1510 = lean_ctor_get(x_1406, 0);
x_1511 = lean_ctor_get(x_1406, 1);
lean_inc(x_1511);
lean_inc(x_1510);
lean_dec(x_1406);
x_1512 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1512, 0, x_1510);
lean_ctor_set(x_1512, 1, x_1511);
return x_1512;
}
}
}
else
{
lean_object* x_1513; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1513 = lean_ctor_get(x_1403, 0);
lean_inc(x_1513);
lean_dec(x_1403);
lean_ctor_set(x_1396, 0, x_1513);
return x_1396;
}
}
else
{
lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; 
x_1514 = lean_ctor_get(x_1396, 0);
x_1515 = lean_ctor_get(x_1396, 1);
lean_inc(x_1515);
lean_inc(x_1514);
lean_dec(x_1396);
x_1516 = lean_ctor_get(x_1514, 1);
lean_inc(x_1516);
lean_dec(x_1514);
x_1517 = lean_ctor_get(x_1516, 0);
lean_inc(x_1517);
lean_dec(x_1516);
x_1518 = lean_ctor_get(x_1517, 1);
lean_inc(x_1518);
lean_dec(x_1517);
x_1519 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_1518, x_1);
if (lean_obj_tag(x_1519) == 0)
{
lean_object* x_1520; uint8_t x_1521; lean_object* x_1522; 
x_1520 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1;
x_1521 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_1522 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_1, x_1520, x_1521, x_2, x_3, x_4, x_5, x_1515);
if (lean_obj_tag(x_1522) == 0)
{
lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; uint8_t x_1526; 
x_1523 = lean_ctor_get(x_1522, 0);
lean_inc(x_1523);
x_1524 = lean_ctor_get(x_1522, 1);
lean_inc(x_1524);
if (lean_is_exclusive(x_1522)) {
 lean_ctor_release(x_1522, 0);
 lean_ctor_release(x_1522, 1);
 x_1525 = x_1522;
} else {
 lean_dec_ref(x_1522);
 x_1525 = lean_box(0);
}
x_1526 = l_Lean_Expr_hasMVar(x_1);
if (x_1526 == 0)
{
uint8_t x_1527; 
x_1527 = l_Lean_Expr_hasMVar(x_1523);
if (x_1527 == 0)
{
lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; 
lean_dec(x_1525);
x_1528 = lean_st_ref_take(x_3, x_1524);
x_1529 = lean_ctor_get(x_1528, 0);
lean_inc(x_1529);
x_1530 = lean_ctor_get(x_1529, 1);
lean_inc(x_1530);
x_1531 = lean_ctor_get(x_1530, 0);
lean_inc(x_1531);
x_1532 = lean_ctor_get(x_1528, 1);
lean_inc(x_1532);
lean_dec(x_1528);
x_1533 = lean_ctor_get(x_1529, 0);
lean_inc(x_1533);
x_1534 = lean_ctor_get(x_1529, 2);
lean_inc(x_1534);
x_1535 = lean_ctor_get(x_1529, 3);
lean_inc(x_1535);
x_1536 = lean_ctor_get(x_1529, 4);
lean_inc(x_1536);
if (lean_is_exclusive(x_1529)) {
 lean_ctor_release(x_1529, 0);
 lean_ctor_release(x_1529, 1);
 lean_ctor_release(x_1529, 2);
 lean_ctor_release(x_1529, 3);
 lean_ctor_release(x_1529, 4);
 x_1537 = x_1529;
} else {
 lean_dec_ref(x_1529);
 x_1537 = lean_box(0);
}
x_1538 = lean_ctor_get(x_1530, 1);
lean_inc(x_1538);
x_1539 = lean_ctor_get(x_1530, 2);
lean_inc(x_1539);
x_1540 = lean_ctor_get(x_1530, 3);
lean_inc(x_1540);
x_1541 = lean_ctor_get(x_1530, 4);
lean_inc(x_1541);
x_1542 = lean_ctor_get(x_1530, 5);
lean_inc(x_1542);
x_1543 = lean_ctor_get(x_1530, 6);
lean_inc(x_1543);
if (lean_is_exclusive(x_1530)) {
 lean_ctor_release(x_1530, 0);
 lean_ctor_release(x_1530, 1);
 lean_ctor_release(x_1530, 2);
 lean_ctor_release(x_1530, 3);
 lean_ctor_release(x_1530, 4);
 lean_ctor_release(x_1530, 5);
 lean_ctor_release(x_1530, 6);
 x_1544 = x_1530;
} else {
 lean_dec_ref(x_1530);
 x_1544 = lean_box(0);
}
x_1545 = lean_ctor_get(x_1531, 0);
lean_inc(x_1545);
x_1546 = lean_ctor_get(x_1531, 1);
lean_inc(x_1546);
if (lean_is_exclusive(x_1531)) {
 lean_ctor_release(x_1531, 0);
 lean_ctor_release(x_1531, 1);
 x_1547 = x_1531;
} else {
 lean_dec_ref(x_1531);
 x_1547 = lean_box(0);
}
lean_inc(x_1523);
x_1548 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1546, x_1, x_1523);
if (lean_is_scalar(x_1547)) {
 x_1549 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1549 = x_1547;
}
lean_ctor_set(x_1549, 0, x_1545);
lean_ctor_set(x_1549, 1, x_1548);
if (lean_is_scalar(x_1544)) {
 x_1550 = lean_alloc_ctor(0, 7, 0);
} else {
 x_1550 = x_1544;
}
lean_ctor_set(x_1550, 0, x_1549);
lean_ctor_set(x_1550, 1, x_1538);
lean_ctor_set(x_1550, 2, x_1539);
lean_ctor_set(x_1550, 3, x_1540);
lean_ctor_set(x_1550, 4, x_1541);
lean_ctor_set(x_1550, 5, x_1542);
lean_ctor_set(x_1550, 6, x_1543);
if (lean_is_scalar(x_1537)) {
 x_1551 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1551 = x_1537;
}
lean_ctor_set(x_1551, 0, x_1533);
lean_ctor_set(x_1551, 1, x_1550);
lean_ctor_set(x_1551, 2, x_1534);
lean_ctor_set(x_1551, 3, x_1535);
lean_ctor_set(x_1551, 4, x_1536);
x_1552 = lean_st_ref_set(x_3, x_1551, x_1532);
lean_dec(x_3);
x_1553 = lean_ctor_get(x_1552, 1);
lean_inc(x_1553);
if (lean_is_exclusive(x_1552)) {
 lean_ctor_release(x_1552, 0);
 lean_ctor_release(x_1552, 1);
 x_1554 = x_1552;
} else {
 lean_dec_ref(x_1552);
 x_1554 = lean_box(0);
}
if (lean_is_scalar(x_1554)) {
 x_1555 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1555 = x_1554;
}
lean_ctor_set(x_1555, 0, x_1523);
lean_ctor_set(x_1555, 1, x_1553);
return x_1555;
}
else
{
lean_object* x_1556; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_1525)) {
 x_1556 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1556 = x_1525;
}
lean_ctor_set(x_1556, 0, x_1523);
lean_ctor_set(x_1556, 1, x_1524);
return x_1556;
}
}
else
{
lean_object* x_1557; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_1525)) {
 x_1557 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1557 = x_1525;
}
lean_ctor_set(x_1557, 0, x_1523);
lean_ctor_set(x_1557, 1, x_1524);
return x_1557;
}
}
else
{
lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; 
lean_dec(x_3);
lean_dec(x_1);
x_1558 = lean_ctor_get(x_1522, 0);
lean_inc(x_1558);
x_1559 = lean_ctor_get(x_1522, 1);
lean_inc(x_1559);
if (lean_is_exclusive(x_1522)) {
 lean_ctor_release(x_1522, 0);
 lean_ctor_release(x_1522, 1);
 x_1560 = x_1522;
} else {
 lean_dec_ref(x_1522);
 x_1560 = lean_box(0);
}
if (lean_is_scalar(x_1560)) {
 x_1561 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1561 = x_1560;
}
lean_ctor_set(x_1561, 0, x_1558);
lean_ctor_set(x_1561, 1, x_1559);
return x_1561;
}
}
else
{
lean_object* x_1562; lean_object* x_1563; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1562 = lean_ctor_get(x_1519, 0);
lean_inc(x_1562);
lean_dec(x_1519);
x_1563 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1563, 0, x_1562);
lean_ctor_set(x_1563, 1, x_1515);
return x_1563;
}
}
}
case 1:
{
lean_object* x_1564; lean_object* x_1565; uint8_t x_1566; 
x_1564 = lean_ctor_get(x_1393, 1);
lean_inc(x_1564);
lean_dec(x_1393);
x_1565 = lean_st_ref_get(x_3, x_1564);
x_1566 = !lean_is_exclusive(x_1565);
if (x_1566 == 0)
{
lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; 
x_1567 = lean_ctor_get(x_1565, 0);
x_1568 = lean_ctor_get(x_1565, 1);
x_1569 = lean_ctor_get(x_1567, 1);
lean_inc(x_1569);
lean_dec(x_1567);
x_1570 = lean_ctor_get(x_1569, 0);
lean_inc(x_1570);
lean_dec(x_1569);
x_1571 = lean_ctor_get(x_1570, 0);
lean_inc(x_1571);
lean_dec(x_1570);
x_1572 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_1571, x_1);
if (lean_obj_tag(x_1572) == 0)
{
lean_object* x_1573; uint8_t x_1574; lean_object* x_1575; 
lean_free_object(x_1565);
x_1573 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1;
x_1574 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_1575 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_1, x_1573, x_1574, x_2, x_3, x_4, x_5, x_1568);
if (lean_obj_tag(x_1575) == 0)
{
uint8_t x_1576; 
x_1576 = !lean_is_exclusive(x_1575);
if (x_1576 == 0)
{
lean_object* x_1577; lean_object* x_1578; uint8_t x_1579; 
x_1577 = lean_ctor_get(x_1575, 0);
x_1578 = lean_ctor_get(x_1575, 1);
x_1579 = l_Lean_Expr_hasMVar(x_1);
if (x_1579 == 0)
{
uint8_t x_1580; 
x_1580 = l_Lean_Expr_hasMVar(x_1577);
if (x_1580 == 0)
{
lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; uint8_t x_1586; 
lean_free_object(x_1575);
x_1581 = lean_st_ref_take(x_3, x_1578);
x_1582 = lean_ctor_get(x_1581, 0);
lean_inc(x_1582);
x_1583 = lean_ctor_get(x_1582, 1);
lean_inc(x_1583);
x_1584 = lean_ctor_get(x_1583, 0);
lean_inc(x_1584);
x_1585 = lean_ctor_get(x_1581, 1);
lean_inc(x_1585);
lean_dec(x_1581);
x_1586 = !lean_is_exclusive(x_1582);
if (x_1586 == 0)
{
lean_object* x_1587; uint8_t x_1588; 
x_1587 = lean_ctor_get(x_1582, 1);
lean_dec(x_1587);
x_1588 = !lean_is_exclusive(x_1583);
if (x_1588 == 0)
{
lean_object* x_1589; uint8_t x_1590; 
x_1589 = lean_ctor_get(x_1583, 0);
lean_dec(x_1589);
x_1590 = !lean_is_exclusive(x_1584);
if (x_1590 == 0)
{
lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; uint8_t x_1594; 
x_1591 = lean_ctor_get(x_1584, 0);
lean_inc(x_1577);
x_1592 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1591, x_1, x_1577);
lean_ctor_set(x_1584, 0, x_1592);
x_1593 = lean_st_ref_set(x_3, x_1582, x_1585);
lean_dec(x_3);
x_1594 = !lean_is_exclusive(x_1593);
if (x_1594 == 0)
{
lean_object* x_1595; 
x_1595 = lean_ctor_get(x_1593, 0);
lean_dec(x_1595);
lean_ctor_set(x_1593, 0, x_1577);
return x_1593;
}
else
{
lean_object* x_1596; lean_object* x_1597; 
x_1596 = lean_ctor_get(x_1593, 1);
lean_inc(x_1596);
lean_dec(x_1593);
x_1597 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1597, 0, x_1577);
lean_ctor_set(x_1597, 1, x_1596);
return x_1597;
}
}
else
{
lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; 
x_1598 = lean_ctor_get(x_1584, 0);
x_1599 = lean_ctor_get(x_1584, 1);
lean_inc(x_1599);
lean_inc(x_1598);
lean_dec(x_1584);
lean_inc(x_1577);
x_1600 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1598, x_1, x_1577);
x_1601 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1601, 0, x_1600);
lean_ctor_set(x_1601, 1, x_1599);
lean_ctor_set(x_1583, 0, x_1601);
x_1602 = lean_st_ref_set(x_3, x_1582, x_1585);
lean_dec(x_3);
x_1603 = lean_ctor_get(x_1602, 1);
lean_inc(x_1603);
if (lean_is_exclusive(x_1602)) {
 lean_ctor_release(x_1602, 0);
 lean_ctor_release(x_1602, 1);
 x_1604 = x_1602;
} else {
 lean_dec_ref(x_1602);
 x_1604 = lean_box(0);
}
if (lean_is_scalar(x_1604)) {
 x_1605 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1605 = x_1604;
}
lean_ctor_set(x_1605, 0, x_1577);
lean_ctor_set(x_1605, 1, x_1603);
return x_1605;
}
}
else
{
lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; 
x_1606 = lean_ctor_get(x_1583, 1);
x_1607 = lean_ctor_get(x_1583, 2);
x_1608 = lean_ctor_get(x_1583, 3);
x_1609 = lean_ctor_get(x_1583, 4);
x_1610 = lean_ctor_get(x_1583, 5);
x_1611 = lean_ctor_get(x_1583, 6);
lean_inc(x_1611);
lean_inc(x_1610);
lean_inc(x_1609);
lean_inc(x_1608);
lean_inc(x_1607);
lean_inc(x_1606);
lean_dec(x_1583);
x_1612 = lean_ctor_get(x_1584, 0);
lean_inc(x_1612);
x_1613 = lean_ctor_get(x_1584, 1);
lean_inc(x_1613);
if (lean_is_exclusive(x_1584)) {
 lean_ctor_release(x_1584, 0);
 lean_ctor_release(x_1584, 1);
 x_1614 = x_1584;
} else {
 lean_dec_ref(x_1584);
 x_1614 = lean_box(0);
}
lean_inc(x_1577);
x_1615 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1612, x_1, x_1577);
if (lean_is_scalar(x_1614)) {
 x_1616 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1616 = x_1614;
}
lean_ctor_set(x_1616, 0, x_1615);
lean_ctor_set(x_1616, 1, x_1613);
x_1617 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_1617, 0, x_1616);
lean_ctor_set(x_1617, 1, x_1606);
lean_ctor_set(x_1617, 2, x_1607);
lean_ctor_set(x_1617, 3, x_1608);
lean_ctor_set(x_1617, 4, x_1609);
lean_ctor_set(x_1617, 5, x_1610);
lean_ctor_set(x_1617, 6, x_1611);
lean_ctor_set(x_1582, 1, x_1617);
x_1618 = lean_st_ref_set(x_3, x_1582, x_1585);
lean_dec(x_3);
x_1619 = lean_ctor_get(x_1618, 1);
lean_inc(x_1619);
if (lean_is_exclusive(x_1618)) {
 lean_ctor_release(x_1618, 0);
 lean_ctor_release(x_1618, 1);
 x_1620 = x_1618;
} else {
 lean_dec_ref(x_1618);
 x_1620 = lean_box(0);
}
if (lean_is_scalar(x_1620)) {
 x_1621 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1621 = x_1620;
}
lean_ctor_set(x_1621, 0, x_1577);
lean_ctor_set(x_1621, 1, x_1619);
return x_1621;
}
}
else
{
lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; 
x_1622 = lean_ctor_get(x_1582, 0);
x_1623 = lean_ctor_get(x_1582, 2);
x_1624 = lean_ctor_get(x_1582, 3);
x_1625 = lean_ctor_get(x_1582, 4);
lean_inc(x_1625);
lean_inc(x_1624);
lean_inc(x_1623);
lean_inc(x_1622);
lean_dec(x_1582);
x_1626 = lean_ctor_get(x_1583, 1);
lean_inc(x_1626);
x_1627 = lean_ctor_get(x_1583, 2);
lean_inc(x_1627);
x_1628 = lean_ctor_get(x_1583, 3);
lean_inc(x_1628);
x_1629 = lean_ctor_get(x_1583, 4);
lean_inc(x_1629);
x_1630 = lean_ctor_get(x_1583, 5);
lean_inc(x_1630);
x_1631 = lean_ctor_get(x_1583, 6);
lean_inc(x_1631);
if (lean_is_exclusive(x_1583)) {
 lean_ctor_release(x_1583, 0);
 lean_ctor_release(x_1583, 1);
 lean_ctor_release(x_1583, 2);
 lean_ctor_release(x_1583, 3);
 lean_ctor_release(x_1583, 4);
 lean_ctor_release(x_1583, 5);
 lean_ctor_release(x_1583, 6);
 x_1632 = x_1583;
} else {
 lean_dec_ref(x_1583);
 x_1632 = lean_box(0);
}
x_1633 = lean_ctor_get(x_1584, 0);
lean_inc(x_1633);
x_1634 = lean_ctor_get(x_1584, 1);
lean_inc(x_1634);
if (lean_is_exclusive(x_1584)) {
 lean_ctor_release(x_1584, 0);
 lean_ctor_release(x_1584, 1);
 x_1635 = x_1584;
} else {
 lean_dec_ref(x_1584);
 x_1635 = lean_box(0);
}
lean_inc(x_1577);
x_1636 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1633, x_1, x_1577);
if (lean_is_scalar(x_1635)) {
 x_1637 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1637 = x_1635;
}
lean_ctor_set(x_1637, 0, x_1636);
lean_ctor_set(x_1637, 1, x_1634);
if (lean_is_scalar(x_1632)) {
 x_1638 = lean_alloc_ctor(0, 7, 0);
} else {
 x_1638 = x_1632;
}
lean_ctor_set(x_1638, 0, x_1637);
lean_ctor_set(x_1638, 1, x_1626);
lean_ctor_set(x_1638, 2, x_1627);
lean_ctor_set(x_1638, 3, x_1628);
lean_ctor_set(x_1638, 4, x_1629);
lean_ctor_set(x_1638, 5, x_1630);
lean_ctor_set(x_1638, 6, x_1631);
x_1639 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1639, 0, x_1622);
lean_ctor_set(x_1639, 1, x_1638);
lean_ctor_set(x_1639, 2, x_1623);
lean_ctor_set(x_1639, 3, x_1624);
lean_ctor_set(x_1639, 4, x_1625);
x_1640 = lean_st_ref_set(x_3, x_1639, x_1585);
lean_dec(x_3);
x_1641 = lean_ctor_get(x_1640, 1);
lean_inc(x_1641);
if (lean_is_exclusive(x_1640)) {
 lean_ctor_release(x_1640, 0);
 lean_ctor_release(x_1640, 1);
 x_1642 = x_1640;
} else {
 lean_dec_ref(x_1640);
 x_1642 = lean_box(0);
}
if (lean_is_scalar(x_1642)) {
 x_1643 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1643 = x_1642;
}
lean_ctor_set(x_1643, 0, x_1577);
lean_ctor_set(x_1643, 1, x_1641);
return x_1643;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_1575;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_1575;
}
}
else
{
lean_object* x_1644; lean_object* x_1645; uint8_t x_1646; 
x_1644 = lean_ctor_get(x_1575, 0);
x_1645 = lean_ctor_get(x_1575, 1);
lean_inc(x_1645);
lean_inc(x_1644);
lean_dec(x_1575);
x_1646 = l_Lean_Expr_hasMVar(x_1);
if (x_1646 == 0)
{
uint8_t x_1647; 
x_1647 = l_Lean_Expr_hasMVar(x_1644);
if (x_1647 == 0)
{
lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; 
x_1648 = lean_st_ref_take(x_3, x_1645);
x_1649 = lean_ctor_get(x_1648, 0);
lean_inc(x_1649);
x_1650 = lean_ctor_get(x_1649, 1);
lean_inc(x_1650);
x_1651 = lean_ctor_get(x_1650, 0);
lean_inc(x_1651);
x_1652 = lean_ctor_get(x_1648, 1);
lean_inc(x_1652);
lean_dec(x_1648);
x_1653 = lean_ctor_get(x_1649, 0);
lean_inc(x_1653);
x_1654 = lean_ctor_get(x_1649, 2);
lean_inc(x_1654);
x_1655 = lean_ctor_get(x_1649, 3);
lean_inc(x_1655);
x_1656 = lean_ctor_get(x_1649, 4);
lean_inc(x_1656);
if (lean_is_exclusive(x_1649)) {
 lean_ctor_release(x_1649, 0);
 lean_ctor_release(x_1649, 1);
 lean_ctor_release(x_1649, 2);
 lean_ctor_release(x_1649, 3);
 lean_ctor_release(x_1649, 4);
 x_1657 = x_1649;
} else {
 lean_dec_ref(x_1649);
 x_1657 = lean_box(0);
}
x_1658 = lean_ctor_get(x_1650, 1);
lean_inc(x_1658);
x_1659 = lean_ctor_get(x_1650, 2);
lean_inc(x_1659);
x_1660 = lean_ctor_get(x_1650, 3);
lean_inc(x_1660);
x_1661 = lean_ctor_get(x_1650, 4);
lean_inc(x_1661);
x_1662 = lean_ctor_get(x_1650, 5);
lean_inc(x_1662);
x_1663 = lean_ctor_get(x_1650, 6);
lean_inc(x_1663);
if (lean_is_exclusive(x_1650)) {
 lean_ctor_release(x_1650, 0);
 lean_ctor_release(x_1650, 1);
 lean_ctor_release(x_1650, 2);
 lean_ctor_release(x_1650, 3);
 lean_ctor_release(x_1650, 4);
 lean_ctor_release(x_1650, 5);
 lean_ctor_release(x_1650, 6);
 x_1664 = x_1650;
} else {
 lean_dec_ref(x_1650);
 x_1664 = lean_box(0);
}
x_1665 = lean_ctor_get(x_1651, 0);
lean_inc(x_1665);
x_1666 = lean_ctor_get(x_1651, 1);
lean_inc(x_1666);
if (lean_is_exclusive(x_1651)) {
 lean_ctor_release(x_1651, 0);
 lean_ctor_release(x_1651, 1);
 x_1667 = x_1651;
} else {
 lean_dec_ref(x_1651);
 x_1667 = lean_box(0);
}
lean_inc(x_1644);
x_1668 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1665, x_1, x_1644);
if (lean_is_scalar(x_1667)) {
 x_1669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1669 = x_1667;
}
lean_ctor_set(x_1669, 0, x_1668);
lean_ctor_set(x_1669, 1, x_1666);
if (lean_is_scalar(x_1664)) {
 x_1670 = lean_alloc_ctor(0, 7, 0);
} else {
 x_1670 = x_1664;
}
lean_ctor_set(x_1670, 0, x_1669);
lean_ctor_set(x_1670, 1, x_1658);
lean_ctor_set(x_1670, 2, x_1659);
lean_ctor_set(x_1670, 3, x_1660);
lean_ctor_set(x_1670, 4, x_1661);
lean_ctor_set(x_1670, 5, x_1662);
lean_ctor_set(x_1670, 6, x_1663);
if (lean_is_scalar(x_1657)) {
 x_1671 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1671 = x_1657;
}
lean_ctor_set(x_1671, 0, x_1653);
lean_ctor_set(x_1671, 1, x_1670);
lean_ctor_set(x_1671, 2, x_1654);
lean_ctor_set(x_1671, 3, x_1655);
lean_ctor_set(x_1671, 4, x_1656);
x_1672 = lean_st_ref_set(x_3, x_1671, x_1652);
lean_dec(x_3);
x_1673 = lean_ctor_get(x_1672, 1);
lean_inc(x_1673);
if (lean_is_exclusive(x_1672)) {
 lean_ctor_release(x_1672, 0);
 lean_ctor_release(x_1672, 1);
 x_1674 = x_1672;
} else {
 lean_dec_ref(x_1672);
 x_1674 = lean_box(0);
}
if (lean_is_scalar(x_1674)) {
 x_1675 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1675 = x_1674;
}
lean_ctor_set(x_1675, 0, x_1644);
lean_ctor_set(x_1675, 1, x_1673);
return x_1675;
}
else
{
lean_object* x_1676; 
lean_dec(x_3);
lean_dec(x_1);
x_1676 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1676, 0, x_1644);
lean_ctor_set(x_1676, 1, x_1645);
return x_1676;
}
}
else
{
lean_object* x_1677; 
lean_dec(x_3);
lean_dec(x_1);
x_1677 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1677, 0, x_1644);
lean_ctor_set(x_1677, 1, x_1645);
return x_1677;
}
}
}
else
{
uint8_t x_1678; 
lean_dec(x_3);
lean_dec(x_1);
x_1678 = !lean_is_exclusive(x_1575);
if (x_1678 == 0)
{
return x_1575;
}
else
{
lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; 
x_1679 = lean_ctor_get(x_1575, 0);
x_1680 = lean_ctor_get(x_1575, 1);
lean_inc(x_1680);
lean_inc(x_1679);
lean_dec(x_1575);
x_1681 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1681, 0, x_1679);
lean_ctor_set(x_1681, 1, x_1680);
return x_1681;
}
}
}
else
{
lean_object* x_1682; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1682 = lean_ctor_get(x_1572, 0);
lean_inc(x_1682);
lean_dec(x_1572);
lean_ctor_set(x_1565, 0, x_1682);
return x_1565;
}
}
else
{
lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; 
x_1683 = lean_ctor_get(x_1565, 0);
x_1684 = lean_ctor_get(x_1565, 1);
lean_inc(x_1684);
lean_inc(x_1683);
lean_dec(x_1565);
x_1685 = lean_ctor_get(x_1683, 1);
lean_inc(x_1685);
lean_dec(x_1683);
x_1686 = lean_ctor_get(x_1685, 0);
lean_inc(x_1686);
lean_dec(x_1685);
x_1687 = lean_ctor_get(x_1686, 0);
lean_inc(x_1687);
lean_dec(x_1686);
x_1688 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_1687, x_1);
if (lean_obj_tag(x_1688) == 0)
{
lean_object* x_1689; uint8_t x_1690; lean_object* x_1691; 
x_1689 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1;
x_1690 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_1691 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_1, x_1689, x_1690, x_2, x_3, x_4, x_5, x_1684);
if (lean_obj_tag(x_1691) == 0)
{
lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; uint8_t x_1695; 
x_1692 = lean_ctor_get(x_1691, 0);
lean_inc(x_1692);
x_1693 = lean_ctor_get(x_1691, 1);
lean_inc(x_1693);
if (lean_is_exclusive(x_1691)) {
 lean_ctor_release(x_1691, 0);
 lean_ctor_release(x_1691, 1);
 x_1694 = x_1691;
} else {
 lean_dec_ref(x_1691);
 x_1694 = lean_box(0);
}
x_1695 = l_Lean_Expr_hasMVar(x_1);
if (x_1695 == 0)
{
uint8_t x_1696; 
x_1696 = l_Lean_Expr_hasMVar(x_1692);
if (x_1696 == 0)
{
lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; 
lean_dec(x_1694);
x_1697 = lean_st_ref_take(x_3, x_1693);
x_1698 = lean_ctor_get(x_1697, 0);
lean_inc(x_1698);
x_1699 = lean_ctor_get(x_1698, 1);
lean_inc(x_1699);
x_1700 = lean_ctor_get(x_1699, 0);
lean_inc(x_1700);
x_1701 = lean_ctor_get(x_1697, 1);
lean_inc(x_1701);
lean_dec(x_1697);
x_1702 = lean_ctor_get(x_1698, 0);
lean_inc(x_1702);
x_1703 = lean_ctor_get(x_1698, 2);
lean_inc(x_1703);
x_1704 = lean_ctor_get(x_1698, 3);
lean_inc(x_1704);
x_1705 = lean_ctor_get(x_1698, 4);
lean_inc(x_1705);
if (lean_is_exclusive(x_1698)) {
 lean_ctor_release(x_1698, 0);
 lean_ctor_release(x_1698, 1);
 lean_ctor_release(x_1698, 2);
 lean_ctor_release(x_1698, 3);
 lean_ctor_release(x_1698, 4);
 x_1706 = x_1698;
} else {
 lean_dec_ref(x_1698);
 x_1706 = lean_box(0);
}
x_1707 = lean_ctor_get(x_1699, 1);
lean_inc(x_1707);
x_1708 = lean_ctor_get(x_1699, 2);
lean_inc(x_1708);
x_1709 = lean_ctor_get(x_1699, 3);
lean_inc(x_1709);
x_1710 = lean_ctor_get(x_1699, 4);
lean_inc(x_1710);
x_1711 = lean_ctor_get(x_1699, 5);
lean_inc(x_1711);
x_1712 = lean_ctor_get(x_1699, 6);
lean_inc(x_1712);
if (lean_is_exclusive(x_1699)) {
 lean_ctor_release(x_1699, 0);
 lean_ctor_release(x_1699, 1);
 lean_ctor_release(x_1699, 2);
 lean_ctor_release(x_1699, 3);
 lean_ctor_release(x_1699, 4);
 lean_ctor_release(x_1699, 5);
 lean_ctor_release(x_1699, 6);
 x_1713 = x_1699;
} else {
 lean_dec_ref(x_1699);
 x_1713 = lean_box(0);
}
x_1714 = lean_ctor_get(x_1700, 0);
lean_inc(x_1714);
x_1715 = lean_ctor_get(x_1700, 1);
lean_inc(x_1715);
if (lean_is_exclusive(x_1700)) {
 lean_ctor_release(x_1700, 0);
 lean_ctor_release(x_1700, 1);
 x_1716 = x_1700;
} else {
 lean_dec_ref(x_1700);
 x_1716 = lean_box(0);
}
lean_inc(x_1692);
x_1717 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_1714, x_1, x_1692);
if (lean_is_scalar(x_1716)) {
 x_1718 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1718 = x_1716;
}
lean_ctor_set(x_1718, 0, x_1717);
lean_ctor_set(x_1718, 1, x_1715);
if (lean_is_scalar(x_1713)) {
 x_1719 = lean_alloc_ctor(0, 7, 0);
} else {
 x_1719 = x_1713;
}
lean_ctor_set(x_1719, 0, x_1718);
lean_ctor_set(x_1719, 1, x_1707);
lean_ctor_set(x_1719, 2, x_1708);
lean_ctor_set(x_1719, 3, x_1709);
lean_ctor_set(x_1719, 4, x_1710);
lean_ctor_set(x_1719, 5, x_1711);
lean_ctor_set(x_1719, 6, x_1712);
if (lean_is_scalar(x_1706)) {
 x_1720 = lean_alloc_ctor(0, 5, 0);
} else {
 x_1720 = x_1706;
}
lean_ctor_set(x_1720, 0, x_1702);
lean_ctor_set(x_1720, 1, x_1719);
lean_ctor_set(x_1720, 2, x_1703);
lean_ctor_set(x_1720, 3, x_1704);
lean_ctor_set(x_1720, 4, x_1705);
x_1721 = lean_st_ref_set(x_3, x_1720, x_1701);
lean_dec(x_3);
x_1722 = lean_ctor_get(x_1721, 1);
lean_inc(x_1722);
if (lean_is_exclusive(x_1721)) {
 lean_ctor_release(x_1721, 0);
 lean_ctor_release(x_1721, 1);
 x_1723 = x_1721;
} else {
 lean_dec_ref(x_1721);
 x_1723 = lean_box(0);
}
if (lean_is_scalar(x_1723)) {
 x_1724 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1724 = x_1723;
}
lean_ctor_set(x_1724, 0, x_1692);
lean_ctor_set(x_1724, 1, x_1722);
return x_1724;
}
else
{
lean_object* x_1725; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_1694)) {
 x_1725 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1725 = x_1694;
}
lean_ctor_set(x_1725, 0, x_1692);
lean_ctor_set(x_1725, 1, x_1693);
return x_1725;
}
}
else
{
lean_object* x_1726; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_1694)) {
 x_1726 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1726 = x_1694;
}
lean_ctor_set(x_1726, 0, x_1692);
lean_ctor_set(x_1726, 1, x_1693);
return x_1726;
}
}
else
{
lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; 
lean_dec(x_3);
lean_dec(x_1);
x_1727 = lean_ctor_get(x_1691, 0);
lean_inc(x_1727);
x_1728 = lean_ctor_get(x_1691, 1);
lean_inc(x_1728);
if (lean_is_exclusive(x_1691)) {
 lean_ctor_release(x_1691, 0);
 lean_ctor_release(x_1691, 1);
 x_1729 = x_1691;
} else {
 lean_dec_ref(x_1691);
 x_1729 = lean_box(0);
}
if (lean_is_scalar(x_1729)) {
 x_1730 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1730 = x_1729;
}
lean_ctor_set(x_1730, 0, x_1727);
lean_ctor_set(x_1730, 1, x_1728);
return x_1730;
}
}
else
{
lean_object* x_1731; lean_object* x_1732; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1731 = lean_ctor_get(x_1688, 0);
lean_inc(x_1731);
lean_dec(x_1688);
x_1732 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1732, 0, x_1731);
lean_ctor_set(x_1732, 1, x_1684);
return x_1732;
}
}
}
default: 
{
lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; 
lean_dec(x_1394);
lean_dec(x_1);
x_1733 = lean_ctor_get(x_1393, 1);
lean_inc(x_1733);
lean_dec(x_1393);
x_1734 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3;
x_1735 = l_panic___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__8(x_1734, x_2, x_3, x_4, x_5, x_1733);
return x_1735;
}
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
uint8_t x_40; uint8_t x_41; uint8_t x_42; 
x_40 = lean_ctor_get_uint8(x_38, 9);
x_41 = 1;
x_42 = l_Lean_Meta_TransparencyMode_lt(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = l_Lean_Meta_inferTypeImp_infer(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
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
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
return x_43;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_43, 0);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_43);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; 
lean_ctor_set_uint8(x_38, 9, x_41);
x_52 = l_Lean_Meta_inferTypeImp_infer(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; 
x_61 = lean_ctor_get_uint8(x_38, 0);
x_62 = lean_ctor_get_uint8(x_38, 1);
x_63 = lean_ctor_get_uint8(x_38, 2);
x_64 = lean_ctor_get_uint8(x_38, 3);
x_65 = lean_ctor_get_uint8(x_38, 4);
x_66 = lean_ctor_get_uint8(x_38, 5);
x_67 = lean_ctor_get_uint8(x_38, 6);
x_68 = lean_ctor_get_uint8(x_38, 7);
x_69 = lean_ctor_get_uint8(x_38, 8);
x_70 = lean_ctor_get_uint8(x_38, 9);
x_71 = lean_ctor_get_uint8(x_38, 10);
x_72 = lean_ctor_get_uint8(x_38, 11);
x_73 = lean_ctor_get_uint8(x_38, 12);
lean_dec(x_38);
x_74 = 1;
x_75 = l_Lean_Meta_TransparencyMode_lt(x_70, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_76, 0, x_61);
lean_ctor_set_uint8(x_76, 1, x_62);
lean_ctor_set_uint8(x_76, 2, x_63);
lean_ctor_set_uint8(x_76, 3, x_64);
lean_ctor_set_uint8(x_76, 4, x_65);
lean_ctor_set_uint8(x_76, 5, x_66);
lean_ctor_set_uint8(x_76, 6, x_67);
lean_ctor_set_uint8(x_76, 7, x_68);
lean_ctor_set_uint8(x_76, 8, x_69);
lean_ctor_set_uint8(x_76, 9, x_70);
lean_ctor_set_uint8(x_76, 10, x_71);
lean_ctor_set_uint8(x_76, 11, x_72);
lean_ctor_set_uint8(x_76, 12, x_73);
lean_ctor_set(x_2, 0, x_76);
x_77 = l_Lean_Meta_inferTypeImp_infer(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_84 = x_77;
} else {
 lean_dec_ref(x_77);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_86, 0, x_61);
lean_ctor_set_uint8(x_86, 1, x_62);
lean_ctor_set_uint8(x_86, 2, x_63);
lean_ctor_set_uint8(x_86, 3, x_64);
lean_ctor_set_uint8(x_86, 4, x_65);
lean_ctor_set_uint8(x_86, 5, x_66);
lean_ctor_set_uint8(x_86, 6, x_67);
lean_ctor_set_uint8(x_86, 7, x_68);
lean_ctor_set_uint8(x_86, 8, x_69);
lean_ctor_set_uint8(x_86, 9, x_74);
lean_ctor_set_uint8(x_86, 10, x_71);
lean_ctor_set_uint8(x_86, 11, x_72);
lean_ctor_set_uint8(x_86, 12, x_73);
lean_ctor_set(x_2, 0, x_86);
x_87 = l_Lean_Meta_inferTypeImp_infer(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_87, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_94 = x_87;
} else {
 lean_dec_ref(x_87);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; 
x_96 = lean_ctor_get(x_2, 0);
x_97 = lean_ctor_get(x_2, 1);
x_98 = lean_ctor_get(x_2, 2);
x_99 = lean_ctor_get(x_2, 3);
x_100 = lean_ctor_get(x_2, 4);
x_101 = lean_ctor_get(x_2, 5);
x_102 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_103 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_2);
x_104 = lean_ctor_get_uint8(x_96, 0);
x_105 = lean_ctor_get_uint8(x_96, 1);
x_106 = lean_ctor_get_uint8(x_96, 2);
x_107 = lean_ctor_get_uint8(x_96, 3);
x_108 = lean_ctor_get_uint8(x_96, 4);
x_109 = lean_ctor_get_uint8(x_96, 5);
x_110 = lean_ctor_get_uint8(x_96, 6);
x_111 = lean_ctor_get_uint8(x_96, 7);
x_112 = lean_ctor_get_uint8(x_96, 8);
x_113 = lean_ctor_get_uint8(x_96, 9);
x_114 = lean_ctor_get_uint8(x_96, 10);
x_115 = lean_ctor_get_uint8(x_96, 11);
x_116 = lean_ctor_get_uint8(x_96, 12);
if (lean_is_exclusive(x_96)) {
 x_117 = x_96;
} else {
 lean_dec_ref(x_96);
 x_117 = lean_box(0);
}
x_118 = 1;
x_119 = l_Lean_Meta_TransparencyMode_lt(x_113, x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
if (lean_is_scalar(x_117)) {
 x_120 = lean_alloc_ctor(0, 0, 13);
} else {
 x_120 = x_117;
}
lean_ctor_set_uint8(x_120, 0, x_104);
lean_ctor_set_uint8(x_120, 1, x_105);
lean_ctor_set_uint8(x_120, 2, x_106);
lean_ctor_set_uint8(x_120, 3, x_107);
lean_ctor_set_uint8(x_120, 4, x_108);
lean_ctor_set_uint8(x_120, 5, x_109);
lean_ctor_set_uint8(x_120, 6, x_110);
lean_ctor_set_uint8(x_120, 7, x_111);
lean_ctor_set_uint8(x_120, 8, x_112);
lean_ctor_set_uint8(x_120, 9, x_113);
lean_ctor_set_uint8(x_120, 10, x_114);
lean_ctor_set_uint8(x_120, 11, x_115);
lean_ctor_set_uint8(x_120, 12, x_116);
x_121 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_97);
lean_ctor_set(x_121, 2, x_98);
lean_ctor_set(x_121, 3, x_99);
lean_ctor_set(x_121, 4, x_100);
lean_ctor_set(x_121, 5, x_101);
lean_ctor_set_uint8(x_121, sizeof(void*)*6, x_102);
lean_ctor_set_uint8(x_121, sizeof(void*)*6 + 1, x_103);
x_122 = l_Lean_Meta_inferTypeImp_infer(x_1, x_121, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_122, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_122, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_129 = x_122;
} else {
 lean_dec_ref(x_122);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
if (lean_is_scalar(x_117)) {
 x_131 = lean_alloc_ctor(0, 0, 13);
} else {
 x_131 = x_117;
}
lean_ctor_set_uint8(x_131, 0, x_104);
lean_ctor_set_uint8(x_131, 1, x_105);
lean_ctor_set_uint8(x_131, 2, x_106);
lean_ctor_set_uint8(x_131, 3, x_107);
lean_ctor_set_uint8(x_131, 4, x_108);
lean_ctor_set_uint8(x_131, 5, x_109);
lean_ctor_set_uint8(x_131, 6, x_110);
lean_ctor_set_uint8(x_131, 7, x_111);
lean_ctor_set_uint8(x_131, 8, x_112);
lean_ctor_set_uint8(x_131, 9, x_118);
lean_ctor_set_uint8(x_131, 10, x_114);
lean_ctor_set_uint8(x_131, 11, x_115);
lean_ctor_set_uint8(x_131, 12, x_116);
x_132 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_97);
lean_ctor_set(x_132, 2, x_98);
lean_ctor_set(x_132, 3, x_99);
lean_ctor_set(x_132, 4, x_100);
lean_ctor_set(x_132, 5, x_101);
lean_ctor_set_uint8(x_132, sizeof(void*)*6, x_102);
lean_ctor_set_uint8(x_132, sizeof(void*)*6 + 1, x_103);
x_133 = l_Lean_Meta_inferTypeImp_infer(x_1, x_132, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_133, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_133, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_140 = x_133;
} else {
 lean_dec_ref(x_133);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_152; lean_object* x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; lean_object* x_167; uint8_t x_168; uint8_t x_169; 
lean_dec(x_4);
x_142 = lean_unsigned_to_nat(1u);
x_143 = lean_nat_add(x_10, x_142);
lean_dec(x_10);
x_144 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_144, 0, x_7);
lean_ctor_set(x_144, 1, x_8);
lean_ctor_set(x_144, 2, x_9);
lean_ctor_set(x_144, 3, x_143);
lean_ctor_set(x_144, 4, x_11);
lean_ctor_set(x_144, 5, x_12);
lean_ctor_set(x_144, 6, x_13);
lean_ctor_set(x_144, 7, x_14);
lean_ctor_set(x_144, 8, x_15);
lean_ctor_set(x_144, 9, x_16);
lean_ctor_set(x_144, 10, x_17);
lean_ctor_set(x_144, 11, x_19);
lean_ctor_set_uint8(x_144, sizeof(void*)*12, x_18);
lean_ctor_set_uint8(x_144, sizeof(void*)*12 + 1, x_20);
x_145 = lean_ctor_get(x_2, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_2, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_2, 2);
lean_inc(x_147);
x_148 = lean_ctor_get(x_2, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_2, 4);
lean_inc(x_149);
x_150 = lean_ctor_get(x_2, 5);
lean_inc(x_150);
x_151 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_152 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_153 = x_2;
} else {
 lean_dec_ref(x_2);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get_uint8(x_145, 0);
x_155 = lean_ctor_get_uint8(x_145, 1);
x_156 = lean_ctor_get_uint8(x_145, 2);
x_157 = lean_ctor_get_uint8(x_145, 3);
x_158 = lean_ctor_get_uint8(x_145, 4);
x_159 = lean_ctor_get_uint8(x_145, 5);
x_160 = lean_ctor_get_uint8(x_145, 6);
x_161 = lean_ctor_get_uint8(x_145, 7);
x_162 = lean_ctor_get_uint8(x_145, 8);
x_163 = lean_ctor_get_uint8(x_145, 9);
x_164 = lean_ctor_get_uint8(x_145, 10);
x_165 = lean_ctor_get_uint8(x_145, 11);
x_166 = lean_ctor_get_uint8(x_145, 12);
if (lean_is_exclusive(x_145)) {
 x_167 = x_145;
} else {
 lean_dec_ref(x_145);
 x_167 = lean_box(0);
}
x_168 = 1;
x_169 = l_Lean_Meta_TransparencyMode_lt(x_163, x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
if (lean_is_scalar(x_167)) {
 x_170 = lean_alloc_ctor(0, 0, 13);
} else {
 x_170 = x_167;
}
lean_ctor_set_uint8(x_170, 0, x_154);
lean_ctor_set_uint8(x_170, 1, x_155);
lean_ctor_set_uint8(x_170, 2, x_156);
lean_ctor_set_uint8(x_170, 3, x_157);
lean_ctor_set_uint8(x_170, 4, x_158);
lean_ctor_set_uint8(x_170, 5, x_159);
lean_ctor_set_uint8(x_170, 6, x_160);
lean_ctor_set_uint8(x_170, 7, x_161);
lean_ctor_set_uint8(x_170, 8, x_162);
lean_ctor_set_uint8(x_170, 9, x_163);
lean_ctor_set_uint8(x_170, 10, x_164);
lean_ctor_set_uint8(x_170, 11, x_165);
lean_ctor_set_uint8(x_170, 12, x_166);
if (lean_is_scalar(x_153)) {
 x_171 = lean_alloc_ctor(0, 6, 2);
} else {
 x_171 = x_153;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_146);
lean_ctor_set(x_171, 2, x_147);
lean_ctor_set(x_171, 3, x_148);
lean_ctor_set(x_171, 4, x_149);
lean_ctor_set(x_171, 5, x_150);
lean_ctor_set_uint8(x_171, sizeof(void*)*6, x_151);
lean_ctor_set_uint8(x_171, sizeof(void*)*6 + 1, x_152);
x_172 = l_Lean_Meta_inferTypeImp_infer(x_1, x_171, x_3, x_144, x_5, x_6);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_175 = x_172;
} else {
 lean_dec_ref(x_172);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_172, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_172, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_179 = x_172;
} else {
 lean_dec_ref(x_172);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
if (lean_is_scalar(x_167)) {
 x_181 = lean_alloc_ctor(0, 0, 13);
} else {
 x_181 = x_167;
}
lean_ctor_set_uint8(x_181, 0, x_154);
lean_ctor_set_uint8(x_181, 1, x_155);
lean_ctor_set_uint8(x_181, 2, x_156);
lean_ctor_set_uint8(x_181, 3, x_157);
lean_ctor_set_uint8(x_181, 4, x_158);
lean_ctor_set_uint8(x_181, 5, x_159);
lean_ctor_set_uint8(x_181, 6, x_160);
lean_ctor_set_uint8(x_181, 7, x_161);
lean_ctor_set_uint8(x_181, 8, x_162);
lean_ctor_set_uint8(x_181, 9, x_168);
lean_ctor_set_uint8(x_181, 10, x_164);
lean_ctor_set_uint8(x_181, 11, x_165);
lean_ctor_set_uint8(x_181, 12, x_166);
if (lean_is_scalar(x_153)) {
 x_182 = lean_alloc_ctor(0, 6, 2);
} else {
 x_182 = x_153;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_146);
lean_ctor_set(x_182, 2, x_147);
lean_ctor_set(x_182, 3, x_148);
lean_ctor_set(x_182, 4, x_149);
lean_ctor_set(x_182, 5, x_150);
lean_ctor_set_uint8(x_182, sizeof(void*)*6, x_151);
lean_ctor_set_uint8(x_182, sizeof(void*)*6 + 1, x_152);
x_183 = l_Lean_Meta_inferTypeImp_infer(x_1, x_182, x_3, x_144, x_5, x_6);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_188 = lean_ctor_get(x_183, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_183, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_190 = x_183;
} else {
 lean_dec_ref(x_183);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
}
else
{
lean_object* x_192; 
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
x_192 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1(x_12, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_192;
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
x_7 = lean_expr_eqv(x_6, x_1);
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
l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__1 = _init_l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__1();
lean_mark_persistent(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__1);
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
l_panic___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__8___closed__1 = _init_l_panic___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__8___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__8___closed__1);
l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1 = _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1();
lean_mark_persistent(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1);
l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2 = _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2();
lean_mark_persistent(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__2);
l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3 = _init_l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3();
lean_mark_persistent(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__3);
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
