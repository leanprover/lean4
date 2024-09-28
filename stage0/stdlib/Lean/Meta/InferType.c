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
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwFunctionExpected___rarg___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_withLocalDecl_x27___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwFunctionExpected___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownMVar___spec__1(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__4;
static lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___rarg___closed__1;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__10;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_arrowDomainsN___spec__3(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_withLocalDecl_x27___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownMVar___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
static lean_object* l_Lean_Meta_throwTypeExcepted___rarg___closed__2;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_isPropFormerType___closed__1;
lean_object* l_Lean_Literal_type(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__2;
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__3;
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_Meta_isPropFormerType___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwTypeExcepted___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownMVar___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwIncorrectNumberOfLevels___spec__1(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__11;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
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
static lean_object* l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__8;
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwUnknownMVar___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp_infer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at_Lean_Meta_arrowDomainsN___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___rarg(lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__7;
LEAN_EXPORT uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Meta_arrowDomainsN___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object*);
extern lean_object* l_Lean_ExprStructEq_instHashable;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_withLocalDecl_x27(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
extern lean_object* l_Id_instMonad;
extern lean_object* l_Lean_ExprStructEq_instBEq;
LEAN_EXPORT lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_inferTypeImp_infer___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_inferTypeImp_infer___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwFunctionExpected___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
extern lean_object* l_instBEqNat;
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
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__6;
lean_object* l_Lean_Level_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__7;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_Expr_instantiateBetaRevRange_visit___spec__7___boxed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwTypeExcepted___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_instHashableNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ExprStructEq_instBEq;
x_2 = l_instBEqNat;
x_3 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instHashableNat___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ExprStructEq_instHashable;
x_2 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__2;
x_3 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.InferType", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Expr.instantiateBetaRevRange.visit", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__4;
x_2 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__5;
x_3 = lean_unsigned_to_nat(63u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__4;
x_2 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__5;
x_3 = lean_unsigned_to_nat(64u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__4;
x_2 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__5;
x_3 = lean_unsigned_to_nat(65u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__4;
x_2 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__5;
x_3 = lean_unsigned_to_nat(62u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__4;
x_2 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__5;
x_3 = lean_unsigned_to_nat(66u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
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
x_270 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__7;
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
x_358 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__8;
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
x_446 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__9;
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
x_534 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__10;
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
x_625 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__1;
x_626 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__3;
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
x_788 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__11;
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
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__4;
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_24; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_3, x_16);
lean_dec(x_3);
x_24 = lean_ctor_get(x_7, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 7)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_18 = x_28;
x_19 = x_12;
goto block_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_dec(x_7);
x_30 = l_Lean_Expr_instantiateBetaRevRange(x_24, x_29, x_4, x_2);
lean_dec(x_29);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_31 = lean_whnf(x_30, x_8, x_9, x_10, x_11, x_12);
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
lean_inc(x_4);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_4);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_18 = x_36;
x_19 = x_33;
goto block_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_32);
lean_dec(x_17);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
x_39 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_38, x_2, x_14, x_1);
lean_dec(x_38);
x_40 = l_Lean_Meta_throwFunctionExpected___rarg(x_39, x_8, x_9, x_10, x_11, x_37);
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
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_31);
if (x_45 == 0)
{
return x_31;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_31, 0);
x_47 = lean_ctor_get(x_31, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_31);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
block_23:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_17;
x_4 = x_21;
x_7 = x_20;
x_12 = x_19;
goto _start;
}
}
else
{
lean_object* x_49; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_7);
lean_ctor_set(x_49, 1, x_12);
return x_49;
}
}
else
{
lean_object* x_50; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_7);
lean_ctor_set(x_50, 1, x_12);
return x_50;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_array_get_size(x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_unsigned_to_nat(1u);
lean_inc(x_11);
x_15 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_2, x_11, x_12, x_11, x_14, x_13, x_3, x_4, x_5, x_6, x_10);
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
x_20 = l_Lean_Expr_instantiateBetaRevRange(x_18, x_19, x_11, x_2);
lean_dec(x_11);
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
x_25 = l_Lean_Expr_instantiateBetaRevRange(x_23, x_24, x_11, x_2);
lean_dec(x_11);
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
lean_dec(x_11);
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
uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
return x_8;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_13;
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
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid projection", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_4, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_25; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_4, x_17);
lean_dec(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_25 = lean_whnf(x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 7)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 2);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Expr_hasLooseBVars(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_19 = x_30;
x_20 = x_27;
goto block_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_inc(x_3);
lean_inc(x_5);
lean_inc(x_1);
x_31 = l_Lean_Expr_proj___override(x_1, x_5, x_3);
x_32 = lean_expr_instantiate1(x_28, x_31);
lean_dec(x_31);
lean_dec(x_28);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_19 = x_33;
x_20 = x_27;
goto block_24;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_26);
lean_dec(x_18);
lean_dec(x_5);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
x_35 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_36 = l_Lean_indentExpr(x_35);
x_37 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_40, x_9, x_10, x_11, x_12, x_34);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
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
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
block_24:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_18;
x_5 = x_22;
x_8 = x_21;
x_13 = x_20;
goto _start;
}
}
else
{
lean_object* x_50; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_8);
lean_ctor_set(x_50, 1, x_13);
return x_50;
}
}
else
{
lean_object* x_51; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_8);
lean_ctor_set(x_51, 1, x_13);
return x_51;
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_17);
lean_dec(x_13);
x_24 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_25 = l_Lean_indentExpr(x_24);
x_26 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_25);
lean_ctor_set(x_18, 0, x_26);
x_27 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_28, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
if (lean_obj_tag(x_30) == 5)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*6);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_31, 2);
lean_inc(x_33);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_13);
x_36 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_37 = l_Lean_indentExpr(x_36);
x_38 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_37);
lean_ctor_set(x_18, 0, x_38);
x_39 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_18);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_40, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_31, 4);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_13);
x_43 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_44 = l_Lean_indentExpr(x_43);
x_45 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_44);
lean_ctor_set(x_18, 0, x_45);
x_46 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_18);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_47, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_48;
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_42);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_42, 0);
x_52 = lean_ctor_get(x_42, 1);
lean_dec(x_52);
x_53 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_51, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 6)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_31, 1);
lean_inc(x_57);
lean_dec(x_31);
x_58 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_13, x_34);
x_59 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__1;
lean_inc(x_58);
x_60 = lean_mk_array(x_58, x_59);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_sub(x_58, x_61);
lean_dec(x_58);
x_63 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_13, x_60, x_62);
x_64 = lean_array_get_size(x_63);
x_65 = lean_nat_dec_eq(x_57, x_64);
lean_dec(x_64);
lean_dec(x_57);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_63);
lean_dec(x_56);
lean_dec(x_17);
x_66 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_67 = l_Lean_indentExpr(x_66);
x_68 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_42, 7);
lean_ctor_set(x_42, 1, x_67);
lean_ctor_set(x_42, 0, x_68);
x_69 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_69);
lean_ctor_set(x_18, 0, x_42);
x_70 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_18, x_4, x_5, x_6, x_7, x_55);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_56, 0);
lean_inc(x_71);
lean_dec(x_56);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Lean_Expr_const___override(x_72, x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_74 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_73, x_63, x_4, x_5, x_6, x_7, x_55);
lean_dec(x_63);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_n(x_2, 2);
lean_inc(x_1);
x_77 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2(x_1, x_2, x_3, x_2, x_34, x_2, x_61, x_75, x_4, x_5, x_6, x_7, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_80 = lean_whnf(x_78, x_4, x_5, x_6, x_7, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 7)
{
uint8_t x_82; 
lean_free_object(x_42);
lean_free_object(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_80, 0);
lean_dec(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_expr_consume_type_annotations(x_84);
lean_ctor_set(x_80, 0, x_85);
return x_80;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_dec(x_80);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_dec(x_81);
x_88 = lean_expr_consume_type_annotations(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_81);
x_90 = lean_ctor_get(x_80, 1);
lean_inc(x_90);
lean_dec(x_80);
x_91 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_92 = l_Lean_indentExpr(x_91);
x_93 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_42, 7);
lean_ctor_set(x_42, 1, x_92);
lean_ctor_set(x_42, 0, x_93);
x_94 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_94);
lean_ctor_set(x_18, 0, x_42);
x_95 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_18, x_4, x_5, x_6, x_7, x_90);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_95;
}
}
else
{
uint8_t x_96; 
lean_free_object(x_42);
lean_free_object(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_80);
if (x_96 == 0)
{
return x_80;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_80, 0);
x_98 = lean_ctor_get(x_80, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_80);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_free_object(x_42);
lean_free_object(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_77);
if (x_100 == 0)
{
return x_77;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_77, 0);
x_102 = lean_ctor_get(x_77, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_77);
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
lean_free_object(x_42);
lean_free_object(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_74);
if (x_104 == 0)
{
return x_74;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_74, 0);
x_106 = lean_ctor_get(x_74, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_74);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_54);
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_13);
x_108 = lean_ctor_get(x_53, 1);
lean_inc(x_108);
lean_dec(x_53);
x_109 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_110 = l_Lean_indentExpr(x_109);
x_111 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_42, 7);
lean_ctor_set(x_42, 1, x_110);
lean_ctor_set(x_42, 0, x_111);
x_112 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_112);
lean_ctor_set(x_18, 0, x_42);
x_113 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_18, x_4, x_5, x_6, x_7, x_108);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_free_object(x_42);
lean_dec(x_31);
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
x_114 = !lean_is_exclusive(x_53);
if (x_114 == 0)
{
return x_53;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_53, 0);
x_116 = lean_ctor_get(x_53, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_53);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_42, 0);
lean_inc(x_118);
lean_dec(x_42);
x_119 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_118, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 6)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_ctor_get(x_31, 1);
lean_inc(x_123);
lean_dec(x_31);
x_124 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_13, x_34);
x_125 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__1;
lean_inc(x_124);
x_126 = lean_mk_array(x_124, x_125);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_nat_sub(x_124, x_127);
lean_dec(x_124);
x_129 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_13, x_126, x_128);
x_130 = lean_array_get_size(x_129);
x_131 = lean_nat_dec_eq(x_123, x_130);
lean_dec(x_130);
lean_dec(x_123);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_129);
lean_dec(x_122);
lean_dec(x_17);
x_132 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_133 = l_Lean_indentExpr(x_132);
x_134 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_136);
lean_ctor_set(x_18, 0, x_135);
x_137 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_18, x_4, x_5, x_6, x_7, x_121);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_122, 0);
lean_inc(x_138);
lean_dec(x_122);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec(x_138);
x_140 = l_Lean_Expr_const___override(x_139, x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_141 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_140, x_129, x_4, x_5, x_6, x_7, x_121);
lean_dec(x_129);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_n(x_2, 2);
lean_inc(x_1);
x_144 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2(x_1, x_2, x_3, x_2, x_34, x_2, x_127, x_142, x_4, x_5, x_6, x_7, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_147 = lean_whnf(x_145, x_4, x_5, x_6, x_7, x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 7)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_free_object(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
lean_dec(x_148);
x_152 = lean_expr_consume_type_annotations(x_151);
if (lean_is_scalar(x_150)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_150;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_149);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_148);
x_154 = lean_ctor_get(x_147, 1);
lean_inc(x_154);
lean_dec(x_147);
x_155 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_156 = l_Lean_indentExpr(x_155);
x_157 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
x_159 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_159);
lean_ctor_set(x_18, 0, x_158);
x_160 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_18, x_4, x_5, x_6, x_7, x_154);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_free_object(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_ctor_get(x_147, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_147, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_163 = x_147;
} else {
 lean_dec_ref(x_147);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_free_object(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_165 = lean_ctor_get(x_144, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_144, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_167 = x_144;
} else {
 lean_dec_ref(x_144);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_free_object(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = lean_ctor_get(x_141, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_141, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_171 = x_141;
} else {
 lean_dec_ref(x_141);
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
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_120);
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_13);
x_173 = lean_ctor_get(x_119, 1);
lean_inc(x_173);
lean_dec(x_119);
x_174 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_175 = l_Lean_indentExpr(x_174);
x_176 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
x_178 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_178);
lean_ctor_set(x_18, 0, x_177);
x_179 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_18, x_4, x_5, x_6, x_7, x_173);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_31);
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
x_180 = lean_ctor_get(x_119, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_119, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_182 = x_119;
} else {
 lean_dec_ref(x_119);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_31);
lean_free_object(x_18);
lean_dec(x_17);
lean_dec(x_13);
x_184 = !lean_is_exclusive(x_42);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = lean_ctor_get(x_42, 1);
lean_dec(x_185);
x_186 = lean_ctor_get(x_42, 0);
lean_dec(x_186);
x_187 = !lean_is_exclusive(x_49);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_188 = lean_ctor_get(x_49, 1);
lean_dec(x_188);
x_189 = lean_ctor_get(x_49, 0);
lean_dec(x_189);
x_190 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_191 = l_Lean_indentExpr(x_190);
x_192 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_49, 7);
lean_ctor_set(x_49, 1, x_191);
lean_ctor_set(x_49, 0, x_192);
x_193 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
lean_ctor_set_tag(x_42, 7);
lean_ctor_set(x_42, 1, x_193);
lean_ctor_set(x_42, 0, x_49);
x_194 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_42, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_49);
x_195 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_196 = l_Lean_indentExpr(x_195);
x_197 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
x_199 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
lean_ctor_set_tag(x_42, 7);
lean_ctor_set(x_42, 1, x_199);
lean_ctor_set(x_42, 0, x_198);
x_200 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_42, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_42);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_201 = x_49;
} else {
 lean_dec_ref(x_49);
 x_201 = lean_box(0);
}
x_202 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_203 = l_Lean_indentExpr(x_202);
x_204 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
if (lean_is_scalar(x_201)) {
 x_205 = lean_alloc_ctor(7, 2, 0);
} else {
 x_205 = x_201;
 lean_ctor_set_tag(x_205, 7);
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_203);
x_206 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_207 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_207, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_208;
}
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_13);
x_209 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_210 = l_Lean_indentExpr(x_209);
x_211 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_210);
lean_ctor_set(x_18, 0, x_211);
x_212 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_213 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_213, 0, x_18);
lean_ctor_set(x_213, 1, x_212);
x_214 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_213, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_30);
lean_dec(x_17);
lean_dec(x_13);
x_215 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_216 = l_Lean_indentExpr(x_215);
x_217 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_216);
lean_ctor_set(x_18, 0, x_217);
x_218 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_219 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_219, 0, x_18);
lean_ctor_set(x_219, 1, x_218);
x_220 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_219, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_220;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_18, 0);
x_222 = lean_ctor_get(x_18, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_18);
x_223 = lean_ctor_get(x_221, 0);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_environment_find(x_223, x_16);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_17);
lean_dec(x_13);
x_225 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_226 = l_Lean_indentExpr(x_225);
x_227 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_228 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_226);
x_229 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_230 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
x_231 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_230, x_4, x_5, x_6, x_7, x_222);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_231;
}
else
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_224, 0);
lean_inc(x_232);
lean_dec(x_224);
if (lean_obj_tag(x_232) == 5)
{
lean_object* x_233; uint8_t x_234; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
lean_dec(x_232);
x_234 = lean_ctor_get_uint8(x_233, sizeof(void*)*6);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_235 = lean_ctor_get(x_233, 2);
lean_inc(x_235);
x_236 = lean_unsigned_to_nat(0u);
x_237 = lean_nat_dec_eq(x_235, x_236);
lean_dec(x_235);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_233);
lean_dec(x_17);
lean_dec(x_13);
x_238 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_239 = l_Lean_indentExpr(x_238);
x_240 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_241 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
x_242 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_243 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_243, x_4, x_5, x_6, x_7, x_222);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_244;
}
else
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_233, 4);
lean_inc(x_245);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_233);
lean_dec(x_17);
lean_dec(x_13);
x_246 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_247 = l_Lean_indentExpr(x_246);
x_248 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_249 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_250 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_251 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_251, x_4, x_5, x_6, x_7, x_222);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_252;
}
else
{
lean_object* x_253; 
x_253 = lean_ctor_get(x_245, 1);
lean_inc(x_253);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_245, 0);
lean_inc(x_254);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_255 = x_245;
} else {
 lean_dec_ref(x_245);
 x_255 = lean_box(0);
}
x_256 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_254, x_4, x_5, x_6, x_7, x_222);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
if (lean_obj_tag(x_257) == 6)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_ctor_get(x_257, 0);
lean_inc(x_259);
lean_dec(x_257);
x_260 = lean_ctor_get(x_233, 1);
lean_inc(x_260);
lean_dec(x_233);
x_261 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_13, x_236);
x_262 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__1;
lean_inc(x_261);
x_263 = lean_mk_array(x_261, x_262);
x_264 = lean_unsigned_to_nat(1u);
x_265 = lean_nat_sub(x_261, x_264);
lean_dec(x_261);
x_266 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_13, x_263, x_265);
x_267 = lean_array_get_size(x_266);
x_268 = lean_nat_dec_eq(x_260, x_267);
lean_dec(x_267);
lean_dec(x_260);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_266);
lean_dec(x_259);
lean_dec(x_17);
x_269 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_270 = l_Lean_indentExpr(x_269);
x_271 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
if (lean_is_scalar(x_255)) {
 x_272 = lean_alloc_ctor(7, 2, 0);
} else {
 x_272 = x_255;
 lean_ctor_set_tag(x_272, 7);
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_270);
x_273 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_274 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
x_275 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_274, x_4, x_5, x_6, x_7, x_258);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_275;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_259, 0);
lean_inc(x_276);
lean_dec(x_259);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
lean_dec(x_276);
x_278 = l_Lean_Expr_const___override(x_277, x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_279 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_278, x_266, x_4, x_5, x_6, x_7, x_258);
lean_dec(x_266);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_n(x_2, 2);
lean_inc(x_1);
x_282 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2(x_1, x_2, x_3, x_2, x_236, x_2, x_264, x_280, x_4, x_5, x_6, x_7, x_281);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_285 = lean_whnf(x_283, x_4, x_5, x_6, x_7, x_284);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
if (lean_obj_tag(x_286) == 7)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_255);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_289 = lean_ctor_get(x_286, 1);
lean_inc(x_289);
lean_dec(x_286);
x_290 = lean_expr_consume_type_annotations(x_289);
if (lean_is_scalar(x_288)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_288;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_287);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_286);
x_292 = lean_ctor_get(x_285, 1);
lean_inc(x_292);
lean_dec(x_285);
x_293 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_294 = l_Lean_indentExpr(x_293);
x_295 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
if (lean_is_scalar(x_255)) {
 x_296 = lean_alloc_ctor(7, 2, 0);
} else {
 x_296 = x_255;
 lean_ctor_set_tag(x_296, 7);
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_294);
x_297 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_298 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
x_299 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_298, x_4, x_5, x_6, x_7, x_292);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_255);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_300 = lean_ctor_get(x_285, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_285, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_302 = x_285;
} else {
 lean_dec_ref(x_285);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_301);
return x_303;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_255);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_304 = lean_ctor_get(x_282, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_282, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_306 = x_282;
} else {
 lean_dec_ref(x_282);
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
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_255);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_308 = lean_ctor_get(x_279, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_279, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_310 = x_279;
} else {
 lean_dec_ref(x_279);
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
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_257);
lean_dec(x_233);
lean_dec(x_17);
lean_dec(x_13);
x_312 = lean_ctor_get(x_256, 1);
lean_inc(x_312);
lean_dec(x_256);
x_313 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_314 = l_Lean_indentExpr(x_313);
x_315 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
if (lean_is_scalar(x_255)) {
 x_316 = lean_alloc_ctor(7, 2, 0);
} else {
 x_316 = x_255;
 lean_ctor_set_tag(x_316, 7);
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_314);
x_317 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_318 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
x_319 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_318, x_4, x_5, x_6, x_7, x_312);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_319;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_255);
lean_dec(x_233);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_320 = lean_ctor_get(x_256, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_256, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_322 = x_256;
} else {
 lean_dec_ref(x_256);
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
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_233);
lean_dec(x_17);
lean_dec(x_13);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_324 = x_245;
} else {
 lean_dec_ref(x_245);
 x_324 = lean_box(0);
}
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_325 = x_253;
} else {
 lean_dec_ref(x_253);
 x_325 = lean_box(0);
}
x_326 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_327 = l_Lean_indentExpr(x_326);
x_328 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
if (lean_is_scalar(x_325)) {
 x_329 = lean_alloc_ctor(7, 2, 0);
} else {
 x_329 = x_325;
 lean_ctor_set_tag(x_329, 7);
}
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_327);
x_330 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
if (lean_is_scalar(x_324)) {
 x_331 = lean_alloc_ctor(7, 2, 0);
} else {
 x_331 = x_324;
 lean_ctor_set_tag(x_331, 7);
}
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
x_332 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_331, x_4, x_5, x_6, x_7, x_222);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_332;
}
}
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_233);
lean_dec(x_17);
lean_dec(x_13);
x_333 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_334 = l_Lean_indentExpr(x_333);
x_335 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_336 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_334);
x_337 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_338 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
x_339 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_338, x_4, x_5, x_6, x_7, x_222);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_339;
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_232);
lean_dec(x_17);
lean_dec(x_13);
x_340 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_341 = l_Lean_indentExpr(x_340);
x_342 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_343 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_341);
x_344 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_345 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
x_346 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_345, x_4, x_5, x_6, x_7, x_222);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_346;
}
}
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_15);
lean_dec(x_13);
x_347 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_348 = l_Lean_indentExpr(x_347);
x_349 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_350 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_348);
x_351 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_352 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
x_353 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_352, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_353;
}
}
else
{
uint8_t x_354; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_354 = !lean_is_exclusive(x_12);
if (x_354 == 0)
{
return x_12;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_12, 0);
x_356 = lean_ctor_get(x_12, 1);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_12);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
}
}
else
{
uint8_t x_358; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_358 = !lean_is_exclusive(x_9);
if (x_358 == 0)
{
return x_9;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_9, 0);
x_360 = lean_ctor_get(x_9, 1);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_9);
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
return x_361;
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
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
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_4, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_13, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_free_object(x_8);
lean_inc(x_4);
x_15 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_Expr_hasMVar(x_1);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Expr_hasMVar(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_free_object(x_15);
x_21 = lean_st_ref_take(x_4, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_22, 1);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_17);
x_29 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_28, x_1, x_17);
lean_ctor_set(x_23, 0, x_29);
x_30 = lean_st_ref_set(x_4, x_22, x_24);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_17);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_17);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
x_37 = lean_ctor_get(x_23, 2);
x_38 = lean_ctor_get(x_23, 3);
x_39 = lean_ctor_get(x_23, 4);
x_40 = lean_ctor_get(x_23, 5);
x_41 = lean_ctor_get(x_23, 6);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
lean_inc(x_17);
x_42 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_35, x_1, x_17);
x_43 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
lean_ctor_set(x_43, 2, x_37);
lean_ctor_set(x_43, 3, x_38);
lean_ctor_set(x_43, 4, x_39);
lean_ctor_set(x_43, 5, x_40);
lean_ctor_set(x_43, 6, x_41);
lean_ctor_set(x_22, 1, x_43);
x_44 = lean_st_ref_set(x_4, x_22, x_24);
lean_dec(x_4);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_17);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_48 = lean_ctor_get(x_22, 0);
x_49 = lean_ctor_get(x_22, 2);
x_50 = lean_ctor_get(x_22, 3);
x_51 = lean_ctor_get(x_22, 4);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_22);
x_52 = lean_ctor_get(x_23, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_23, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_23, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_23, 3);
lean_inc(x_55);
x_56 = lean_ctor_get(x_23, 4);
lean_inc(x_56);
x_57 = lean_ctor_get(x_23, 5);
lean_inc(x_57);
x_58 = lean_ctor_get(x_23, 6);
lean_inc(x_58);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 lean_ctor_release(x_23, 5);
 lean_ctor_release(x_23, 6);
 x_59 = x_23;
} else {
 lean_dec_ref(x_23);
 x_59 = lean_box(0);
}
lean_inc(x_17);
x_60 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_52, x_1, x_17);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 7, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_53);
lean_ctor_set(x_61, 2, x_54);
lean_ctor_set(x_61, 3, x_55);
lean_ctor_set(x_61, 4, x_56);
lean_ctor_set(x_61, 5, x_57);
lean_ctor_set(x_61, 6, x_58);
x_62 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_62, 0, x_48);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_49);
lean_ctor_set(x_62, 3, x_50);
lean_ctor_set(x_62, 4, x_51);
x_63 = lean_st_ref_set(x_4, x_62, x_24);
lean_dec(x_4);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_17);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_15, 0);
x_68 = lean_ctor_get(x_15, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_15);
x_69 = l_Lean_Expr_hasMVar(x_1);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_hasMVar(x_67);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_71 = lean_st_ref_take(x_4, x_68);
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
x_86 = lean_ctor_get(x_73, 6);
lean_inc(x_86);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 lean_ctor_release(x_73, 3);
 lean_ctor_release(x_73, 4);
 lean_ctor_release(x_73, 5);
 lean_ctor_release(x_73, 6);
 x_87 = x_73;
} else {
 lean_dec_ref(x_73);
 x_87 = lean_box(0);
}
lean_inc(x_67);
x_88 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_80, x_1, x_67);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 7, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_81);
lean_ctor_set(x_89, 2, x_82);
lean_ctor_set(x_89, 3, x_83);
lean_ctor_set(x_89, 4, x_84);
lean_ctor_set(x_89, 5, x_85);
lean_ctor_set(x_89, 6, x_86);
if (lean_is_scalar(x_79)) {
 x_90 = lean_alloc_ctor(0, 5, 0);
} else {
 x_90 = x_79;
}
lean_ctor_set(x_90, 0, x_75);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_76);
lean_ctor_set(x_90, 3, x_77);
lean_ctor_set(x_90, 4, x_78);
x_91 = lean_st_ref_set(x_4, x_90, x_74);
lean_dec(x_4);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_67);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
else
{
lean_object* x_95; 
lean_dec(x_4);
lean_dec(x_1);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_67);
lean_ctor_set(x_95, 1, x_68);
return x_95;
}
}
else
{
lean_object* x_96; 
lean_dec(x_4);
lean_dec(x_1);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_67);
lean_ctor_set(x_96, 1, x_68);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_4);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_15);
if (x_97 == 0)
{
return x_15;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_15, 0);
x_99 = lean_ctor_get(x_15, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_15);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_ctor_get(x_14, 0);
lean_inc(x_101);
lean_dec(x_14);
lean_ctor_set(x_8, 0, x_101);
return x_8;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_8, 0);
x_103 = lean_ctor_get(x_8, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_8);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec(x_104);
x_106 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_105, x_1);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
lean_inc(x_4);
x_107 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_103);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = l_Lean_Expr_hasMVar(x_1);
if (x_111 == 0)
{
uint8_t x_112; 
x_112 = l_Lean_Expr_hasMVar(x_108);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_110);
x_113 = lean_st_ref_take(x_4, x_109);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_ctor_get(x_114, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_114, 4);
lean_inc(x_120);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 lean_ctor_release(x_114, 3);
 lean_ctor_release(x_114, 4);
 x_121 = x_114;
} else {
 lean_dec_ref(x_114);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_115, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_115, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_115, 2);
lean_inc(x_124);
x_125 = lean_ctor_get(x_115, 3);
lean_inc(x_125);
x_126 = lean_ctor_get(x_115, 4);
lean_inc(x_126);
x_127 = lean_ctor_get(x_115, 5);
lean_inc(x_127);
x_128 = lean_ctor_get(x_115, 6);
lean_inc(x_128);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 lean_ctor_release(x_115, 2);
 lean_ctor_release(x_115, 3);
 lean_ctor_release(x_115, 4);
 lean_ctor_release(x_115, 5);
 lean_ctor_release(x_115, 6);
 x_129 = x_115;
} else {
 lean_dec_ref(x_115);
 x_129 = lean_box(0);
}
lean_inc(x_108);
x_130 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_122, x_1, x_108);
if (lean_is_scalar(x_129)) {
 x_131 = lean_alloc_ctor(0, 7, 0);
} else {
 x_131 = x_129;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_123);
lean_ctor_set(x_131, 2, x_124);
lean_ctor_set(x_131, 3, x_125);
lean_ctor_set(x_131, 4, x_126);
lean_ctor_set(x_131, 5, x_127);
lean_ctor_set(x_131, 6, x_128);
if (lean_is_scalar(x_121)) {
 x_132 = lean_alloc_ctor(0, 5, 0);
} else {
 x_132 = x_121;
}
lean_ctor_set(x_132, 0, x_117);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set(x_132, 2, x_118);
lean_ctor_set(x_132, 3, x_119);
lean_ctor_set(x_132, 4, x_120);
x_133 = lean_st_ref_set(x_4, x_132, x_116);
lean_dec(x_4);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_108);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
else
{
lean_object* x_137; 
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_110)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_110;
}
lean_ctor_set(x_137, 0, x_108);
lean_ctor_set(x_137, 1, x_109);
return x_137;
}
}
else
{
lean_object* x_138; 
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_110)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_110;
}
lean_ctor_set(x_138, 0, x_108);
lean_ctor_set(x_138, 1, x_109);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_4);
lean_dec(x_1);
x_139 = lean_ctor_get(x_107, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_107, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_141 = x_107;
} else {
 lean_dec_ref(x_107);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_143 = lean_ctor_get(x_106, 0);
lean_inc(x_143);
lean_dec(x_106);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_103);
return x_144;
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
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_st_ref_get(x_3, x_6);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_33, x_1);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_free_object(x_28);
x_35 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_27, x_23, x_2, x_3, x_4, x_5, x_31);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = l_Lean_Expr_hasMVar(x_1);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Expr_hasMVar(x_37);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_free_object(x_35);
x_41 = lean_st_ref_take(x_3, x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_42, 1);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_37);
x_49 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_48, x_1, x_37);
lean_ctor_set(x_43, 0, x_49);
x_50 = lean_st_ref_set(x_3, x_42, x_44);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_37);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_37);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_55 = lean_ctor_get(x_43, 0);
x_56 = lean_ctor_get(x_43, 1);
x_57 = lean_ctor_get(x_43, 2);
x_58 = lean_ctor_get(x_43, 3);
x_59 = lean_ctor_get(x_43, 4);
x_60 = lean_ctor_get(x_43, 5);
x_61 = lean_ctor_get(x_43, 6);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_43);
lean_inc(x_37);
x_62 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_55, x_1, x_37);
x_63 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_56);
lean_ctor_set(x_63, 2, x_57);
lean_ctor_set(x_63, 3, x_58);
lean_ctor_set(x_63, 4, x_59);
lean_ctor_set(x_63, 5, x_60);
lean_ctor_set(x_63, 6, x_61);
lean_ctor_set(x_42, 1, x_63);
x_64 = lean_st_ref_set(x_3, x_42, x_44);
lean_dec(x_3);
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
lean_ctor_set(x_67, 0, x_37);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_68 = lean_ctor_get(x_42, 0);
x_69 = lean_ctor_get(x_42, 2);
x_70 = lean_ctor_get(x_42, 3);
x_71 = lean_ctor_get(x_42, 4);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_42);
x_72 = lean_ctor_get(x_43, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_43, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_43, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_43, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_43, 4);
lean_inc(x_76);
x_77 = lean_ctor_get(x_43, 5);
lean_inc(x_77);
x_78 = lean_ctor_get(x_43, 6);
lean_inc(x_78);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 lean_ctor_release(x_43, 4);
 lean_ctor_release(x_43, 5);
 lean_ctor_release(x_43, 6);
 x_79 = x_43;
} else {
 lean_dec_ref(x_43);
 x_79 = lean_box(0);
}
lean_inc(x_37);
x_80 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_72, x_1, x_37);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 7, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_73);
lean_ctor_set(x_81, 2, x_74);
lean_ctor_set(x_81, 3, x_75);
lean_ctor_set(x_81, 4, x_76);
lean_ctor_set(x_81, 5, x_77);
lean_ctor_set(x_81, 6, x_78);
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_68);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_69);
lean_ctor_set(x_82, 3, x_70);
lean_ctor_set(x_82, 4, x_71);
x_83 = lean_st_ref_set(x_3, x_82, x_44);
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
lean_ctor_set(x_86, 0, x_37);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_35;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_35;
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_35, 0);
x_88 = lean_ctor_get(x_35, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_35);
x_89 = l_Lean_Expr_hasMVar(x_1);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = l_Lean_Expr_hasMVar(x_87);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_91 = lean_st_ref_take(x_3, x_88);
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
x_106 = lean_ctor_get(x_93, 6);
lean_inc(x_106);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 lean_ctor_release(x_93, 2);
 lean_ctor_release(x_93, 3);
 lean_ctor_release(x_93, 4);
 lean_ctor_release(x_93, 5);
 lean_ctor_release(x_93, 6);
 x_107 = x_93;
} else {
 lean_dec_ref(x_93);
 x_107 = lean_box(0);
}
lean_inc(x_87);
x_108 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_100, x_1, x_87);
if (lean_is_scalar(x_107)) {
 x_109 = lean_alloc_ctor(0, 7, 0);
} else {
 x_109 = x_107;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_101);
lean_ctor_set(x_109, 2, x_102);
lean_ctor_set(x_109, 3, x_103);
lean_ctor_set(x_109, 4, x_104);
lean_ctor_set(x_109, 5, x_105);
lean_ctor_set(x_109, 6, x_106);
if (lean_is_scalar(x_99)) {
 x_110 = lean_alloc_ctor(0, 5, 0);
} else {
 x_110 = x_99;
}
lean_ctor_set(x_110, 0, x_95);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_96);
lean_ctor_set(x_110, 3, x_97);
lean_ctor_set(x_110, 4, x_98);
x_111 = lean_st_ref_set(x_3, x_110, x_94);
lean_dec(x_3);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_87);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
else
{
lean_object* x_115; 
lean_dec(x_3);
lean_dec(x_1);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_87);
lean_ctor_set(x_115, 1, x_88);
return x_115;
}
}
else
{
lean_object* x_116; 
lean_dec(x_3);
lean_dec(x_1);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_87);
lean_ctor_set(x_116, 1, x_88);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_3);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_35);
if (x_117 == 0)
{
return x_35;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_35, 0);
x_119 = lean_ctor_get(x_35, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_35);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_object* x_121; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = lean_ctor_get(x_34, 0);
lean_inc(x_121);
lean_dec(x_34);
lean_ctor_set(x_28, 0, x_121);
return x_28;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_28, 0);
x_123 = lean_ctor_get(x_28, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_28);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec(x_124);
x_126 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_125, x_1);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_27, x_23, x_2, x_3, x_4, x_5, x_123);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
x_131 = l_Lean_Expr_hasMVar(x_1);
if (x_131 == 0)
{
uint8_t x_132; 
x_132 = l_Lean_Expr_hasMVar(x_128);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_130);
x_133 = lean_st_ref_take(x_3, x_129);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_134, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_134, 3);
lean_inc(x_139);
x_140 = lean_ctor_get(x_134, 4);
lean_inc(x_140);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 lean_ctor_release(x_134, 2);
 lean_ctor_release(x_134, 3);
 lean_ctor_release(x_134, 4);
 x_141 = x_134;
} else {
 lean_dec_ref(x_134);
 x_141 = lean_box(0);
}
x_142 = lean_ctor_get(x_135, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_135, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_135, 2);
lean_inc(x_144);
x_145 = lean_ctor_get(x_135, 3);
lean_inc(x_145);
x_146 = lean_ctor_get(x_135, 4);
lean_inc(x_146);
x_147 = lean_ctor_get(x_135, 5);
lean_inc(x_147);
x_148 = lean_ctor_get(x_135, 6);
lean_inc(x_148);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 lean_ctor_release(x_135, 5);
 lean_ctor_release(x_135, 6);
 x_149 = x_135;
} else {
 lean_dec_ref(x_135);
 x_149 = lean_box(0);
}
lean_inc(x_128);
x_150 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_142, x_1, x_128);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 7, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_143);
lean_ctor_set(x_151, 2, x_144);
lean_ctor_set(x_151, 3, x_145);
lean_ctor_set(x_151, 4, x_146);
lean_ctor_set(x_151, 5, x_147);
lean_ctor_set(x_151, 6, x_148);
if (lean_is_scalar(x_141)) {
 x_152 = lean_alloc_ctor(0, 5, 0);
} else {
 x_152 = x_141;
}
lean_ctor_set(x_152, 0, x_137);
lean_ctor_set(x_152, 1, x_151);
lean_ctor_set(x_152, 2, x_138);
lean_ctor_set(x_152, 3, x_139);
lean_ctor_set(x_152, 4, x_140);
x_153 = lean_st_ref_set(x_3, x_152, x_136);
lean_dec(x_3);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_128);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
else
{
lean_object* x_157; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_130)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_130;
}
lean_ctor_set(x_157, 0, x_128);
lean_ctor_set(x_157, 1, x_129);
return x_157;
}
}
else
{
lean_object* x_158; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_130)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_130;
}
lean_ctor_set(x_158, 0, x_128);
lean_ctor_set(x_158, 1, x_129);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_3);
lean_dec(x_1);
x_159 = lean_ctor_get(x_127, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_127, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_161 = x_127;
} else {
 lean_dec_ref(x_127);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_163 = lean_ctor_get(x_126, 0);
lean_inc(x_163);
lean_dec(x_126);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_123);
return x_164;
}
}
}
}
case 5:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_165 = lean_ctor_get(x_1, 0);
lean_inc(x_165);
x_166 = l_Lean_Expr_getAppFn(x_165);
lean_dec(x_165);
x_167 = lean_unsigned_to_nat(0u);
x_168 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_167);
x_169 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__1;
lean_inc(x_168);
x_170 = lean_mk_array(x_168, x_169);
x_171 = lean_unsigned_to_nat(1u);
x_172 = lean_nat_sub(x_168, x_171);
lean_dec(x_168);
lean_inc(x_1);
x_173 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_170, x_172);
x_174 = lean_st_ref_get(x_3, x_6);
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
x_180 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_179, x_1);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
lean_free_object(x_174);
lean_inc(x_3);
x_181 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_166, x_173, x_2, x_3, x_4, x_5, x_177);
lean_dec(x_173);
if (lean_obj_tag(x_181) == 0)
{
uint8_t x_182; 
x_182 = !lean_is_exclusive(x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_183 = lean_ctor_get(x_181, 0);
x_184 = lean_ctor_get(x_181, 1);
x_185 = l_Lean_Expr_hasMVar(x_1);
if (x_185 == 0)
{
uint8_t x_186; 
x_186 = l_Lean_Expr_hasMVar(x_183);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
lean_free_object(x_181);
x_187 = lean_st_ref_take(x_3, x_184);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
lean_dec(x_187);
x_191 = !lean_is_exclusive(x_188);
if (x_191 == 0)
{
lean_object* x_192; uint8_t x_193; 
x_192 = lean_ctor_get(x_188, 1);
lean_dec(x_192);
x_193 = !lean_is_exclusive(x_189);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_194 = lean_ctor_get(x_189, 0);
lean_inc(x_183);
x_195 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_194, x_1, x_183);
lean_ctor_set(x_189, 0, x_195);
x_196 = lean_st_ref_set(x_3, x_188, x_190);
lean_dec(x_3);
x_197 = !lean_is_exclusive(x_196);
if (x_197 == 0)
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_196, 0);
lean_dec(x_198);
lean_ctor_set(x_196, 0, x_183);
return x_196;
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
lean_dec(x_196);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_183);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_201 = lean_ctor_get(x_189, 0);
x_202 = lean_ctor_get(x_189, 1);
x_203 = lean_ctor_get(x_189, 2);
x_204 = lean_ctor_get(x_189, 3);
x_205 = lean_ctor_get(x_189, 4);
x_206 = lean_ctor_get(x_189, 5);
x_207 = lean_ctor_get(x_189, 6);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_189);
lean_inc(x_183);
x_208 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_201, x_1, x_183);
x_209 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_202);
lean_ctor_set(x_209, 2, x_203);
lean_ctor_set(x_209, 3, x_204);
lean_ctor_set(x_209, 4, x_205);
lean_ctor_set(x_209, 5, x_206);
lean_ctor_set(x_209, 6, x_207);
lean_ctor_set(x_188, 1, x_209);
x_210 = lean_st_ref_set(x_3, x_188, x_190);
lean_dec(x_3);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_212 = x_210;
} else {
 lean_dec_ref(x_210);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_183);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_214 = lean_ctor_get(x_188, 0);
x_215 = lean_ctor_get(x_188, 2);
x_216 = lean_ctor_get(x_188, 3);
x_217 = lean_ctor_get(x_188, 4);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_188);
x_218 = lean_ctor_get(x_189, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_189, 1);
lean_inc(x_219);
x_220 = lean_ctor_get(x_189, 2);
lean_inc(x_220);
x_221 = lean_ctor_get(x_189, 3);
lean_inc(x_221);
x_222 = lean_ctor_get(x_189, 4);
lean_inc(x_222);
x_223 = lean_ctor_get(x_189, 5);
lean_inc(x_223);
x_224 = lean_ctor_get(x_189, 6);
lean_inc(x_224);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 lean_ctor_release(x_189, 4);
 lean_ctor_release(x_189, 5);
 lean_ctor_release(x_189, 6);
 x_225 = x_189;
} else {
 lean_dec_ref(x_189);
 x_225 = lean_box(0);
}
lean_inc(x_183);
x_226 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_218, x_1, x_183);
if (lean_is_scalar(x_225)) {
 x_227 = lean_alloc_ctor(0, 7, 0);
} else {
 x_227 = x_225;
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_219);
lean_ctor_set(x_227, 2, x_220);
lean_ctor_set(x_227, 3, x_221);
lean_ctor_set(x_227, 4, x_222);
lean_ctor_set(x_227, 5, x_223);
lean_ctor_set(x_227, 6, x_224);
x_228 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_228, 0, x_214);
lean_ctor_set(x_228, 1, x_227);
lean_ctor_set(x_228, 2, x_215);
lean_ctor_set(x_228, 3, x_216);
lean_ctor_set(x_228, 4, x_217);
x_229 = lean_st_ref_set(x_3, x_228, x_190);
lean_dec(x_3);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_231 = x_229;
} else {
 lean_dec_ref(x_229);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_183);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_181;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_181;
}
}
else
{
lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_233 = lean_ctor_get(x_181, 0);
x_234 = lean_ctor_get(x_181, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_181);
x_235 = l_Lean_Expr_hasMVar(x_1);
if (x_235 == 0)
{
uint8_t x_236; 
x_236 = l_Lean_Expr_hasMVar(x_233);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_237 = lean_st_ref_take(x_3, x_234);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_dec(x_237);
x_241 = lean_ctor_get(x_238, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_238, 2);
lean_inc(x_242);
x_243 = lean_ctor_get(x_238, 3);
lean_inc(x_243);
x_244 = lean_ctor_get(x_238, 4);
lean_inc(x_244);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 lean_ctor_release(x_238, 2);
 lean_ctor_release(x_238, 3);
 lean_ctor_release(x_238, 4);
 x_245 = x_238;
} else {
 lean_dec_ref(x_238);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_239, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_239, 1);
lean_inc(x_247);
x_248 = lean_ctor_get(x_239, 2);
lean_inc(x_248);
x_249 = lean_ctor_get(x_239, 3);
lean_inc(x_249);
x_250 = lean_ctor_get(x_239, 4);
lean_inc(x_250);
x_251 = lean_ctor_get(x_239, 5);
lean_inc(x_251);
x_252 = lean_ctor_get(x_239, 6);
lean_inc(x_252);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 lean_ctor_release(x_239, 2);
 lean_ctor_release(x_239, 3);
 lean_ctor_release(x_239, 4);
 lean_ctor_release(x_239, 5);
 lean_ctor_release(x_239, 6);
 x_253 = x_239;
} else {
 lean_dec_ref(x_239);
 x_253 = lean_box(0);
}
lean_inc(x_233);
x_254 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_246, x_1, x_233);
if (lean_is_scalar(x_253)) {
 x_255 = lean_alloc_ctor(0, 7, 0);
} else {
 x_255 = x_253;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_247);
lean_ctor_set(x_255, 2, x_248);
lean_ctor_set(x_255, 3, x_249);
lean_ctor_set(x_255, 4, x_250);
lean_ctor_set(x_255, 5, x_251);
lean_ctor_set(x_255, 6, x_252);
if (lean_is_scalar(x_245)) {
 x_256 = lean_alloc_ctor(0, 5, 0);
} else {
 x_256 = x_245;
}
lean_ctor_set(x_256, 0, x_241);
lean_ctor_set(x_256, 1, x_255);
lean_ctor_set(x_256, 2, x_242);
lean_ctor_set(x_256, 3, x_243);
lean_ctor_set(x_256, 4, x_244);
x_257 = lean_st_ref_set(x_3, x_256, x_240);
lean_dec(x_3);
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_259 = x_257;
} else {
 lean_dec_ref(x_257);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_233);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
else
{
lean_object* x_261; 
lean_dec(x_3);
lean_dec(x_1);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_233);
lean_ctor_set(x_261, 1, x_234);
return x_261;
}
}
else
{
lean_object* x_262; 
lean_dec(x_3);
lean_dec(x_1);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_233);
lean_ctor_set(x_262, 1, x_234);
return x_262;
}
}
}
else
{
uint8_t x_263; 
lean_dec(x_3);
lean_dec(x_1);
x_263 = !lean_is_exclusive(x_181);
if (x_263 == 0)
{
return x_181;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_181, 0);
x_265 = lean_ctor_get(x_181, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_181);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
else
{
lean_object* x_267; 
lean_dec(x_173);
lean_dec(x_166);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_267 = lean_ctor_get(x_180, 0);
lean_inc(x_267);
lean_dec(x_180);
lean_ctor_set(x_174, 0, x_267);
return x_174;
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_268 = lean_ctor_get(x_174, 0);
x_269 = lean_ctor_get(x_174, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_174);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
lean_dec(x_270);
x_272 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_271, x_1);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; 
lean_inc(x_3);
x_273 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_166, x_173, x_2, x_3, x_4, x_5, x_269);
lean_dec(x_173);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_276 = x_273;
} else {
 lean_dec_ref(x_273);
 x_276 = lean_box(0);
}
x_277 = l_Lean_Expr_hasMVar(x_1);
if (x_277 == 0)
{
uint8_t x_278; 
x_278 = l_Lean_Expr_hasMVar(x_274);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_276);
x_279 = lean_st_ref_take(x_3, x_275);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
x_282 = lean_ctor_get(x_279, 1);
lean_inc(x_282);
lean_dec(x_279);
x_283 = lean_ctor_get(x_280, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_280, 2);
lean_inc(x_284);
x_285 = lean_ctor_get(x_280, 3);
lean_inc(x_285);
x_286 = lean_ctor_get(x_280, 4);
lean_inc(x_286);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 lean_ctor_release(x_280, 2);
 lean_ctor_release(x_280, 3);
 lean_ctor_release(x_280, 4);
 x_287 = x_280;
} else {
 lean_dec_ref(x_280);
 x_287 = lean_box(0);
}
x_288 = lean_ctor_get(x_281, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_281, 1);
lean_inc(x_289);
x_290 = lean_ctor_get(x_281, 2);
lean_inc(x_290);
x_291 = lean_ctor_get(x_281, 3);
lean_inc(x_291);
x_292 = lean_ctor_get(x_281, 4);
lean_inc(x_292);
x_293 = lean_ctor_get(x_281, 5);
lean_inc(x_293);
x_294 = lean_ctor_get(x_281, 6);
lean_inc(x_294);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 lean_ctor_release(x_281, 2);
 lean_ctor_release(x_281, 3);
 lean_ctor_release(x_281, 4);
 lean_ctor_release(x_281, 5);
 lean_ctor_release(x_281, 6);
 x_295 = x_281;
} else {
 lean_dec_ref(x_281);
 x_295 = lean_box(0);
}
lean_inc(x_274);
x_296 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_288, x_1, x_274);
if (lean_is_scalar(x_295)) {
 x_297 = lean_alloc_ctor(0, 7, 0);
} else {
 x_297 = x_295;
}
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_289);
lean_ctor_set(x_297, 2, x_290);
lean_ctor_set(x_297, 3, x_291);
lean_ctor_set(x_297, 4, x_292);
lean_ctor_set(x_297, 5, x_293);
lean_ctor_set(x_297, 6, x_294);
if (lean_is_scalar(x_287)) {
 x_298 = lean_alloc_ctor(0, 5, 0);
} else {
 x_298 = x_287;
}
lean_ctor_set(x_298, 0, x_283);
lean_ctor_set(x_298, 1, x_297);
lean_ctor_set(x_298, 2, x_284);
lean_ctor_set(x_298, 3, x_285);
lean_ctor_set(x_298, 4, x_286);
x_299 = lean_st_ref_set(x_3, x_298, x_282);
lean_dec(x_3);
x_300 = lean_ctor_get(x_299, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_301 = x_299;
} else {
 lean_dec_ref(x_299);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_274);
lean_ctor_set(x_302, 1, x_300);
return x_302;
}
else
{
lean_object* x_303; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_276)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_276;
}
lean_ctor_set(x_303, 0, x_274);
lean_ctor_set(x_303, 1, x_275);
return x_303;
}
}
else
{
lean_object* x_304; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_276)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_276;
}
lean_ctor_set(x_304, 0, x_274);
lean_ctor_set(x_304, 1, x_275);
return x_304;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_3);
lean_dec(x_1);
x_305 = lean_ctor_get(x_273, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_273, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_307 = x_273;
} else {
 lean_dec_ref(x_273);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_305);
lean_ctor_set(x_308, 1, x_306);
return x_308;
}
}
else
{
lean_object* x_309; lean_object* x_310; 
lean_dec(x_173);
lean_dec(x_166);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_309 = lean_ctor_get(x_272, 0);
lean_inc(x_309);
lean_dec(x_272);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_269);
return x_310;
}
}
}
case 7:
{
lean_object* x_311; uint8_t x_312; 
x_311 = lean_st_ref_get(x_3, x_6);
x_312 = !lean_is_exclusive(x_311);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_313 = lean_ctor_get(x_311, 0);
x_314 = lean_ctor_get(x_311, 1);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
lean_dec(x_315);
x_317 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_316, x_1);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; uint8_t x_319; lean_object* x_320; 
lean_free_object(x_311);
x_318 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1;
x_319 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_320 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_1, x_318, x_319, x_2, x_3, x_4, x_5, x_314);
if (lean_obj_tag(x_320) == 0)
{
uint8_t x_321; 
x_321 = !lean_is_exclusive(x_320);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_322 = lean_ctor_get(x_320, 0);
x_323 = lean_ctor_get(x_320, 1);
x_324 = l_Lean_Expr_hasMVar(x_1);
if (x_324 == 0)
{
uint8_t x_325; 
x_325 = l_Lean_Expr_hasMVar(x_322);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
lean_free_object(x_320);
x_326 = lean_st_ref_take(x_3, x_323);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_327, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_326, 1);
lean_inc(x_329);
lean_dec(x_326);
x_330 = !lean_is_exclusive(x_327);
if (x_330 == 0)
{
lean_object* x_331; uint8_t x_332; 
x_331 = lean_ctor_get(x_327, 1);
lean_dec(x_331);
x_332 = !lean_is_exclusive(x_328);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; 
x_333 = lean_ctor_get(x_328, 0);
lean_inc(x_322);
x_334 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_333, x_1, x_322);
lean_ctor_set(x_328, 0, x_334);
x_335 = lean_st_ref_set(x_3, x_327, x_329);
lean_dec(x_3);
x_336 = !lean_is_exclusive(x_335);
if (x_336 == 0)
{
lean_object* x_337; 
x_337 = lean_ctor_get(x_335, 0);
lean_dec(x_337);
lean_ctor_set(x_335, 0, x_322);
return x_335;
}
else
{
lean_object* x_338; lean_object* x_339; 
x_338 = lean_ctor_get(x_335, 1);
lean_inc(x_338);
lean_dec(x_335);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_322);
lean_ctor_set(x_339, 1, x_338);
return x_339;
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_340 = lean_ctor_get(x_328, 0);
x_341 = lean_ctor_get(x_328, 1);
x_342 = lean_ctor_get(x_328, 2);
x_343 = lean_ctor_get(x_328, 3);
x_344 = lean_ctor_get(x_328, 4);
x_345 = lean_ctor_get(x_328, 5);
x_346 = lean_ctor_get(x_328, 6);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_328);
lean_inc(x_322);
x_347 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_340, x_1, x_322);
x_348 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_341);
lean_ctor_set(x_348, 2, x_342);
lean_ctor_set(x_348, 3, x_343);
lean_ctor_set(x_348, 4, x_344);
lean_ctor_set(x_348, 5, x_345);
lean_ctor_set(x_348, 6, x_346);
lean_ctor_set(x_327, 1, x_348);
x_349 = lean_st_ref_set(x_3, x_327, x_329);
lean_dec(x_3);
x_350 = lean_ctor_get(x_349, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 x_351 = x_349;
} else {
 lean_dec_ref(x_349);
 x_351 = lean_box(0);
}
if (lean_is_scalar(x_351)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_351;
}
lean_ctor_set(x_352, 0, x_322);
lean_ctor_set(x_352, 1, x_350);
return x_352;
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_353 = lean_ctor_get(x_327, 0);
x_354 = lean_ctor_get(x_327, 2);
x_355 = lean_ctor_get(x_327, 3);
x_356 = lean_ctor_get(x_327, 4);
lean_inc(x_356);
lean_inc(x_355);
lean_inc(x_354);
lean_inc(x_353);
lean_dec(x_327);
x_357 = lean_ctor_get(x_328, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_328, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_328, 2);
lean_inc(x_359);
x_360 = lean_ctor_get(x_328, 3);
lean_inc(x_360);
x_361 = lean_ctor_get(x_328, 4);
lean_inc(x_361);
x_362 = lean_ctor_get(x_328, 5);
lean_inc(x_362);
x_363 = lean_ctor_get(x_328, 6);
lean_inc(x_363);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 lean_ctor_release(x_328, 2);
 lean_ctor_release(x_328, 3);
 lean_ctor_release(x_328, 4);
 lean_ctor_release(x_328, 5);
 lean_ctor_release(x_328, 6);
 x_364 = x_328;
} else {
 lean_dec_ref(x_328);
 x_364 = lean_box(0);
}
lean_inc(x_322);
x_365 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_357, x_1, x_322);
if (lean_is_scalar(x_364)) {
 x_366 = lean_alloc_ctor(0, 7, 0);
} else {
 x_366 = x_364;
}
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_358);
lean_ctor_set(x_366, 2, x_359);
lean_ctor_set(x_366, 3, x_360);
lean_ctor_set(x_366, 4, x_361);
lean_ctor_set(x_366, 5, x_362);
lean_ctor_set(x_366, 6, x_363);
x_367 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_367, 0, x_353);
lean_ctor_set(x_367, 1, x_366);
lean_ctor_set(x_367, 2, x_354);
lean_ctor_set(x_367, 3, x_355);
lean_ctor_set(x_367, 4, x_356);
x_368 = lean_st_ref_set(x_3, x_367, x_329);
lean_dec(x_3);
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_370 = x_368;
} else {
 lean_dec_ref(x_368);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_322);
lean_ctor_set(x_371, 1, x_369);
return x_371;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_320;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_320;
}
}
else
{
lean_object* x_372; lean_object* x_373; uint8_t x_374; 
x_372 = lean_ctor_get(x_320, 0);
x_373 = lean_ctor_get(x_320, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_320);
x_374 = l_Lean_Expr_hasMVar(x_1);
if (x_374 == 0)
{
uint8_t x_375; 
x_375 = l_Lean_Expr_hasMVar(x_372);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_376 = lean_st_ref_take(x_3, x_373);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_377, 1);
lean_inc(x_378);
x_379 = lean_ctor_get(x_376, 1);
lean_inc(x_379);
lean_dec(x_376);
x_380 = lean_ctor_get(x_377, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_377, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_377, 3);
lean_inc(x_382);
x_383 = lean_ctor_get(x_377, 4);
lean_inc(x_383);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 lean_ctor_release(x_377, 4);
 x_384 = x_377;
} else {
 lean_dec_ref(x_377);
 x_384 = lean_box(0);
}
x_385 = lean_ctor_get(x_378, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_378, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_378, 2);
lean_inc(x_387);
x_388 = lean_ctor_get(x_378, 3);
lean_inc(x_388);
x_389 = lean_ctor_get(x_378, 4);
lean_inc(x_389);
x_390 = lean_ctor_get(x_378, 5);
lean_inc(x_390);
x_391 = lean_ctor_get(x_378, 6);
lean_inc(x_391);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 lean_ctor_release(x_378, 4);
 lean_ctor_release(x_378, 5);
 lean_ctor_release(x_378, 6);
 x_392 = x_378;
} else {
 lean_dec_ref(x_378);
 x_392 = lean_box(0);
}
lean_inc(x_372);
x_393 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_385, x_1, x_372);
if (lean_is_scalar(x_392)) {
 x_394 = lean_alloc_ctor(0, 7, 0);
} else {
 x_394 = x_392;
}
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_386);
lean_ctor_set(x_394, 2, x_387);
lean_ctor_set(x_394, 3, x_388);
lean_ctor_set(x_394, 4, x_389);
lean_ctor_set(x_394, 5, x_390);
lean_ctor_set(x_394, 6, x_391);
if (lean_is_scalar(x_384)) {
 x_395 = lean_alloc_ctor(0, 5, 0);
} else {
 x_395 = x_384;
}
lean_ctor_set(x_395, 0, x_380);
lean_ctor_set(x_395, 1, x_394);
lean_ctor_set(x_395, 2, x_381);
lean_ctor_set(x_395, 3, x_382);
lean_ctor_set(x_395, 4, x_383);
x_396 = lean_st_ref_set(x_3, x_395, x_379);
lean_dec(x_3);
x_397 = lean_ctor_get(x_396, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_398 = x_396;
} else {
 lean_dec_ref(x_396);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(0, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_372);
lean_ctor_set(x_399, 1, x_397);
return x_399;
}
else
{
lean_object* x_400; 
lean_dec(x_3);
lean_dec(x_1);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_372);
lean_ctor_set(x_400, 1, x_373);
return x_400;
}
}
else
{
lean_object* x_401; 
lean_dec(x_3);
lean_dec(x_1);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_372);
lean_ctor_set(x_401, 1, x_373);
return x_401;
}
}
}
else
{
uint8_t x_402; 
lean_dec(x_3);
lean_dec(x_1);
x_402 = !lean_is_exclusive(x_320);
if (x_402 == 0)
{
return x_320;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_403 = lean_ctor_get(x_320, 0);
x_404 = lean_ctor_get(x_320, 1);
lean_inc(x_404);
lean_inc(x_403);
lean_dec(x_320);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_403);
lean_ctor_set(x_405, 1, x_404);
return x_405;
}
}
}
else
{
lean_object* x_406; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_406 = lean_ctor_get(x_317, 0);
lean_inc(x_406);
lean_dec(x_317);
lean_ctor_set(x_311, 0, x_406);
return x_311;
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_407 = lean_ctor_get(x_311, 0);
x_408 = lean_ctor_get(x_311, 1);
lean_inc(x_408);
lean_inc(x_407);
lean_dec(x_311);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
lean_dec(x_409);
x_411 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_410, x_1);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; uint8_t x_413; lean_object* x_414; 
x_412 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1;
x_413 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_414 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_1, x_412, x_413, x_2, x_3, x_4, x_5, x_408);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
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
x_418 = l_Lean_Expr_hasMVar(x_1);
if (x_418 == 0)
{
uint8_t x_419; 
x_419 = l_Lean_Expr_hasMVar(x_415);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_417);
x_420 = lean_st_ref_take(x_3, x_416);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_421, 1);
lean_inc(x_422);
x_423 = lean_ctor_get(x_420, 1);
lean_inc(x_423);
lean_dec(x_420);
x_424 = lean_ctor_get(x_421, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_421, 2);
lean_inc(x_425);
x_426 = lean_ctor_get(x_421, 3);
lean_inc(x_426);
x_427 = lean_ctor_get(x_421, 4);
lean_inc(x_427);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 lean_ctor_release(x_421, 2);
 lean_ctor_release(x_421, 3);
 lean_ctor_release(x_421, 4);
 x_428 = x_421;
} else {
 lean_dec_ref(x_421);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_422, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_422, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_422, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_422, 3);
lean_inc(x_432);
x_433 = lean_ctor_get(x_422, 4);
lean_inc(x_433);
x_434 = lean_ctor_get(x_422, 5);
lean_inc(x_434);
x_435 = lean_ctor_get(x_422, 6);
lean_inc(x_435);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 lean_ctor_release(x_422, 2);
 lean_ctor_release(x_422, 3);
 lean_ctor_release(x_422, 4);
 lean_ctor_release(x_422, 5);
 lean_ctor_release(x_422, 6);
 x_436 = x_422;
} else {
 lean_dec_ref(x_422);
 x_436 = lean_box(0);
}
lean_inc(x_415);
x_437 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_429, x_1, x_415);
if (lean_is_scalar(x_436)) {
 x_438 = lean_alloc_ctor(0, 7, 0);
} else {
 x_438 = x_436;
}
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_430);
lean_ctor_set(x_438, 2, x_431);
lean_ctor_set(x_438, 3, x_432);
lean_ctor_set(x_438, 4, x_433);
lean_ctor_set(x_438, 5, x_434);
lean_ctor_set(x_438, 6, x_435);
if (lean_is_scalar(x_428)) {
 x_439 = lean_alloc_ctor(0, 5, 0);
} else {
 x_439 = x_428;
}
lean_ctor_set(x_439, 0, x_424);
lean_ctor_set(x_439, 1, x_438);
lean_ctor_set(x_439, 2, x_425);
lean_ctor_set(x_439, 3, x_426);
lean_ctor_set(x_439, 4, x_427);
x_440 = lean_st_ref_set(x_3, x_439, x_423);
lean_dec(x_3);
x_441 = lean_ctor_get(x_440, 1);
lean_inc(x_441);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_442 = x_440;
} else {
 lean_dec_ref(x_440);
 x_442 = lean_box(0);
}
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(0, 2, 0);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_415);
lean_ctor_set(x_443, 1, x_441);
return x_443;
}
else
{
lean_object* x_444; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_417)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_417;
}
lean_ctor_set(x_444, 0, x_415);
lean_ctor_set(x_444, 1, x_416);
return x_444;
}
}
else
{
lean_object* x_445; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_417)) {
 x_445 = lean_alloc_ctor(0, 2, 0);
} else {
 x_445 = x_417;
}
lean_ctor_set(x_445, 0, x_415);
lean_ctor_set(x_445, 1, x_416);
return x_445;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_3);
lean_dec(x_1);
x_446 = lean_ctor_get(x_414, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_414, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_448 = x_414;
} else {
 lean_dec_ref(x_414);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_446);
lean_ctor_set(x_449, 1, x_447);
return x_449;
}
}
else
{
lean_object* x_450; lean_object* x_451; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_450 = lean_ctor_get(x_411, 0);
lean_inc(x_450);
lean_dec(x_411);
x_451 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_408);
return x_451;
}
}
}
case 9:
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_452 = lean_ctor_get(x_1, 0);
lean_inc(x_452);
lean_dec(x_1);
x_453 = l_Lean_Literal_type(x_452);
lean_dec(x_452);
x_454 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_6);
return x_454;
}
case 10:
{
lean_object* x_455; 
x_455 = lean_ctor_get(x_1, 1);
lean_inc(x_455);
lean_dec(x_1);
x_1 = x_455;
goto _start;
}
case 11:
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; 
x_457 = lean_ctor_get(x_1, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_1, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_1, 2);
lean_inc(x_459);
x_460 = lean_st_ref_get(x_3, x_6);
x_461 = !lean_is_exclusive(x_460);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_462 = lean_ctor_get(x_460, 0);
x_463 = lean_ctor_get(x_460, 1);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
lean_dec(x_464);
x_466 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_465, x_1);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; 
lean_free_object(x_460);
lean_inc(x_3);
x_467 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(x_457, x_458, x_459, x_2, x_3, x_4, x_5, x_463);
if (lean_obj_tag(x_467) == 0)
{
uint8_t x_468; 
x_468 = !lean_is_exclusive(x_467);
if (x_468 == 0)
{
lean_object* x_469; lean_object* x_470; uint8_t x_471; 
x_469 = lean_ctor_get(x_467, 0);
x_470 = lean_ctor_get(x_467, 1);
x_471 = l_Lean_Expr_hasMVar(x_1);
if (x_471 == 0)
{
uint8_t x_472; 
x_472 = l_Lean_Expr_hasMVar(x_469);
if (x_472 == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; 
lean_free_object(x_467);
x_473 = lean_st_ref_take(x_3, x_470);
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_474, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_473, 1);
lean_inc(x_476);
lean_dec(x_473);
x_477 = !lean_is_exclusive(x_474);
if (x_477 == 0)
{
lean_object* x_478; uint8_t x_479; 
x_478 = lean_ctor_get(x_474, 1);
lean_dec(x_478);
x_479 = !lean_is_exclusive(x_475);
if (x_479 == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; 
x_480 = lean_ctor_get(x_475, 0);
lean_inc(x_469);
x_481 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_480, x_1, x_469);
lean_ctor_set(x_475, 0, x_481);
x_482 = lean_st_ref_set(x_3, x_474, x_476);
lean_dec(x_3);
x_483 = !lean_is_exclusive(x_482);
if (x_483 == 0)
{
lean_object* x_484; 
x_484 = lean_ctor_get(x_482, 0);
lean_dec(x_484);
lean_ctor_set(x_482, 0, x_469);
return x_482;
}
else
{
lean_object* x_485; lean_object* x_486; 
x_485 = lean_ctor_get(x_482, 1);
lean_inc(x_485);
lean_dec(x_482);
x_486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_486, 0, x_469);
lean_ctor_set(x_486, 1, x_485);
return x_486;
}
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_487 = lean_ctor_get(x_475, 0);
x_488 = lean_ctor_get(x_475, 1);
x_489 = lean_ctor_get(x_475, 2);
x_490 = lean_ctor_get(x_475, 3);
x_491 = lean_ctor_get(x_475, 4);
x_492 = lean_ctor_get(x_475, 5);
x_493 = lean_ctor_get(x_475, 6);
lean_inc(x_493);
lean_inc(x_492);
lean_inc(x_491);
lean_inc(x_490);
lean_inc(x_489);
lean_inc(x_488);
lean_inc(x_487);
lean_dec(x_475);
lean_inc(x_469);
x_494 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_487, x_1, x_469);
x_495 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_488);
lean_ctor_set(x_495, 2, x_489);
lean_ctor_set(x_495, 3, x_490);
lean_ctor_set(x_495, 4, x_491);
lean_ctor_set(x_495, 5, x_492);
lean_ctor_set(x_495, 6, x_493);
lean_ctor_set(x_474, 1, x_495);
x_496 = lean_st_ref_set(x_3, x_474, x_476);
lean_dec(x_3);
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_498 = x_496;
} else {
 lean_dec_ref(x_496);
 x_498 = lean_box(0);
}
if (lean_is_scalar(x_498)) {
 x_499 = lean_alloc_ctor(0, 2, 0);
} else {
 x_499 = x_498;
}
lean_ctor_set(x_499, 0, x_469);
lean_ctor_set(x_499, 1, x_497);
return x_499;
}
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_500 = lean_ctor_get(x_474, 0);
x_501 = lean_ctor_get(x_474, 2);
x_502 = lean_ctor_get(x_474, 3);
x_503 = lean_ctor_get(x_474, 4);
lean_inc(x_503);
lean_inc(x_502);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_474);
x_504 = lean_ctor_get(x_475, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_475, 1);
lean_inc(x_505);
x_506 = lean_ctor_get(x_475, 2);
lean_inc(x_506);
x_507 = lean_ctor_get(x_475, 3);
lean_inc(x_507);
x_508 = lean_ctor_get(x_475, 4);
lean_inc(x_508);
x_509 = lean_ctor_get(x_475, 5);
lean_inc(x_509);
x_510 = lean_ctor_get(x_475, 6);
lean_inc(x_510);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 lean_ctor_release(x_475, 2);
 lean_ctor_release(x_475, 3);
 lean_ctor_release(x_475, 4);
 lean_ctor_release(x_475, 5);
 lean_ctor_release(x_475, 6);
 x_511 = x_475;
} else {
 lean_dec_ref(x_475);
 x_511 = lean_box(0);
}
lean_inc(x_469);
x_512 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_504, x_1, x_469);
if (lean_is_scalar(x_511)) {
 x_513 = lean_alloc_ctor(0, 7, 0);
} else {
 x_513 = x_511;
}
lean_ctor_set(x_513, 0, x_512);
lean_ctor_set(x_513, 1, x_505);
lean_ctor_set(x_513, 2, x_506);
lean_ctor_set(x_513, 3, x_507);
lean_ctor_set(x_513, 4, x_508);
lean_ctor_set(x_513, 5, x_509);
lean_ctor_set(x_513, 6, x_510);
x_514 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_514, 0, x_500);
lean_ctor_set(x_514, 1, x_513);
lean_ctor_set(x_514, 2, x_501);
lean_ctor_set(x_514, 3, x_502);
lean_ctor_set(x_514, 4, x_503);
x_515 = lean_st_ref_set(x_3, x_514, x_476);
lean_dec(x_3);
x_516 = lean_ctor_get(x_515, 1);
lean_inc(x_516);
if (lean_is_exclusive(x_515)) {
 lean_ctor_release(x_515, 0);
 lean_ctor_release(x_515, 1);
 x_517 = x_515;
} else {
 lean_dec_ref(x_515);
 x_517 = lean_box(0);
}
if (lean_is_scalar(x_517)) {
 x_518 = lean_alloc_ctor(0, 2, 0);
} else {
 x_518 = x_517;
}
lean_ctor_set(x_518, 0, x_469);
lean_ctor_set(x_518, 1, x_516);
return x_518;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_467;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_467;
}
}
else
{
lean_object* x_519; lean_object* x_520; uint8_t x_521; 
x_519 = lean_ctor_get(x_467, 0);
x_520 = lean_ctor_get(x_467, 1);
lean_inc(x_520);
lean_inc(x_519);
lean_dec(x_467);
x_521 = l_Lean_Expr_hasMVar(x_1);
if (x_521 == 0)
{
uint8_t x_522; 
x_522 = l_Lean_Expr_hasMVar(x_519);
if (x_522 == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_523 = lean_st_ref_take(x_3, x_520);
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_524, 1);
lean_inc(x_525);
x_526 = lean_ctor_get(x_523, 1);
lean_inc(x_526);
lean_dec(x_523);
x_527 = lean_ctor_get(x_524, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_524, 2);
lean_inc(x_528);
x_529 = lean_ctor_get(x_524, 3);
lean_inc(x_529);
x_530 = lean_ctor_get(x_524, 4);
lean_inc(x_530);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 lean_ctor_release(x_524, 2);
 lean_ctor_release(x_524, 3);
 lean_ctor_release(x_524, 4);
 x_531 = x_524;
} else {
 lean_dec_ref(x_524);
 x_531 = lean_box(0);
}
x_532 = lean_ctor_get(x_525, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_525, 1);
lean_inc(x_533);
x_534 = lean_ctor_get(x_525, 2);
lean_inc(x_534);
x_535 = lean_ctor_get(x_525, 3);
lean_inc(x_535);
x_536 = lean_ctor_get(x_525, 4);
lean_inc(x_536);
x_537 = lean_ctor_get(x_525, 5);
lean_inc(x_537);
x_538 = lean_ctor_get(x_525, 6);
lean_inc(x_538);
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 lean_ctor_release(x_525, 1);
 lean_ctor_release(x_525, 2);
 lean_ctor_release(x_525, 3);
 lean_ctor_release(x_525, 4);
 lean_ctor_release(x_525, 5);
 lean_ctor_release(x_525, 6);
 x_539 = x_525;
} else {
 lean_dec_ref(x_525);
 x_539 = lean_box(0);
}
lean_inc(x_519);
x_540 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_532, x_1, x_519);
if (lean_is_scalar(x_539)) {
 x_541 = lean_alloc_ctor(0, 7, 0);
} else {
 x_541 = x_539;
}
lean_ctor_set(x_541, 0, x_540);
lean_ctor_set(x_541, 1, x_533);
lean_ctor_set(x_541, 2, x_534);
lean_ctor_set(x_541, 3, x_535);
lean_ctor_set(x_541, 4, x_536);
lean_ctor_set(x_541, 5, x_537);
lean_ctor_set(x_541, 6, x_538);
if (lean_is_scalar(x_531)) {
 x_542 = lean_alloc_ctor(0, 5, 0);
} else {
 x_542 = x_531;
}
lean_ctor_set(x_542, 0, x_527);
lean_ctor_set(x_542, 1, x_541);
lean_ctor_set(x_542, 2, x_528);
lean_ctor_set(x_542, 3, x_529);
lean_ctor_set(x_542, 4, x_530);
x_543 = lean_st_ref_set(x_3, x_542, x_526);
lean_dec(x_3);
x_544 = lean_ctor_get(x_543, 1);
lean_inc(x_544);
if (lean_is_exclusive(x_543)) {
 lean_ctor_release(x_543, 0);
 lean_ctor_release(x_543, 1);
 x_545 = x_543;
} else {
 lean_dec_ref(x_543);
 x_545 = lean_box(0);
}
if (lean_is_scalar(x_545)) {
 x_546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_546 = x_545;
}
lean_ctor_set(x_546, 0, x_519);
lean_ctor_set(x_546, 1, x_544);
return x_546;
}
else
{
lean_object* x_547; 
lean_dec(x_3);
lean_dec(x_1);
x_547 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_547, 0, x_519);
lean_ctor_set(x_547, 1, x_520);
return x_547;
}
}
else
{
lean_object* x_548; 
lean_dec(x_3);
lean_dec(x_1);
x_548 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_548, 0, x_519);
lean_ctor_set(x_548, 1, x_520);
return x_548;
}
}
}
else
{
uint8_t x_549; 
lean_dec(x_3);
lean_dec(x_1);
x_549 = !lean_is_exclusive(x_467);
if (x_549 == 0)
{
return x_467;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_550 = lean_ctor_get(x_467, 0);
x_551 = lean_ctor_get(x_467, 1);
lean_inc(x_551);
lean_inc(x_550);
lean_dec(x_467);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
return x_552;
}
}
}
else
{
lean_object* x_553; 
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_553 = lean_ctor_get(x_466, 0);
lean_inc(x_553);
lean_dec(x_466);
lean_ctor_set(x_460, 0, x_553);
return x_460;
}
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_554 = lean_ctor_get(x_460, 0);
x_555 = lean_ctor_get(x_460, 1);
lean_inc(x_555);
lean_inc(x_554);
lean_dec(x_460);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
lean_dec(x_556);
x_558 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_557, x_1);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; 
lean_inc(x_3);
x_559 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(x_457, x_458, x_459, x_2, x_3, x_4, x_5, x_555);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; uint8_t x_563; 
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
x_563 = l_Lean_Expr_hasMVar(x_1);
if (x_563 == 0)
{
uint8_t x_564; 
x_564 = l_Lean_Expr_hasMVar(x_560);
if (x_564 == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
lean_dec(x_562);
x_565 = lean_st_ref_take(x_3, x_561);
x_566 = lean_ctor_get(x_565, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_566, 1);
lean_inc(x_567);
x_568 = lean_ctor_get(x_565, 1);
lean_inc(x_568);
lean_dec(x_565);
x_569 = lean_ctor_get(x_566, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_566, 2);
lean_inc(x_570);
x_571 = lean_ctor_get(x_566, 3);
lean_inc(x_571);
x_572 = lean_ctor_get(x_566, 4);
lean_inc(x_572);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 lean_ctor_release(x_566, 2);
 lean_ctor_release(x_566, 3);
 lean_ctor_release(x_566, 4);
 x_573 = x_566;
} else {
 lean_dec_ref(x_566);
 x_573 = lean_box(0);
}
x_574 = lean_ctor_get(x_567, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_567, 1);
lean_inc(x_575);
x_576 = lean_ctor_get(x_567, 2);
lean_inc(x_576);
x_577 = lean_ctor_get(x_567, 3);
lean_inc(x_577);
x_578 = lean_ctor_get(x_567, 4);
lean_inc(x_578);
x_579 = lean_ctor_get(x_567, 5);
lean_inc(x_579);
x_580 = lean_ctor_get(x_567, 6);
lean_inc(x_580);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 lean_ctor_release(x_567, 1);
 lean_ctor_release(x_567, 2);
 lean_ctor_release(x_567, 3);
 lean_ctor_release(x_567, 4);
 lean_ctor_release(x_567, 5);
 lean_ctor_release(x_567, 6);
 x_581 = x_567;
} else {
 lean_dec_ref(x_567);
 x_581 = lean_box(0);
}
lean_inc(x_560);
x_582 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_574, x_1, x_560);
if (lean_is_scalar(x_581)) {
 x_583 = lean_alloc_ctor(0, 7, 0);
} else {
 x_583 = x_581;
}
lean_ctor_set(x_583, 0, x_582);
lean_ctor_set(x_583, 1, x_575);
lean_ctor_set(x_583, 2, x_576);
lean_ctor_set(x_583, 3, x_577);
lean_ctor_set(x_583, 4, x_578);
lean_ctor_set(x_583, 5, x_579);
lean_ctor_set(x_583, 6, x_580);
if (lean_is_scalar(x_573)) {
 x_584 = lean_alloc_ctor(0, 5, 0);
} else {
 x_584 = x_573;
}
lean_ctor_set(x_584, 0, x_569);
lean_ctor_set(x_584, 1, x_583);
lean_ctor_set(x_584, 2, x_570);
lean_ctor_set(x_584, 3, x_571);
lean_ctor_set(x_584, 4, x_572);
x_585 = lean_st_ref_set(x_3, x_584, x_568);
lean_dec(x_3);
x_586 = lean_ctor_get(x_585, 1);
lean_inc(x_586);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 lean_ctor_release(x_585, 1);
 x_587 = x_585;
} else {
 lean_dec_ref(x_585);
 x_587 = lean_box(0);
}
if (lean_is_scalar(x_587)) {
 x_588 = lean_alloc_ctor(0, 2, 0);
} else {
 x_588 = x_587;
}
lean_ctor_set(x_588, 0, x_560);
lean_ctor_set(x_588, 1, x_586);
return x_588;
}
else
{
lean_object* x_589; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_562)) {
 x_589 = lean_alloc_ctor(0, 2, 0);
} else {
 x_589 = x_562;
}
lean_ctor_set(x_589, 0, x_560);
lean_ctor_set(x_589, 1, x_561);
return x_589;
}
}
else
{
lean_object* x_590; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_562)) {
 x_590 = lean_alloc_ctor(0, 2, 0);
} else {
 x_590 = x_562;
}
lean_ctor_set(x_590, 0, x_560);
lean_ctor_set(x_590, 1, x_561);
return x_590;
}
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
lean_dec(x_3);
lean_dec(x_1);
x_591 = lean_ctor_get(x_559, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_559, 1);
lean_inc(x_592);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 lean_ctor_release(x_559, 1);
 x_593 = x_559;
} else {
 lean_dec_ref(x_559);
 x_593 = lean_box(0);
}
if (lean_is_scalar(x_593)) {
 x_594 = lean_alloc_ctor(1, 2, 0);
} else {
 x_594 = x_593;
}
lean_ctor_set(x_594, 0, x_591);
lean_ctor_set(x_594, 1, x_592);
return x_594;
}
}
else
{
lean_object* x_595; lean_object* x_596; 
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_595 = lean_ctor_get(x_558, 0);
lean_inc(x_595);
lean_dec(x_558);
x_596 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_596, 0, x_595);
lean_ctor_set(x_596, 1, x_555);
return x_596;
}
}
}
default: 
{
lean_object* x_597; uint8_t x_598; 
x_597 = lean_st_ref_get(x_3, x_6);
x_598 = !lean_is_exclusive(x_597);
if (x_598 == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_599 = lean_ctor_get(x_597, 0);
x_600 = lean_ctor_get(x_597, 1);
x_601 = lean_ctor_get(x_599, 1);
lean_inc(x_601);
lean_dec(x_599);
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
lean_dec(x_601);
x_603 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_602, x_1);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; uint8_t x_605; lean_object* x_606; 
lean_free_object(x_597);
x_604 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1;
x_605 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_606 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_1, x_604, x_605, x_2, x_3, x_4, x_5, x_600);
if (lean_obj_tag(x_606) == 0)
{
uint8_t x_607; 
x_607 = !lean_is_exclusive(x_606);
if (x_607 == 0)
{
lean_object* x_608; lean_object* x_609; uint8_t x_610; 
x_608 = lean_ctor_get(x_606, 0);
x_609 = lean_ctor_get(x_606, 1);
x_610 = l_Lean_Expr_hasMVar(x_1);
if (x_610 == 0)
{
uint8_t x_611; 
x_611 = l_Lean_Expr_hasMVar(x_608);
if (x_611 == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; uint8_t x_616; 
lean_free_object(x_606);
x_612 = lean_st_ref_take(x_3, x_609);
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_613, 1);
lean_inc(x_614);
x_615 = lean_ctor_get(x_612, 1);
lean_inc(x_615);
lean_dec(x_612);
x_616 = !lean_is_exclusive(x_613);
if (x_616 == 0)
{
lean_object* x_617; uint8_t x_618; 
x_617 = lean_ctor_get(x_613, 1);
lean_dec(x_617);
x_618 = !lean_is_exclusive(x_614);
if (x_618 == 0)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; uint8_t x_622; 
x_619 = lean_ctor_get(x_614, 0);
lean_inc(x_608);
x_620 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_619, x_1, x_608);
lean_ctor_set(x_614, 0, x_620);
x_621 = lean_st_ref_set(x_3, x_613, x_615);
lean_dec(x_3);
x_622 = !lean_is_exclusive(x_621);
if (x_622 == 0)
{
lean_object* x_623; 
x_623 = lean_ctor_get(x_621, 0);
lean_dec(x_623);
lean_ctor_set(x_621, 0, x_608);
return x_621;
}
else
{
lean_object* x_624; lean_object* x_625; 
x_624 = lean_ctor_get(x_621, 1);
lean_inc(x_624);
lean_dec(x_621);
x_625 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_625, 0, x_608);
lean_ctor_set(x_625, 1, x_624);
return x_625;
}
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_626 = lean_ctor_get(x_614, 0);
x_627 = lean_ctor_get(x_614, 1);
x_628 = lean_ctor_get(x_614, 2);
x_629 = lean_ctor_get(x_614, 3);
x_630 = lean_ctor_get(x_614, 4);
x_631 = lean_ctor_get(x_614, 5);
x_632 = lean_ctor_get(x_614, 6);
lean_inc(x_632);
lean_inc(x_631);
lean_inc(x_630);
lean_inc(x_629);
lean_inc(x_628);
lean_inc(x_627);
lean_inc(x_626);
lean_dec(x_614);
lean_inc(x_608);
x_633 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_626, x_1, x_608);
x_634 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_634, 0, x_633);
lean_ctor_set(x_634, 1, x_627);
lean_ctor_set(x_634, 2, x_628);
lean_ctor_set(x_634, 3, x_629);
lean_ctor_set(x_634, 4, x_630);
lean_ctor_set(x_634, 5, x_631);
lean_ctor_set(x_634, 6, x_632);
lean_ctor_set(x_613, 1, x_634);
x_635 = lean_st_ref_set(x_3, x_613, x_615);
lean_dec(x_3);
x_636 = lean_ctor_get(x_635, 1);
lean_inc(x_636);
if (lean_is_exclusive(x_635)) {
 lean_ctor_release(x_635, 0);
 lean_ctor_release(x_635, 1);
 x_637 = x_635;
} else {
 lean_dec_ref(x_635);
 x_637 = lean_box(0);
}
if (lean_is_scalar(x_637)) {
 x_638 = lean_alloc_ctor(0, 2, 0);
} else {
 x_638 = x_637;
}
lean_ctor_set(x_638, 0, x_608);
lean_ctor_set(x_638, 1, x_636);
return x_638;
}
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_639 = lean_ctor_get(x_613, 0);
x_640 = lean_ctor_get(x_613, 2);
x_641 = lean_ctor_get(x_613, 3);
x_642 = lean_ctor_get(x_613, 4);
lean_inc(x_642);
lean_inc(x_641);
lean_inc(x_640);
lean_inc(x_639);
lean_dec(x_613);
x_643 = lean_ctor_get(x_614, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_614, 1);
lean_inc(x_644);
x_645 = lean_ctor_get(x_614, 2);
lean_inc(x_645);
x_646 = lean_ctor_get(x_614, 3);
lean_inc(x_646);
x_647 = lean_ctor_get(x_614, 4);
lean_inc(x_647);
x_648 = lean_ctor_get(x_614, 5);
lean_inc(x_648);
x_649 = lean_ctor_get(x_614, 6);
lean_inc(x_649);
if (lean_is_exclusive(x_614)) {
 lean_ctor_release(x_614, 0);
 lean_ctor_release(x_614, 1);
 lean_ctor_release(x_614, 2);
 lean_ctor_release(x_614, 3);
 lean_ctor_release(x_614, 4);
 lean_ctor_release(x_614, 5);
 lean_ctor_release(x_614, 6);
 x_650 = x_614;
} else {
 lean_dec_ref(x_614);
 x_650 = lean_box(0);
}
lean_inc(x_608);
x_651 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_643, x_1, x_608);
if (lean_is_scalar(x_650)) {
 x_652 = lean_alloc_ctor(0, 7, 0);
} else {
 x_652 = x_650;
}
lean_ctor_set(x_652, 0, x_651);
lean_ctor_set(x_652, 1, x_644);
lean_ctor_set(x_652, 2, x_645);
lean_ctor_set(x_652, 3, x_646);
lean_ctor_set(x_652, 4, x_647);
lean_ctor_set(x_652, 5, x_648);
lean_ctor_set(x_652, 6, x_649);
x_653 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_653, 0, x_639);
lean_ctor_set(x_653, 1, x_652);
lean_ctor_set(x_653, 2, x_640);
lean_ctor_set(x_653, 3, x_641);
lean_ctor_set(x_653, 4, x_642);
x_654 = lean_st_ref_set(x_3, x_653, x_615);
lean_dec(x_3);
x_655 = lean_ctor_get(x_654, 1);
lean_inc(x_655);
if (lean_is_exclusive(x_654)) {
 lean_ctor_release(x_654, 0);
 lean_ctor_release(x_654, 1);
 x_656 = x_654;
} else {
 lean_dec_ref(x_654);
 x_656 = lean_box(0);
}
if (lean_is_scalar(x_656)) {
 x_657 = lean_alloc_ctor(0, 2, 0);
} else {
 x_657 = x_656;
}
lean_ctor_set(x_657, 0, x_608);
lean_ctor_set(x_657, 1, x_655);
return x_657;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_606;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_606;
}
}
else
{
lean_object* x_658; lean_object* x_659; uint8_t x_660; 
x_658 = lean_ctor_get(x_606, 0);
x_659 = lean_ctor_get(x_606, 1);
lean_inc(x_659);
lean_inc(x_658);
lean_dec(x_606);
x_660 = l_Lean_Expr_hasMVar(x_1);
if (x_660 == 0)
{
uint8_t x_661; 
x_661 = l_Lean_Expr_hasMVar(x_658);
if (x_661 == 0)
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_662 = lean_st_ref_take(x_3, x_659);
x_663 = lean_ctor_get(x_662, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_663, 1);
lean_inc(x_664);
x_665 = lean_ctor_get(x_662, 1);
lean_inc(x_665);
lean_dec(x_662);
x_666 = lean_ctor_get(x_663, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_663, 2);
lean_inc(x_667);
x_668 = lean_ctor_get(x_663, 3);
lean_inc(x_668);
x_669 = lean_ctor_get(x_663, 4);
lean_inc(x_669);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 lean_ctor_release(x_663, 1);
 lean_ctor_release(x_663, 2);
 lean_ctor_release(x_663, 3);
 lean_ctor_release(x_663, 4);
 x_670 = x_663;
} else {
 lean_dec_ref(x_663);
 x_670 = lean_box(0);
}
x_671 = lean_ctor_get(x_664, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_664, 1);
lean_inc(x_672);
x_673 = lean_ctor_get(x_664, 2);
lean_inc(x_673);
x_674 = lean_ctor_get(x_664, 3);
lean_inc(x_674);
x_675 = lean_ctor_get(x_664, 4);
lean_inc(x_675);
x_676 = lean_ctor_get(x_664, 5);
lean_inc(x_676);
x_677 = lean_ctor_get(x_664, 6);
lean_inc(x_677);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 lean_ctor_release(x_664, 1);
 lean_ctor_release(x_664, 2);
 lean_ctor_release(x_664, 3);
 lean_ctor_release(x_664, 4);
 lean_ctor_release(x_664, 5);
 lean_ctor_release(x_664, 6);
 x_678 = x_664;
} else {
 lean_dec_ref(x_664);
 x_678 = lean_box(0);
}
lean_inc(x_658);
x_679 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_671, x_1, x_658);
if (lean_is_scalar(x_678)) {
 x_680 = lean_alloc_ctor(0, 7, 0);
} else {
 x_680 = x_678;
}
lean_ctor_set(x_680, 0, x_679);
lean_ctor_set(x_680, 1, x_672);
lean_ctor_set(x_680, 2, x_673);
lean_ctor_set(x_680, 3, x_674);
lean_ctor_set(x_680, 4, x_675);
lean_ctor_set(x_680, 5, x_676);
lean_ctor_set(x_680, 6, x_677);
if (lean_is_scalar(x_670)) {
 x_681 = lean_alloc_ctor(0, 5, 0);
} else {
 x_681 = x_670;
}
lean_ctor_set(x_681, 0, x_666);
lean_ctor_set(x_681, 1, x_680);
lean_ctor_set(x_681, 2, x_667);
lean_ctor_set(x_681, 3, x_668);
lean_ctor_set(x_681, 4, x_669);
x_682 = lean_st_ref_set(x_3, x_681, x_665);
lean_dec(x_3);
x_683 = lean_ctor_get(x_682, 1);
lean_inc(x_683);
if (lean_is_exclusive(x_682)) {
 lean_ctor_release(x_682, 0);
 lean_ctor_release(x_682, 1);
 x_684 = x_682;
} else {
 lean_dec_ref(x_682);
 x_684 = lean_box(0);
}
if (lean_is_scalar(x_684)) {
 x_685 = lean_alloc_ctor(0, 2, 0);
} else {
 x_685 = x_684;
}
lean_ctor_set(x_685, 0, x_658);
lean_ctor_set(x_685, 1, x_683);
return x_685;
}
else
{
lean_object* x_686; 
lean_dec(x_3);
lean_dec(x_1);
x_686 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_686, 0, x_658);
lean_ctor_set(x_686, 1, x_659);
return x_686;
}
}
else
{
lean_object* x_687; 
lean_dec(x_3);
lean_dec(x_1);
x_687 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_687, 0, x_658);
lean_ctor_set(x_687, 1, x_659);
return x_687;
}
}
}
else
{
uint8_t x_688; 
lean_dec(x_3);
lean_dec(x_1);
x_688 = !lean_is_exclusive(x_606);
if (x_688 == 0)
{
return x_606;
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_689 = lean_ctor_get(x_606, 0);
x_690 = lean_ctor_get(x_606, 1);
lean_inc(x_690);
lean_inc(x_689);
lean_dec(x_606);
x_691 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_691, 0, x_689);
lean_ctor_set(x_691, 1, x_690);
return x_691;
}
}
}
else
{
lean_object* x_692; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_692 = lean_ctor_get(x_603, 0);
lean_inc(x_692);
lean_dec(x_603);
lean_ctor_set(x_597, 0, x_692);
return x_597;
}
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_693 = lean_ctor_get(x_597, 0);
x_694 = lean_ctor_get(x_597, 1);
lean_inc(x_694);
lean_inc(x_693);
lean_dec(x_597);
x_695 = lean_ctor_get(x_693, 1);
lean_inc(x_695);
lean_dec(x_693);
x_696 = lean_ctor_get(x_695, 0);
lean_inc(x_696);
lean_dec(x_695);
x_697 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_696, x_1);
if (lean_obj_tag(x_697) == 0)
{
lean_object* x_698; uint8_t x_699; lean_object* x_700; 
x_698 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1;
x_699 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_700 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_1, x_698, x_699, x_2, x_3, x_4, x_5, x_694);
if (lean_obj_tag(x_700) == 0)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; uint8_t x_704; 
x_701 = lean_ctor_get(x_700, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_700, 1);
lean_inc(x_702);
if (lean_is_exclusive(x_700)) {
 lean_ctor_release(x_700, 0);
 lean_ctor_release(x_700, 1);
 x_703 = x_700;
} else {
 lean_dec_ref(x_700);
 x_703 = lean_box(0);
}
x_704 = l_Lean_Expr_hasMVar(x_1);
if (x_704 == 0)
{
uint8_t x_705; 
x_705 = l_Lean_Expr_hasMVar(x_701);
if (x_705 == 0)
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
lean_dec(x_703);
x_706 = lean_st_ref_take(x_3, x_702);
x_707 = lean_ctor_get(x_706, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_707, 1);
lean_inc(x_708);
x_709 = lean_ctor_get(x_706, 1);
lean_inc(x_709);
lean_dec(x_706);
x_710 = lean_ctor_get(x_707, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_707, 2);
lean_inc(x_711);
x_712 = lean_ctor_get(x_707, 3);
lean_inc(x_712);
x_713 = lean_ctor_get(x_707, 4);
lean_inc(x_713);
if (lean_is_exclusive(x_707)) {
 lean_ctor_release(x_707, 0);
 lean_ctor_release(x_707, 1);
 lean_ctor_release(x_707, 2);
 lean_ctor_release(x_707, 3);
 lean_ctor_release(x_707, 4);
 x_714 = x_707;
} else {
 lean_dec_ref(x_707);
 x_714 = lean_box(0);
}
x_715 = lean_ctor_get(x_708, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_708, 1);
lean_inc(x_716);
x_717 = lean_ctor_get(x_708, 2);
lean_inc(x_717);
x_718 = lean_ctor_get(x_708, 3);
lean_inc(x_718);
x_719 = lean_ctor_get(x_708, 4);
lean_inc(x_719);
x_720 = lean_ctor_get(x_708, 5);
lean_inc(x_720);
x_721 = lean_ctor_get(x_708, 6);
lean_inc(x_721);
if (lean_is_exclusive(x_708)) {
 lean_ctor_release(x_708, 0);
 lean_ctor_release(x_708, 1);
 lean_ctor_release(x_708, 2);
 lean_ctor_release(x_708, 3);
 lean_ctor_release(x_708, 4);
 lean_ctor_release(x_708, 5);
 lean_ctor_release(x_708, 6);
 x_722 = x_708;
} else {
 lean_dec_ref(x_708);
 x_722 = lean_box(0);
}
lean_inc(x_701);
x_723 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_715, x_1, x_701);
if (lean_is_scalar(x_722)) {
 x_724 = lean_alloc_ctor(0, 7, 0);
} else {
 x_724 = x_722;
}
lean_ctor_set(x_724, 0, x_723);
lean_ctor_set(x_724, 1, x_716);
lean_ctor_set(x_724, 2, x_717);
lean_ctor_set(x_724, 3, x_718);
lean_ctor_set(x_724, 4, x_719);
lean_ctor_set(x_724, 5, x_720);
lean_ctor_set(x_724, 6, x_721);
if (lean_is_scalar(x_714)) {
 x_725 = lean_alloc_ctor(0, 5, 0);
} else {
 x_725 = x_714;
}
lean_ctor_set(x_725, 0, x_710);
lean_ctor_set(x_725, 1, x_724);
lean_ctor_set(x_725, 2, x_711);
lean_ctor_set(x_725, 3, x_712);
lean_ctor_set(x_725, 4, x_713);
x_726 = lean_st_ref_set(x_3, x_725, x_709);
lean_dec(x_3);
x_727 = lean_ctor_get(x_726, 1);
lean_inc(x_727);
if (lean_is_exclusive(x_726)) {
 lean_ctor_release(x_726, 0);
 lean_ctor_release(x_726, 1);
 x_728 = x_726;
} else {
 lean_dec_ref(x_726);
 x_728 = lean_box(0);
}
if (lean_is_scalar(x_728)) {
 x_729 = lean_alloc_ctor(0, 2, 0);
} else {
 x_729 = x_728;
}
lean_ctor_set(x_729, 0, x_701);
lean_ctor_set(x_729, 1, x_727);
return x_729;
}
else
{
lean_object* x_730; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_703)) {
 x_730 = lean_alloc_ctor(0, 2, 0);
} else {
 x_730 = x_703;
}
lean_ctor_set(x_730, 0, x_701);
lean_ctor_set(x_730, 1, x_702);
return x_730;
}
}
else
{
lean_object* x_731; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_703)) {
 x_731 = lean_alloc_ctor(0, 2, 0);
} else {
 x_731 = x_703;
}
lean_ctor_set(x_731, 0, x_701);
lean_ctor_set(x_731, 1, x_702);
return x_731;
}
}
else
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
lean_dec(x_3);
lean_dec(x_1);
x_732 = lean_ctor_get(x_700, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_700, 1);
lean_inc(x_733);
if (lean_is_exclusive(x_700)) {
 lean_ctor_release(x_700, 0);
 lean_ctor_release(x_700, 1);
 x_734 = x_700;
} else {
 lean_dec_ref(x_700);
 x_734 = lean_box(0);
}
if (lean_is_scalar(x_734)) {
 x_735 = lean_alloc_ctor(1, 2, 0);
} else {
 x_735 = x_734;
}
lean_ctor_set(x_735, 0, x_732);
lean_ctor_set(x_735, 1, x_733);
return x_735;
}
}
else
{
lean_object* x_736; lean_object* x_737; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_736 = lean_ctor_get(x_697, 0);
lean_inc(x_736);
lean_dec(x_697);
x_737 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_737, 0, x_736);
lean_ctor_set(x_737, 1, x_694);
return x_737;
}
}
}
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__2;
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
uint8_t x_40; lean_object* x_41; 
x_40 = 1;
lean_ctor_set_uint8(x_38, 9, x_40);
x_41 = l_Lean_Meta_inferTypeImp_infer(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
x_50 = lean_ctor_get_uint8(x_38, 0);
x_51 = lean_ctor_get_uint8(x_38, 1);
x_52 = lean_ctor_get_uint8(x_38, 2);
x_53 = lean_ctor_get_uint8(x_38, 3);
x_54 = lean_ctor_get_uint8(x_38, 4);
x_55 = lean_ctor_get_uint8(x_38, 5);
x_56 = lean_ctor_get_uint8(x_38, 6);
x_57 = lean_ctor_get_uint8(x_38, 7);
x_58 = lean_ctor_get_uint8(x_38, 8);
x_59 = lean_ctor_get_uint8(x_38, 10);
x_60 = lean_ctor_get_uint8(x_38, 11);
x_61 = lean_ctor_get_uint8(x_38, 12);
lean_dec(x_38);
x_62 = 1;
x_63 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_63, 0, x_50);
lean_ctor_set_uint8(x_63, 1, x_51);
lean_ctor_set_uint8(x_63, 2, x_52);
lean_ctor_set_uint8(x_63, 3, x_53);
lean_ctor_set_uint8(x_63, 4, x_54);
lean_ctor_set_uint8(x_63, 5, x_55);
lean_ctor_set_uint8(x_63, 6, x_56);
lean_ctor_set_uint8(x_63, 7, x_57);
lean_ctor_set_uint8(x_63, 8, x_58);
lean_ctor_set_uint8(x_63, 9, x_62);
lean_ctor_set_uint8(x_63, 10, x_59);
lean_ctor_set_uint8(x_63, 11, x_60);
lean_ctor_set_uint8(x_63, 12, x_61);
lean_ctor_set(x_2, 0, x_63);
x_64 = l_Lean_Meta_inferTypeImp_infer(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_73 = lean_ctor_get(x_2, 0);
x_74 = lean_ctor_get(x_2, 1);
x_75 = lean_ctor_get(x_2, 2);
x_76 = lean_ctor_get(x_2, 3);
x_77 = lean_ctor_get(x_2, 4);
x_78 = lean_ctor_get(x_2, 5);
x_79 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_80 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_2);
x_81 = lean_ctor_get_uint8(x_73, 0);
x_82 = lean_ctor_get_uint8(x_73, 1);
x_83 = lean_ctor_get_uint8(x_73, 2);
x_84 = lean_ctor_get_uint8(x_73, 3);
x_85 = lean_ctor_get_uint8(x_73, 4);
x_86 = lean_ctor_get_uint8(x_73, 5);
x_87 = lean_ctor_get_uint8(x_73, 6);
x_88 = lean_ctor_get_uint8(x_73, 7);
x_89 = lean_ctor_get_uint8(x_73, 8);
x_90 = lean_ctor_get_uint8(x_73, 10);
x_91 = lean_ctor_get_uint8(x_73, 11);
x_92 = lean_ctor_get_uint8(x_73, 12);
if (lean_is_exclusive(x_73)) {
 x_93 = x_73;
} else {
 lean_dec_ref(x_73);
 x_93 = lean_box(0);
}
x_94 = 1;
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 0, 13);
} else {
 x_95 = x_93;
}
lean_ctor_set_uint8(x_95, 0, x_81);
lean_ctor_set_uint8(x_95, 1, x_82);
lean_ctor_set_uint8(x_95, 2, x_83);
lean_ctor_set_uint8(x_95, 3, x_84);
lean_ctor_set_uint8(x_95, 4, x_85);
lean_ctor_set_uint8(x_95, 5, x_86);
lean_ctor_set_uint8(x_95, 6, x_87);
lean_ctor_set_uint8(x_95, 7, x_88);
lean_ctor_set_uint8(x_95, 8, x_89);
lean_ctor_set_uint8(x_95, 9, x_94);
lean_ctor_set_uint8(x_95, 10, x_90);
lean_ctor_set_uint8(x_95, 11, x_91);
lean_ctor_set_uint8(x_95, 12, x_92);
x_96 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_74);
lean_ctor_set(x_96, 2, x_75);
lean_ctor_set(x_96, 3, x_76);
lean_ctor_set(x_96, 4, x_77);
lean_ctor_set(x_96, 5, x_78);
lean_ctor_set_uint8(x_96, sizeof(void*)*6, x_79);
lean_ctor_set_uint8(x_96, sizeof(void*)*6 + 1, x_80);
x_97 = l_Lean_Meta_inferTypeImp_infer(x_1, x_96, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_97, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_97, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_104 = x_97;
} else {
 lean_dec_ref(x_97);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_4);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_add(x_10, x_106);
lean_dec(x_10);
x_108 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_108, 0, x_7);
lean_ctor_set(x_108, 1, x_8);
lean_ctor_set(x_108, 2, x_9);
lean_ctor_set(x_108, 3, x_107);
lean_ctor_set(x_108, 4, x_11);
lean_ctor_set(x_108, 5, x_12);
lean_ctor_set(x_108, 6, x_13);
lean_ctor_set(x_108, 7, x_14);
lean_ctor_set(x_108, 8, x_15);
lean_ctor_set(x_108, 9, x_16);
lean_ctor_set(x_108, 10, x_17);
lean_ctor_set(x_108, 11, x_19);
lean_ctor_set_uint8(x_108, sizeof(void*)*12, x_18);
lean_ctor_set_uint8(x_108, sizeof(void*)*12 + 1, x_20);
x_109 = lean_ctor_get(x_2, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_2, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_2, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_2, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_2, 4);
lean_inc(x_113);
x_114 = lean_ctor_get(x_2, 5);
lean_inc(x_114);
x_115 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_116 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_117 = x_2;
} else {
 lean_dec_ref(x_2);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get_uint8(x_109, 0);
x_119 = lean_ctor_get_uint8(x_109, 1);
x_120 = lean_ctor_get_uint8(x_109, 2);
x_121 = lean_ctor_get_uint8(x_109, 3);
x_122 = lean_ctor_get_uint8(x_109, 4);
x_123 = lean_ctor_get_uint8(x_109, 5);
x_124 = lean_ctor_get_uint8(x_109, 6);
x_125 = lean_ctor_get_uint8(x_109, 7);
x_126 = lean_ctor_get_uint8(x_109, 8);
x_127 = lean_ctor_get_uint8(x_109, 10);
x_128 = lean_ctor_get_uint8(x_109, 11);
x_129 = lean_ctor_get_uint8(x_109, 12);
if (lean_is_exclusive(x_109)) {
 x_130 = x_109;
} else {
 lean_dec_ref(x_109);
 x_130 = lean_box(0);
}
x_131 = 1;
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 0, 13);
} else {
 x_132 = x_130;
}
lean_ctor_set_uint8(x_132, 0, x_118);
lean_ctor_set_uint8(x_132, 1, x_119);
lean_ctor_set_uint8(x_132, 2, x_120);
lean_ctor_set_uint8(x_132, 3, x_121);
lean_ctor_set_uint8(x_132, 4, x_122);
lean_ctor_set_uint8(x_132, 5, x_123);
lean_ctor_set_uint8(x_132, 6, x_124);
lean_ctor_set_uint8(x_132, 7, x_125);
lean_ctor_set_uint8(x_132, 8, x_126);
lean_ctor_set_uint8(x_132, 9, x_131);
lean_ctor_set_uint8(x_132, 10, x_127);
lean_ctor_set_uint8(x_132, 11, x_128);
lean_ctor_set_uint8(x_132, 12, x_129);
if (lean_is_scalar(x_117)) {
 x_133 = lean_alloc_ctor(0, 6, 2);
} else {
 x_133 = x_117;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_110);
lean_ctor_set(x_133, 2, x_111);
lean_ctor_set(x_133, 3, x_112);
lean_ctor_set(x_133, 4, x_113);
lean_ctor_set(x_133, 5, x_114);
lean_ctor_set_uint8(x_133, sizeof(void*)*6, x_115);
lean_ctor_set_uint8(x_133, sizeof(void*)*6 + 1, x_116);
x_134 = l_Lean_Meta_inferTypeImp_infer(x_1, x_133, x_3, x_108, x_5, x_6);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_137 = x_134;
} else {
 lean_dec_ref(x_134);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_134, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_134, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_141 = x_134;
} else {
 lean_dec_ref(x_134);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
}
else
{
lean_object* x_143; 
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
x_143 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1(x_12, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_143;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_withLocalDecl_x27___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___rarg(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_Expr_fvar___override(x_11);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = 0;
x_17 = l_Lean_LocalContext_mkLocalDecl(x_15, x_11, x_1, x_3, x_2, x_16);
lean_ctor_set(x_5, 1, x_17);
x_18 = lean_apply_6(x_4, x_13, x_5, x_6, x_7, x_8, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_ctor_get(x_5, 2);
x_22 = lean_ctor_get(x_5, 3);
x_23 = lean_ctor_get(x_5, 4);
x_24 = lean_ctor_get(x_5, 5);
x_25 = lean_ctor_get_uint8(x_5, sizeof(void*)*6);
x_26 = lean_ctor_get_uint8(x_5, sizeof(void*)*6 + 1);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_27 = 0;
x_28 = l_Lean_LocalContext_mkLocalDecl(x_20, x_11, x_1, x_3, x_2, x_27);
x_29 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_21);
lean_ctor_set(x_29, 3, x_22);
lean_ctor_set(x_29, 4, x_23);
lean_ctor_set(x_29, 5, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*6, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*6 + 1, x_26);
x_30 = lean_apply_6(x_4, x_13, x_29, x_6, x_7, x_8, x_12);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_withLocalDecl_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_withLocalDecl_x27___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_withLocalDecl_x27___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Meta_InferType_0__Lean_Meta_withLocalDecl_x27___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
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
x_16 = l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___rarg(x_6, x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_17);
x_19 = l_Lean_Expr_fvar___override(x_17);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
x_22 = 0;
x_23 = l_Lean_LocalContext_mkLocalDecl(x_21, x_17, x_11, x_15, x_14, x_22);
x_24 = lean_ctor_get(x_3, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 4);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 5);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_29 = lean_ctor_get_uint8(x_3, sizeof(void*)*6 + 1);
lean_dec(x_3);
x_30 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_25);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*6, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*6 + 1, x_29);
x_31 = lean_array_push(x_2, x_19);
x_1 = x_13;
x_2 = x_31;
x_3 = x_30;
x_7 = x_18;
goto _start;
}
default: 
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_34 = l_Lean_Meta_whnfD(x_33, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
switch (lean_obj_tag(x_35)) {
case 3:
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
case 7:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_dec(x_34);
x_45 = l_Lean_Meta_typeFormerTypeLevel_go___closed__1;
x_1 = x_35;
x_2 = x_45;
x_7 = x_44;
goto _start;
}
default: 
{
uint8_t x_47; 
lean_dec(x_35);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_34);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_34, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_34, 0, x_49);
return x_34;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_34, 1);
lean_inc(x_50);
lean_dec(x_34);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_34);
if (x_53 == 0)
{
return x_34;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_34, 0);
x_55 = lean_ctor_get(x_34, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_34);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
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
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected dependent type ", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" in ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
lean_inc(x_14);
x_15 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Meta_arrowDomainsN___spec__4(x_2, x_14);
if (x_15 == 0)
{
size_t x_16; size_t x_17; lean_object* x_18; 
lean_dec(x_14);
x_16 = 1;
x_17 = lean_usize_add(x_5, x_16);
x_18 = lean_box(0);
x_5 = x_17;
x_6 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_20 = l_Lean_MessageData_ofExpr(x_14);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__2;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__4;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_MessageData_ofExpr(x_1);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_28, x_7, x_8, x_9, x_10, x_11);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
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
x_9 = lean_array_size(x_2);
x_10 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_arrowDomainsN___spec__1(x_9, x_10, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_size(x_12);
x_15 = lean_box(0);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5(x_1, x_2, x_12, x_14, x_10, x_15, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_12);
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
else
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lambda__1___boxed), 8, 1);
lean_closure_set(x_9, 0, x_2);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
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
l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2 = _init_l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2);
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
l_Lean_Meta_inferTypeImp_infer___closed__1 = _init_l_Lean_Meta_inferTypeImp_infer___closed__1();
lean_mark_persistent(l_Lean_Meta_inferTypeImp_infer___closed__1);
l_Lean_Meta_inferTypeImp_infer___closed__2 = _init_l_Lean_Meta_inferTypeImp_infer___closed__2();
lean_mark_persistent(l_Lean_Meta_inferTypeImp_infer___closed__2);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__2);
l_Lean_Meta_typeFormerTypeLevel_go___closed__1 = _init_l_Lean_Meta_typeFormerTypeLevel_go___closed__1();
lean_mark_persistent(l_Lean_Meta_typeFormerTypeLevel_go___closed__1);
l_Lean_Meta_isPropFormerType___closed__1 = _init_l_Lean_Meta_isPropFormerType___closed__1();
lean_mark_persistent(l_Lean_Meta_isPropFormerType___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_arrowDomainsN___spec__5___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
