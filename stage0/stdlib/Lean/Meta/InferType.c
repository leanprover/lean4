// Lean compiler output
// Module: Lean.Meta.InferType
// Imports: Init Lean.Data.LBool Lean.Meta.Basic
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
extern lean_object* l_Lean_ExprStructEq_instHashableExprStructEq;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwFunctionExpected___rarg___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_withLocalDecl_x27___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwFunctionExpected___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___closed__1;
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__4(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Core_instantiateTypeLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownMVar___spec__1(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___rarg___closed__1;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected(lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__10;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Expr_instantiateBetaRevRange___spec__1(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels(lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_withLocalDecl_x27___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownMVar___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_instantiateBetaRevRange_visit___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
static lean_object* l_Lean_Meta_throwTypeExcepted___rarg___closed__2;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Literal_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Expr_instantiateBetaRevRange_visit___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__3;
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___rarg___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_mkAppRangeAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_instantiateBetaRevRange_visit___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwTypeExcepted___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwUnknownMVar___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwIncorrectNumberOfLevels___spec__1(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at_Lean_Expr_instantiateBetaRevRange_visit___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__5;
static lean_object* l_Lean_Meta_throwTypeExcepted___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1(lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__11;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Expr_instantiateBetaRevRange_visit___spec__7___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
extern lean_object* l_Lean_instInhabitedExpr;
static size_t l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___closed__2;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExcepted(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwFunctionExpected___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonadStateT___rarg(lean_object*);
lean_object* lean_expr_consume_type_annotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwFunctionExpected___rarg___closed__1;
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at_Lean_Expr_instantiateBetaRevRange_visit___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__8;
lean_object* lean_usize_to_nat(size_t);
size_t lean_data_hashmap_mk_idx(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
extern lean_object* l_Lean_ExprStructEq_instBEqExprStructEq;
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwUnknownMVar___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp_infer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerTypeQuick___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_isTypeFormerTypeQuick(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Expr_instantiateBetaRevRange___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(uint8_t, uint8_t);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_withLocalDecl_x27(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshFVarId___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_inferTypeImp_infer___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__2;
static lean_object* l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10___closed__2;
static lean_object* l_Lean_Meta_throwUnknownMVar___rarg___closed__2;
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Id_instMonadId;
extern lean_object* l_instBEqNat;
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwUnknownMVar___rarg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwIncorrectNumberOfLevels___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
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
lean_object* l_Lean_Level_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isTypeFormerType_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_throwTypeExcepted___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
lean_object* l_instHashableNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = l_Lean_Expr_hash(x_5);
lean_dec(x_5);
x_8 = lean_uint64_of_nat(x_6);
lean_dec(x_6);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_data_hashmap_mk_idx(x_4, x_9);
x_11 = lean_array_uget(x_3, x_10);
lean_dec(x_3);
x_12 = l_Lean_AssocList_find_x3f___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_2, x_11);
lean_dec(x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__4(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Expr_instantiateBetaRevRange_visit___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_data_hashmap_mk_idx(x_7, x_9);
x_11 = lean_array_uget(x_2, x_10);
lean_ctor_set(x_3, 2, x_11);
x_12 = lean_array_uset(x_2, x_10, x_3);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_17 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_18 = lean_apply_1(x_1, x_14);
x_19 = lean_unbox_uint64(x_18);
lean_dec(x_18);
x_20 = lean_data_hashmap_mk_idx(x_17, x_19);
x_21 = lean_array_uget(x_2, x_20);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_array_uset(x_2, x_20, x_22);
x_2 = x_23;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_Expr_instantiateBetaRevRange_visit___spec__7___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = l_Lean_Expr_hash(x_7);
lean_dec(x_7);
x_10 = lean_uint64_of_nat(x_8);
lean_dec(x_8);
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = lean_data_hashmap_mk_idx(x_6, x_11);
x_13 = lean_array_uget(x_1, x_12);
lean_ctor_set(x_2, 2, x_13);
x_14 = lean_array_uset(x_1, x_12, x_2);
x_1 = x_14;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_19 = lean_array_get_size(x_1);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
x_22 = l_Lean_Expr_hash(x_20);
lean_dec(x_20);
x_23 = lean_uint64_of_nat(x_21);
lean_dec(x_21);
x_24 = lean_uint64_mix_hash(x_22, x_23);
x_25 = lean_data_hashmap_mk_idx(x_19, x_24);
x_26 = lean_array_uget(x_1, x_25);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_array_uset(x_1, x_25, x_27);
x_1 = x_28;
x_2 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_AssocList_foldlM___at_Lean_Expr_instantiateBetaRevRange_visit___spec__7___at_Lean_Expr_instantiateBetaRevRange_visit___spec__8(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_HashMapImp_moveEntries___at_Lean_Expr_instantiateBetaRevRange_visit___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_14 = l_Lean_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__9(x_1, x_2, x_8);
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
x_16 = l_Lean_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__9(x_1, x_2, x_8);
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
x_25 = l_Lean_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__9(x_1, x_2, x_19);
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
x_28 = l_Lean_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__9(x_1, x_2, x_19);
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
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; lean_object* x_14; uint8_t x_15; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = l_Lean_Expr_hash(x_8);
lean_dec(x_8);
x_11 = lean_uint64_of_nat(x_9);
lean_dec(x_9);
x_12 = lean_uint64_mix_hash(x_10, x_11);
lean_inc(x_7);
x_13 = lean_data_hashmap_mk_idx(x_7, x_12);
x_14 = lean_array_uget(x_6, x_13);
x_15 = l_Lean_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__4(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_5, x_16);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 2, x_14);
x_19 = lean_array_uset(x_6, x_13, x_18);
x_20 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_17);
x_21 = lean_nat_dec_le(x_20, x_7);
lean_dec(x_7);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_free_object(x_1);
x_22 = l_Lean_HashMapImp_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__5(x_17, x_19);
return x_22;
}
else
{
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
x_23 = l_Lean_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__9(x_2, x_3, x_14);
x_24 = lean_array_uset(x_6, x_13, x_23);
lean_ctor_set(x_1, 1, x_24);
return x_1;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; lean_object* x_34; uint8_t x_35; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
x_27 = lean_array_get_size(x_26);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
x_30 = l_Lean_Expr_hash(x_28);
lean_dec(x_28);
x_31 = lean_uint64_of_nat(x_29);
lean_dec(x_29);
x_32 = lean_uint64_mix_hash(x_30, x_31);
lean_inc(x_27);
x_33 = lean_data_hashmap_mk_idx(x_27, x_32);
x_34 = lean_array_uget(x_26, x_33);
x_35 = l_Lean_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__4(x_2, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_25, x_36);
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set(x_38, 2, x_34);
x_39 = lean_array_uset(x_26, x_33, x_38);
x_40 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_37);
x_41 = lean_nat_dec_le(x_40, x_27);
lean_dec(x_27);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_Lean_HashMapImp_expand___at_Lean_Expr_instantiateBetaRevRange_visit___spec__5(x_37, x_39);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_27);
x_44 = l_Lean_AssocList_replace___at_Lean_Expr_instantiateBetaRevRange_visit___spec__9(x_2, x_3, x_34);
x_45 = lean_array_uset(x_26, x_33, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_25);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Id_instMonadId;
x_2 = l_StateT_instMonadStateT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10___closed__1;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10___closed__2;
x_4 = lean_panic_fn(x_3, x_1);
x_5 = lean_apply_1(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_instantiateBetaRevRange_visit___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at_Lean_Expr_instantiateBetaRevRange_visit___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_4);
lean_inc(x_7);
x_14 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_7, x_4, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_8);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = l_Array_mapMUnsafe_map___at_Lean_Expr_instantiateBetaRevRange_visit___spec__11(x_1, x_2, x_3, x_4, x_18, x_19, x_8, x_16);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lean_Expr_isBVar(x_7);
lean_dec(x_7);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = l_Lean_mkAppRev(x_15, x_22);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
uint8_t x_25; lean_object* x_26; 
x_25 = 0;
x_26 = l_Lean_Expr_betaRev(x_15, x_22, x_25, x_25);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = l_Lean_Expr_isBVar(x_7);
lean_dec(x_7);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_mkAppRev(x_15, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_32 = 0;
x_33 = l_Lean_Expr_betaRev(x_15, x_27, x_32, x_32);
lean_dec(x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ExprStructEq_instBEqExprStructEq;
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
x_1 = l_Lean_ExprStructEq_instHashableExprStructEq;
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
x_1 = lean_mk_string_from_bytes("Lean.Meta.InferType", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Expr.instantiateBetaRevRange.visit", 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__7() {
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
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__8() {
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
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__9() {
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
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange_visit___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__4;
x_2 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__5;
x_3 = lean_unsigned_to_nat(61u);
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
x_3 = lean_unsigned_to_nat(65u);
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
lean_object* x_9; lean_object* x_10; 
lean_inc(x_5);
lean_inc(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
lean_inc(x_9);
lean_inc(x_6);
x_10 = l_Lean_HashMapImp_find_x3f___at_Lean_Expr_instantiateBetaRevRange_visit___spec__1(x_6, x_9);
if (lean_obj_tag(x_10) == 0)
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_nat_sub(x_2, x_1);
x_13 = lean_nat_add(x_5, x_12);
x_14 = lean_nat_dec_lt(x_11, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_15 = lean_nat_sub(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
x_16 = l_Lean_Expr_bvar___override(x_15);
lean_inc(x_16);
x_17 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_6, x_9, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_12);
x_19 = lean_nat_sub(x_11, x_5);
lean_dec(x_11);
x_20 = lean_nat_sub(x_2, x_19);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_20, x_21);
lean_dec(x_20);
x_23 = lean_array_get_size(x_3);
x_24 = lean_nat_dec_lt(x_22, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_22);
x_25 = l_Lean_instInhabitedExpr;
x_26 = l___private_Init_Util_0__outOfBounds___rarg(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_expr_lift_loose_bvars(x_26, x_27, x_5);
lean_dec(x_5);
lean_dec(x_26);
lean_inc(x_28);
x_29 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_6, x_9, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_array_fget(x_3, x_22);
lean_dec(x_22);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_expr_lift_loose_bvars(x_31, x_32, x_5);
lean_dec(x_5);
lean_dec(x_31);
lean_inc(x_33);
x_34 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_6, x_9, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
case 1:
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_5);
lean_dec(x_4);
x_36 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__7;
x_37 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10(x_36, x_6);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
x_41 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_40, x_9, x_39);
lean_ctor_set(x_37, 1, x_41);
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_37);
lean_inc(x_42);
x_44 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_43, x_9, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
case 2:
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_5);
lean_dec(x_4);
x_46 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__8;
x_47 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10(x_46, x_6);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
x_51 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_50, x_9, x_49);
lean_ctor_set(x_47, 1, x_51);
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
lean_inc(x_52);
x_54 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_53, x_9, x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
case 3:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_5);
lean_dec(x_4);
x_56 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__9;
x_57 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10(x_56, x_6);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
x_61 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_60, x_9, x_59);
lean_ctor_set(x_57, 1, x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_57);
lean_inc(x_62);
x_64 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_63, x_9, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
case 4:
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_dec(x_5);
lean_dec(x_4);
x_66 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__10;
x_67 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10(x_66, x_6);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
x_71 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_70, x_9, x_69);
lean_ctor_set(x_67, 1, x_71);
return x_67;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_67, 0);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_67);
lean_inc(x_72);
x_74 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_73, x_9, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
case 5:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_76 = lean_unsigned_to_nat(0u);
x_77 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_4, x_76);
x_78 = lean_mk_empty_array_with_capacity(x_77);
lean_dec(x_77);
x_79 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__1;
x_80 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__3;
x_81 = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at_Lean_Expr_instantiateBetaRevRange_visit___spec__12(x_1, x_2, x_3, x_5, x_79, x_80, x_4, x_78, x_6);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
x_85 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_84, x_9, x_83);
lean_ctor_set(x_81, 1, x_85);
return x_81;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_81, 0);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_81);
lean_inc(x_86);
x_88 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_87, x_9, x_86);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
case 6:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_90 = lean_ctor_get(x_4, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_4, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_4, 2);
lean_inc(x_92);
x_93 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
lean_dec(x_4);
lean_inc(x_5);
lean_inc(x_91);
x_94 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_91, x_5, x_6);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_add(x_5, x_97);
lean_dec(x_5);
lean_inc(x_92);
x_99 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_92, x_98, x_96);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; size_t x_104; size_t x_105; uint8_t x_106; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_103 = l_Lean_Expr_lam___override(x_90, x_91, x_92, x_93);
x_104 = lean_ptr_addr(x_91);
lean_dec(x_91);
x_105 = lean_ptr_addr(x_95);
x_106 = lean_usize_dec_eq(x_104, x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_103);
lean_dec(x_92);
x_107 = l_Lean_Expr_lam___override(x_90, x_95, x_101, x_93);
lean_inc(x_107);
x_108 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_102, x_9, x_107);
lean_ctor_set(x_99, 1, x_108);
lean_ctor_set(x_99, 0, x_107);
return x_99;
}
else
{
size_t x_109; size_t x_110; uint8_t x_111; 
x_109 = lean_ptr_addr(x_92);
lean_dec(x_92);
x_110 = lean_ptr_addr(x_101);
x_111 = lean_usize_dec_eq(x_109, x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_103);
x_112 = l_Lean_Expr_lam___override(x_90, x_95, x_101, x_93);
lean_inc(x_112);
x_113 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_102, x_9, x_112);
lean_ctor_set(x_99, 1, x_113);
lean_ctor_set(x_99, 0, x_112);
return x_99;
}
else
{
uint8_t x_114; 
x_114 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_93, x_93);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_103);
x_115 = l_Lean_Expr_lam___override(x_90, x_95, x_101, x_93);
lean_inc(x_115);
x_116 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_102, x_9, x_115);
lean_ctor_set(x_99, 1, x_116);
lean_ctor_set(x_99, 0, x_115);
return x_99;
}
else
{
lean_object* x_117; 
lean_dec(x_101);
lean_dec(x_95);
lean_dec(x_90);
lean_inc(x_103);
x_117 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_102, x_9, x_103);
lean_ctor_set(x_99, 1, x_117);
lean_ctor_set(x_99, 0, x_103);
return x_99;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; size_t x_121; size_t x_122; uint8_t x_123; 
x_118 = lean_ctor_get(x_99, 0);
x_119 = lean_ctor_get(x_99, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_99);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
x_120 = l_Lean_Expr_lam___override(x_90, x_91, x_92, x_93);
x_121 = lean_ptr_addr(x_91);
lean_dec(x_91);
x_122 = lean_ptr_addr(x_95);
x_123 = lean_usize_dec_eq(x_121, x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_120);
lean_dec(x_92);
x_124 = l_Lean_Expr_lam___override(x_90, x_95, x_118, x_93);
lean_inc(x_124);
x_125 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_119, x_9, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
else
{
size_t x_127; size_t x_128; uint8_t x_129; 
x_127 = lean_ptr_addr(x_92);
lean_dec(x_92);
x_128 = lean_ptr_addr(x_118);
x_129 = lean_usize_dec_eq(x_127, x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_120);
x_130 = l_Lean_Expr_lam___override(x_90, x_95, x_118, x_93);
lean_inc(x_130);
x_131 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_119, x_9, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
else
{
uint8_t x_133; 
x_133 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_93, x_93);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_120);
x_134 = l_Lean_Expr_lam___override(x_90, x_95, x_118, x_93);
lean_inc(x_134);
x_135 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_119, x_9, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_118);
lean_dec(x_95);
lean_dec(x_90);
lean_inc(x_120);
x_137 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_119, x_9, x_120);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_120);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
}
case 7:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_139 = lean_ctor_get(x_4, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_4, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_4, 2);
lean_inc(x_141);
x_142 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
lean_dec(x_4);
lean_inc(x_5);
lean_inc(x_140);
x_143 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_140, x_5, x_6);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_unsigned_to_nat(1u);
x_147 = lean_nat_add(x_5, x_146);
lean_dec(x_5);
lean_inc(x_141);
x_148 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_141, x_147, x_145);
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; size_t x_153; size_t x_154; uint8_t x_155; 
x_150 = lean_ctor_get(x_148, 0);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
x_152 = l_Lean_Expr_forallE___override(x_139, x_140, x_141, x_142);
x_153 = lean_ptr_addr(x_140);
lean_dec(x_140);
x_154 = lean_ptr_addr(x_144);
x_155 = lean_usize_dec_eq(x_153, x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_152);
lean_dec(x_141);
x_156 = l_Lean_Expr_forallE___override(x_139, x_144, x_150, x_142);
lean_inc(x_156);
x_157 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_151, x_9, x_156);
lean_ctor_set(x_148, 1, x_157);
lean_ctor_set(x_148, 0, x_156);
return x_148;
}
else
{
size_t x_158; size_t x_159; uint8_t x_160; 
x_158 = lean_ptr_addr(x_141);
lean_dec(x_141);
x_159 = lean_ptr_addr(x_150);
x_160 = lean_usize_dec_eq(x_158, x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_152);
x_161 = l_Lean_Expr_forallE___override(x_139, x_144, x_150, x_142);
lean_inc(x_161);
x_162 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_151, x_9, x_161);
lean_ctor_set(x_148, 1, x_162);
lean_ctor_set(x_148, 0, x_161);
return x_148;
}
else
{
uint8_t x_163; 
x_163 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_142, x_142);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_152);
x_164 = l_Lean_Expr_forallE___override(x_139, x_144, x_150, x_142);
lean_inc(x_164);
x_165 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_151, x_9, x_164);
lean_ctor_set(x_148, 1, x_165);
lean_ctor_set(x_148, 0, x_164);
return x_148;
}
else
{
lean_object* x_166; 
lean_dec(x_150);
lean_dec(x_144);
lean_dec(x_139);
lean_inc(x_152);
x_166 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_151, x_9, x_152);
lean_ctor_set(x_148, 1, x_166);
lean_ctor_set(x_148, 0, x_152);
return x_148;
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; size_t x_170; size_t x_171; uint8_t x_172; 
x_167 = lean_ctor_get(x_148, 0);
x_168 = lean_ctor_get(x_148, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_148);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
x_169 = l_Lean_Expr_forallE___override(x_139, x_140, x_141, x_142);
x_170 = lean_ptr_addr(x_140);
lean_dec(x_140);
x_171 = lean_ptr_addr(x_144);
x_172 = lean_usize_dec_eq(x_170, x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_169);
lean_dec(x_141);
x_173 = l_Lean_Expr_forallE___override(x_139, x_144, x_167, x_142);
lean_inc(x_173);
x_174 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_168, x_9, x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
else
{
size_t x_176; size_t x_177; uint8_t x_178; 
x_176 = lean_ptr_addr(x_141);
lean_dec(x_141);
x_177 = lean_ptr_addr(x_167);
x_178 = lean_usize_dec_eq(x_176, x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_169);
x_179 = l_Lean_Expr_forallE___override(x_139, x_144, x_167, x_142);
lean_inc(x_179);
x_180 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_168, x_9, x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
else
{
uint8_t x_182; 
x_182 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_142, x_142);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_169);
x_183 = l_Lean_Expr_forallE___override(x_139, x_144, x_167, x_142);
lean_inc(x_183);
x_184 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_168, x_9, x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_167);
lean_dec(x_144);
lean_dec(x_139);
lean_inc(x_169);
x_186 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_168, x_9, x_169);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_169);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
}
}
case 8:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_188 = lean_ctor_get(x_4, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_4, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_4, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_4, 3);
lean_inc(x_191);
x_192 = lean_ctor_get_uint8(x_4, sizeof(void*)*4 + 8);
lean_inc(x_5);
lean_inc(x_189);
x_193 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_189, x_5, x_6);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
lean_inc(x_5);
lean_inc(x_190);
x_196 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_190, x_5, x_195);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_unsigned_to_nat(1u);
x_200 = lean_nat_add(x_5, x_199);
lean_dec(x_5);
lean_inc(x_191);
x_201 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_191, x_200, x_198);
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; size_t x_205; size_t x_206; uint8_t x_207; 
x_203 = lean_ctor_get(x_201, 0);
x_204 = lean_ctor_get(x_201, 1);
x_205 = lean_ptr_addr(x_189);
lean_dec(x_189);
x_206 = lean_ptr_addr(x_194);
x_207 = lean_usize_dec_eq(x_205, x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_4);
x_208 = l_Lean_Expr_letE___override(x_188, x_194, x_197, x_203, x_192);
lean_inc(x_208);
x_209 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_204, x_9, x_208);
lean_ctor_set(x_201, 1, x_209);
lean_ctor_set(x_201, 0, x_208);
return x_201;
}
else
{
size_t x_210; size_t x_211; uint8_t x_212; 
x_210 = lean_ptr_addr(x_190);
lean_dec(x_190);
x_211 = lean_ptr_addr(x_197);
x_212 = lean_usize_dec_eq(x_210, x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_191);
lean_dec(x_4);
x_213 = l_Lean_Expr_letE___override(x_188, x_194, x_197, x_203, x_192);
lean_inc(x_213);
x_214 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_204, x_9, x_213);
lean_ctor_set(x_201, 1, x_214);
lean_ctor_set(x_201, 0, x_213);
return x_201;
}
else
{
size_t x_215; size_t x_216; uint8_t x_217; 
x_215 = lean_ptr_addr(x_191);
lean_dec(x_191);
x_216 = lean_ptr_addr(x_203);
x_217 = lean_usize_dec_eq(x_215, x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_4);
x_218 = l_Lean_Expr_letE___override(x_188, x_194, x_197, x_203, x_192);
lean_inc(x_218);
x_219 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_204, x_9, x_218);
lean_ctor_set(x_201, 1, x_219);
lean_ctor_set(x_201, 0, x_218);
return x_201;
}
else
{
lean_object* x_220; 
lean_dec(x_203);
lean_dec(x_197);
lean_dec(x_194);
lean_dec(x_188);
lean_inc(x_4);
x_220 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_204, x_9, x_4);
lean_ctor_set(x_201, 1, x_220);
lean_ctor_set(x_201, 0, x_4);
return x_201;
}
}
}
}
else
{
lean_object* x_221; lean_object* x_222; size_t x_223; size_t x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_201, 0);
x_222 = lean_ctor_get(x_201, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_201);
x_223 = lean_ptr_addr(x_189);
lean_dec(x_189);
x_224 = lean_ptr_addr(x_194);
x_225 = lean_usize_dec_eq(x_223, x_224);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_4);
x_226 = l_Lean_Expr_letE___override(x_188, x_194, x_197, x_221, x_192);
lean_inc(x_226);
x_227 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_222, x_9, x_226);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
else
{
size_t x_229; size_t x_230; uint8_t x_231; 
x_229 = lean_ptr_addr(x_190);
lean_dec(x_190);
x_230 = lean_ptr_addr(x_197);
x_231 = lean_usize_dec_eq(x_229, x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_191);
lean_dec(x_4);
x_232 = l_Lean_Expr_letE___override(x_188, x_194, x_197, x_221, x_192);
lean_inc(x_232);
x_233 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_222, x_9, x_232);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
else
{
size_t x_235; size_t x_236; uint8_t x_237; 
x_235 = lean_ptr_addr(x_191);
lean_dec(x_191);
x_236 = lean_ptr_addr(x_221);
x_237 = lean_usize_dec_eq(x_235, x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_4);
x_238 = l_Lean_Expr_letE___override(x_188, x_194, x_197, x_221, x_192);
lean_inc(x_238);
x_239 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_222, x_9, x_238);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; 
lean_dec(x_221);
lean_dec(x_197);
lean_dec(x_194);
lean_dec(x_188);
lean_inc(x_4);
x_241 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_222, x_9, x_4);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_4);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
}
}
case 9:
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; 
lean_dec(x_5);
lean_dec(x_4);
x_243 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__11;
x_244 = l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10(x_243, x_6);
x_245 = !lean_is_exclusive(x_244);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_244, 0);
x_247 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
x_248 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_247, x_9, x_246);
lean_ctor_set(x_244, 1, x_248);
return x_244;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_244, 0);
x_250 = lean_ctor_get(x_244, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_244);
lean_inc(x_249);
x_251 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_250, x_9, x_249);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
case 10:
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_253 = lean_ctor_get(x_4, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_4, 1);
lean_inc(x_254);
lean_inc(x_254);
x_255 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_254, x_5, x_6);
x_256 = !lean_is_exclusive(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; size_t x_259; size_t x_260; uint8_t x_261; 
x_257 = lean_ctor_get(x_255, 0);
x_258 = lean_ctor_get(x_255, 1);
x_259 = lean_ptr_addr(x_254);
lean_dec(x_254);
x_260 = lean_ptr_addr(x_257);
x_261 = lean_usize_dec_eq(x_259, x_260);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_4);
x_262 = l_Lean_Expr_mdata___override(x_253, x_257);
lean_inc(x_262);
x_263 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_258, x_9, x_262);
lean_ctor_set(x_255, 1, x_263);
lean_ctor_set(x_255, 0, x_262);
return x_255;
}
else
{
lean_object* x_264; 
lean_dec(x_257);
lean_dec(x_253);
lean_inc(x_4);
x_264 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_258, x_9, x_4);
lean_ctor_set(x_255, 1, x_264);
lean_ctor_set(x_255, 0, x_4);
return x_255;
}
}
else
{
lean_object* x_265; lean_object* x_266; size_t x_267; size_t x_268; uint8_t x_269; 
x_265 = lean_ctor_get(x_255, 0);
x_266 = lean_ctor_get(x_255, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_255);
x_267 = lean_ptr_addr(x_254);
lean_dec(x_254);
x_268 = lean_ptr_addr(x_265);
x_269 = lean_usize_dec_eq(x_267, x_268);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_4);
x_270 = l_Lean_Expr_mdata___override(x_253, x_265);
lean_inc(x_270);
x_271 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_266, x_9, x_270);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; 
lean_dec(x_265);
lean_dec(x_253);
lean_inc(x_4);
x_273 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_266, x_9, x_4);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_4);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
default: 
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_275 = lean_ctor_get(x_4, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_4, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_4, 2);
lean_inc(x_277);
lean_inc(x_277);
x_278 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_277, x_5, x_6);
x_279 = !lean_is_exclusive(x_278);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; size_t x_282; size_t x_283; uint8_t x_284; 
x_280 = lean_ctor_get(x_278, 0);
x_281 = lean_ctor_get(x_278, 1);
x_282 = lean_ptr_addr(x_277);
lean_dec(x_277);
x_283 = lean_ptr_addr(x_280);
x_284 = lean_usize_dec_eq(x_282, x_283);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; 
lean_dec(x_4);
x_285 = l_Lean_Expr_proj___override(x_275, x_276, x_280);
lean_inc(x_285);
x_286 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_281, x_9, x_285);
lean_ctor_set(x_278, 1, x_286);
lean_ctor_set(x_278, 0, x_285);
return x_278;
}
else
{
lean_object* x_287; 
lean_dec(x_280);
lean_dec(x_276);
lean_dec(x_275);
lean_inc(x_4);
x_287 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_281, x_9, x_4);
lean_ctor_set(x_278, 1, x_287);
lean_ctor_set(x_278, 0, x_4);
return x_278;
}
}
else
{
lean_object* x_288; lean_object* x_289; size_t x_290; size_t x_291; uint8_t x_292; 
x_288 = lean_ctor_get(x_278, 0);
x_289 = lean_ctor_get(x_278, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_278);
x_290 = lean_ptr_addr(x_277);
lean_dec(x_277);
x_291 = lean_ptr_addr(x_288);
x_292 = lean_usize_dec_eq(x_290, x_291);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_4);
x_293 = l_Lean_Expr_proj___override(x_275, x_276, x_288);
lean_inc(x_293);
x_294 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_289, x_9, x_293);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
else
{
lean_object* x_296; lean_object* x_297; 
lean_dec(x_288);
lean_dec(x_276);
lean_dec(x_275);
lean_inc(x_4);
x_296 = l_Lean_HashMap_insert___at_Lean_Expr_instantiateBetaRevRange_visit___spec__3(x_289, x_9, x_4);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_4);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
}
}
}
}
else
{
lean_object* x_298; lean_object* x_299; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_298 = lean_ctor_get(x_10, 0);
lean_inc(x_298);
lean_dec(x_10);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_6);
return x_299;
}
}
else
{
lean_object* x_300; 
lean_dec(x_5);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_4);
lean_ctor_set(x_300, 1, x_6);
return x_300;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at_Lean_Expr_instantiateBetaRevRange_visit___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_Expr_instantiateBetaRevRange_visit___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Expr_instantiateBetaRevRange_visit___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Expr_instantiateBetaRevRange_visit___spec__11(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at_Lean_Expr_instantiateBetaRevRange_visit___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at_Lean_Expr_instantiateBetaRevRange_visit___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Expr_instantiateBetaRevRange___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("assertion violation: ", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("stop ≤ args.size\n    ", 23);
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
x_1 = lean_mk_string_from_bytes("Lean.Expr.instantiateBetaRevRange", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_instantiateBetaRevRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__4;
x_2 = l_Lean_Expr_instantiateBetaRevRange___closed__4;
x_3 = lean_unsigned_to_nat(27u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Expr_instantiateBetaRevRange___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
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
x_10 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(8u);
x_12 = l_Lean_mkHashMapImp___rarg(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Expr_instantiateBetaRevRange_visit(x_2, x_3, x_4, x_1, x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_Expr_instantiateBetaRevRange___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_Expr_instantiateBetaRevRange___spec__1(x_1);
lean_dec(x_1);
return x_2;
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
x_1 = lean_mk_string_from_bytes("function expected", 17);
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
x_1 = lean_mk_string_from_bytes("", 0);
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
x_1 = lean_mk_string_from_bytes("incorrect number of universe levels ", 36);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_throwIncorrectNumberOfLevels___rarg), 7, 0);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = l_Lean_Core_instantiateTypeLevelParams(x_9, x_2, x_5, x_6, x_10);
lean_dec(x_9);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_1 = lean_mk_string_from_bytes("invalid projection", 18);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_7, x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_environment_find(x_21, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_17);
lean_dec(x_13);
x_23 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_24 = l_Lean_indentExpr(x_23);
x_25 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_28, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
if (lean_obj_tag(x_30) == 5)
{
lean_object* x_31; uint8_t x_32; uint8_t x_134; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_134 = lean_ctor_get_uint8(x_31, sizeof(void*)*5);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_31, 2);
lean_inc(x_135);
x_136 = lean_unsigned_to_nat(0u);
x_137 = lean_nat_dec_eq(x_135, x_136);
lean_dec(x_135);
if (x_137 == 0)
{
uint8_t x_138; 
x_138 = 1;
x_32 = x_138;
goto block_133;
}
else
{
uint8_t x_139; 
x_139 = 0;
x_32 = x_139;
goto block_133;
}
}
else
{
uint8_t x_140; 
x_140 = 1;
x_32 = x_140;
goto block_133;
}
block_133:
{
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 4);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_13);
x_34 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_35 = l_Lean_indentExpr(x_34);
x_36 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_39, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
lean_dec(x_33);
x_43 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_42, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 6)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_103; uint8_t x_104; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_31, 1);
lean_inc(x_47);
lean_dec(x_31);
x_48 = lean_unsigned_to_nat(0u);
x_49 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_13, x_48);
x_50 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__1;
lean_inc(x_49);
x_51 = lean_mk_array(x_49, x_50);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_sub(x_49, x_52);
lean_dec(x_49);
x_54 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_13, x_51, x_53);
x_103 = lean_array_get_size(x_54);
x_104 = lean_nat_dec_eq(x_47, x_103);
lean_dec(x_103);
lean_dec(x_47);
if (x_104 == 0)
{
uint8_t x_105; 
x_105 = 1;
x_55 = x_105;
goto block_102;
}
else
{
uint8_t x_106; 
x_106 = 0;
x_55 = x_106;
goto block_102;
}
block_102:
{
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_46, 0);
lean_inc(x_56);
lean_dec(x_46);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l_Lean_Expr_const___override(x_57, x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_59 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_58, x_54, x_4, x_5, x_6, x_7, x_45);
lean_dec(x_54);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_n(x_2, 2);
lean_inc(x_1);
x_62 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2(x_1, x_2, x_3, x_2, x_48, x_2, x_52, x_60, x_4, x_5, x_6, x_7, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_65 = lean_whnf(x_63, x_4, x_5, x_6, x_7, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 7)
{
uint8_t x_67; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_65, 0);
lean_dec(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_expr_consume_type_annotations(x_69);
lean_ctor_set(x_65, 0, x_70);
return x_65;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
lean_dec(x_65);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_dec(x_66);
x_73 = lean_expr_consume_type_annotations(x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_66);
x_75 = lean_ctor_get(x_65, 1);
lean_inc(x_75);
lean_dec(x_65);
x_76 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_77 = l_Lean_indentExpr(x_76);
x_78 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_81, x_4, x_5, x_6, x_7, x_75);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_65);
if (x_83 == 0)
{
return x_65;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_65, 0);
x_85 = lean_ctor_get(x_65, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_65);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_62);
if (x_87 == 0)
{
return x_62;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_62, 0);
x_89 = lean_ctor_get(x_62, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_62);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_59);
if (x_91 == 0)
{
return x_59;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_59, 0);
x_93 = lean_ctor_get(x_59, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_59);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_54);
lean_dec(x_46);
lean_dec(x_17);
x_95 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_96 = l_Lean_indentExpr(x_95);
x_97 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_100, x_4, x_5, x_6, x_7, x_45);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_101;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_44);
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_13);
x_107 = lean_ctor_get(x_43, 1);
lean_inc(x_107);
lean_dec(x_43);
x_108 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_109 = l_Lean_indentExpr(x_108);
x_110 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
x_112 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_113, x_4, x_5, x_6, x_7, x_107);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_114;
}
}
else
{
uint8_t x_115; 
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_43);
if (x_115 == 0)
{
return x_43;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_43, 0);
x_117 = lean_ctor_get(x_43, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_43);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_41);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_13);
x_119 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_120 = l_Lean_indentExpr(x_119);
x_121 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
x_123 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_124, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_13);
x_126 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_127 = l_Lean_indentExpr(x_126);
x_128 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
x_130 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_131, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_132;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_30);
lean_dec(x_17);
lean_dec(x_13);
x_141 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_142 = l_Lean_indentExpr(x_141);
x_143 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_146, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_147;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_15);
lean_dec(x_13);
x_148 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_149 = l_Lean_indentExpr(x_148);
x_150 = l_Std_Range_forIn_loop___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__2___closed__2;
x_151 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
x_152 = l_Lean_Meta_throwFunctionExpected___rarg___closed__4;
x_153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_153, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_154;
}
}
else
{
uint8_t x_155; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_155 = !lean_is_exclusive(x_12);
if (x_155 == 0)
{
return x_12;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_12, 0);
x_157 = lean_ctor_get(x_12, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_12);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_9);
if (x_159 == 0)
{
return x_9;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_9, 0);
x_161 = lean_ctor_get(x_9, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_9);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
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
x_1 = lean_mk_string_from_bytes("type expected", 13);
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
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_40 = lean_ctor_get(x_9, 1);
x_41 = lean_ctor_get(x_9, 2);
x_42 = lean_ctor_get(x_9, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_9);
x_43 = lean_ctor_get(x_10, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_10, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_10, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_10, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_10, 5);
lean_inc(x_48);
x_49 = lean_ctor_get(x_10, 6);
lean_inc(x_49);
x_50 = lean_ctor_get(x_10, 7);
lean_inc(x_50);
x_51 = lean_ctor_get(x_10, 8);
lean_inc(x_51);
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
 x_52 = x_10;
} else {
 lean_dec_ref(x_10);
 x_52 = lean_box(0);
}
x_53 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_50, x_1, x_2);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 9, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_44);
lean_ctor_set(x_54, 2, x_45);
lean_ctor_set(x_54, 3, x_46);
lean_ctor_set(x_54, 4, x_47);
lean_ctor_set(x_54, 5, x_48);
lean_ctor_set(x_54, 6, x_49);
lean_ctor_set(x_54, 7, x_53);
lean_ctor_set(x_54, 8, x_51);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_40);
lean_ctor_set(x_55, 2, x_41);
lean_ctor_set(x_55, 3, x_42);
x_56 = lean_st_ref_set(x_4, x_55, x_11);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
x_59 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = 0;
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(x_9, x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg), 7, 0);
return x_2;
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
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1;
x_8 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg), 7, 0);
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
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1;
x_8 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
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
x_1 = lean_mk_string_from_bytes("unknown metavariable '?", 23);
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
x_1 = lean_mk_string_from_bytes("'", 1);
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
lean_inc(x_1);
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
lean_inc(x_1);
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
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_expr_equal(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_PersistentHashMap_findAtAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__3(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Expr_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_findAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__2(x_3, x_5, x_2);
lean_dec(x_2);
return x_6;
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Expr_hash(x_2);
x_8 = lean_uint64_to_usize(x_7);
x_9 = 1;
x_10 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5(x_5, x_8, x_9, x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_Expr_hash(x_2);
x_16 = lean_uint64_to_usize(x_15);
x_17 = 1;
x_18 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__5(x_13, x_16, x_17, x_2, x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_14, x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
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
lean_inc(x_1);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
x_37 = lean_ctor_get(x_23, 2);
x_38 = lean_ctor_get(x_23, 3);
x_39 = lean_ctor_get(x_23, 4);
x_40 = lean_ctor_get(x_23, 5);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
lean_inc(x_17);
x_41 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_35, x_1, x_17);
x_42 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_38);
lean_ctor_set(x_42, 4, x_39);
lean_ctor_set(x_42, 5, x_40);
lean_ctor_set(x_22, 1, x_42);
x_43 = lean_st_ref_set(x_4, x_22, x_24);
lean_dec(x_4);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_17);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 2);
x_49 = lean_ctor_get(x_22, 3);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
x_50 = lean_ctor_get(x_23, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_23, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_23, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_23, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_23, 4);
lean_inc(x_54);
x_55 = lean_ctor_get(x_23, 5);
lean_inc(x_55);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 lean_ctor_release(x_23, 5);
 x_56 = x_23;
} else {
 lean_dec_ref(x_23);
 x_56 = lean_box(0);
}
lean_inc(x_17);
x_57 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_50, x_1, x_17);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 6, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_51);
lean_ctor_set(x_58, 2, x_52);
lean_ctor_set(x_58, 3, x_53);
lean_ctor_set(x_58, 4, x_54);
lean_ctor_set(x_58, 5, x_55);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_47);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_48);
lean_ctor_set(x_59, 3, x_49);
x_60 = lean_st_ref_set(x_4, x_59, x_24);
lean_dec(x_4);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_17);
lean_ctor_set(x_63, 1, x_61);
return x_63;
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
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_15, 0);
x_65 = lean_ctor_get(x_15, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_15);
x_66 = l_Lean_Expr_hasMVar(x_1);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = l_Lean_Expr_hasMVar(x_64);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_68 = lean_st_ref_take(x_4, x_65);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_69, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 3);
lean_inc(x_74);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 lean_ctor_release(x_69, 2);
 lean_ctor_release(x_69, 3);
 x_75 = x_69;
} else {
 lean_dec_ref(x_69);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_70, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_70, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_70, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_70, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_70, 5);
lean_inc(x_81);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 lean_ctor_release(x_70, 2);
 lean_ctor_release(x_70, 3);
 lean_ctor_release(x_70, 4);
 lean_ctor_release(x_70, 5);
 x_82 = x_70;
} else {
 lean_dec_ref(x_70);
 x_82 = lean_box(0);
}
lean_inc(x_64);
x_83 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_76, x_1, x_64);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 6, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_77);
lean_ctor_set(x_84, 2, x_78);
lean_ctor_set(x_84, 3, x_79);
lean_ctor_set(x_84, 4, x_80);
lean_ctor_set(x_84, 5, x_81);
if (lean_is_scalar(x_75)) {
 x_85 = lean_alloc_ctor(0, 4, 0);
} else {
 x_85 = x_75;
}
lean_ctor_set(x_85, 0, x_72);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_73);
lean_ctor_set(x_85, 3, x_74);
x_86 = lean_st_ref_set(x_4, x_85, x_71);
lean_dec(x_4);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_64);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
else
{
lean_object* x_90; 
lean_dec(x_4);
lean_dec(x_1);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_64);
lean_ctor_set(x_90, 1, x_65);
return x_90;
}
}
else
{
lean_object* x_91; 
lean_dec(x_4);
lean_dec(x_1);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_64);
lean_ctor_set(x_91, 1, x_65);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_4);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_15);
if (x_92 == 0)
{
return x_15;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_15, 0);
x_94 = lean_ctor_get(x_15, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_15);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = lean_ctor_get(x_14, 0);
lean_inc(x_96);
lean_dec(x_14);
lean_ctor_set(x_8, 0, x_96);
return x_8;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_8, 0);
x_98 = lean_ctor_get(x_8, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_8);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec(x_99);
lean_inc(x_1);
x_101 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_100, x_1);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
lean_inc(x_4);
x_102 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_98);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
x_106 = l_Lean_Expr_hasMVar(x_1);
if (x_106 == 0)
{
uint8_t x_107; 
x_107 = l_Lean_Expr_hasMVar(x_103);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_105);
x_108 = lean_st_ref_take(x_4, x_104);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_109, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_109, 3);
lean_inc(x_114);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 lean_ctor_release(x_109, 2);
 lean_ctor_release(x_109, 3);
 x_115 = x_109;
} else {
 lean_dec_ref(x_109);
 x_115 = lean_box(0);
}
x_116 = lean_ctor_get(x_110, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_110, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_110, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_110, 4);
lean_inc(x_120);
x_121 = lean_ctor_get(x_110, 5);
lean_inc(x_121);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 lean_ctor_release(x_110, 3);
 lean_ctor_release(x_110, 4);
 lean_ctor_release(x_110, 5);
 x_122 = x_110;
} else {
 lean_dec_ref(x_110);
 x_122 = lean_box(0);
}
lean_inc(x_103);
x_123 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_116, x_1, x_103);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 6, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_117);
lean_ctor_set(x_124, 2, x_118);
lean_ctor_set(x_124, 3, x_119);
lean_ctor_set(x_124, 4, x_120);
lean_ctor_set(x_124, 5, x_121);
if (lean_is_scalar(x_115)) {
 x_125 = lean_alloc_ctor(0, 4, 0);
} else {
 x_125 = x_115;
}
lean_ctor_set(x_125, 0, x_112);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set(x_125, 2, x_113);
lean_ctor_set(x_125, 3, x_114);
x_126 = lean_st_ref_set(x_4, x_125, x_111);
lean_dec(x_4);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_128 = x_126;
} else {
 lean_dec_ref(x_126);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_103);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
else
{
lean_object* x_130; 
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_105)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_105;
}
lean_ctor_set(x_130, 0, x_103);
lean_ctor_set(x_130, 1, x_104);
return x_130;
}
}
else
{
lean_object* x_131; 
lean_dec(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_105)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_105;
}
lean_ctor_set(x_131, 0, x_103);
lean_ctor_set(x_131, 1, x_104);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_4);
lean_dec(x_1);
x_132 = lean_ctor_get(x_102, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_102, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_134 = x_102;
} else {
 lean_dec_ref(x_102);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = lean_ctor_get(x_101, 0);
lean_inc(x_136);
lean_dec(x_101);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_98);
return x_137;
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
x_1 = lean_mk_string_from_bytes("unexpected bound variable ", 26);
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
lean_inc(x_1);
x_34 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_33, x_1);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_free_object(x_28);
lean_inc(x_3);
x_35 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_27, x_23, x_2, x_3, x_4, x_5, x_31);
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
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_55 = lean_ctor_get(x_43, 0);
x_56 = lean_ctor_get(x_43, 1);
x_57 = lean_ctor_get(x_43, 2);
x_58 = lean_ctor_get(x_43, 3);
x_59 = lean_ctor_get(x_43, 4);
x_60 = lean_ctor_get(x_43, 5);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_43);
lean_inc(x_37);
x_61 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_55, x_1, x_37);
x_62 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
lean_ctor_set(x_62, 2, x_57);
lean_ctor_set(x_62, 3, x_58);
lean_ctor_set(x_62, 4, x_59);
lean_ctor_set(x_62, 5, x_60);
lean_ctor_set(x_42, 1, x_62);
x_63 = lean_st_ref_set(x_3, x_42, x_44);
lean_dec(x_3);
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
lean_ctor_set(x_66, 0, x_37);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_67 = lean_ctor_get(x_42, 0);
x_68 = lean_ctor_get(x_42, 2);
x_69 = lean_ctor_get(x_42, 3);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_42);
x_70 = lean_ctor_get(x_43, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_43, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_43, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_43, 3);
lean_inc(x_73);
x_74 = lean_ctor_get(x_43, 4);
lean_inc(x_74);
x_75 = lean_ctor_get(x_43, 5);
lean_inc(x_75);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 lean_ctor_release(x_43, 4);
 lean_ctor_release(x_43, 5);
 x_76 = x_43;
} else {
 lean_dec_ref(x_43);
 x_76 = lean_box(0);
}
lean_inc(x_37);
x_77 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_70, x_1, x_37);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 6, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_71);
lean_ctor_set(x_78, 2, x_72);
lean_ctor_set(x_78, 3, x_73);
lean_ctor_set(x_78, 4, x_74);
lean_ctor_set(x_78, 5, x_75);
x_79 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_79, 0, x_67);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_68);
lean_ctor_set(x_79, 3, x_69);
x_80 = lean_st_ref_set(x_3, x_79, x_44);
lean_dec(x_3);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_37);
lean_ctor_set(x_83, 1, x_81);
return x_83;
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
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_35, 0);
x_85 = lean_ctor_get(x_35, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_35);
x_86 = l_Lean_Expr_hasMVar(x_1);
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = l_Lean_Expr_hasMVar(x_84);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_88 = lean_st_ref_take(x_3, x_85);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_89, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_89, 3);
lean_inc(x_94);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 x_95 = x_89;
} else {
 lean_dec_ref(x_89);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_90, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_90, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_90, 3);
lean_inc(x_99);
x_100 = lean_ctor_get(x_90, 4);
lean_inc(x_100);
x_101 = lean_ctor_get(x_90, 5);
lean_inc(x_101);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 lean_ctor_release(x_90, 3);
 lean_ctor_release(x_90, 4);
 lean_ctor_release(x_90, 5);
 x_102 = x_90;
} else {
 lean_dec_ref(x_90);
 x_102 = lean_box(0);
}
lean_inc(x_84);
x_103 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_96, x_1, x_84);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 6, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_97);
lean_ctor_set(x_104, 2, x_98);
lean_ctor_set(x_104, 3, x_99);
lean_ctor_set(x_104, 4, x_100);
lean_ctor_set(x_104, 5, x_101);
if (lean_is_scalar(x_95)) {
 x_105 = lean_alloc_ctor(0, 4, 0);
} else {
 x_105 = x_95;
}
lean_ctor_set(x_105, 0, x_92);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_105, 2, x_93);
lean_ctor_set(x_105, 3, x_94);
x_106 = lean_st_ref_set(x_3, x_105, x_91);
lean_dec(x_3);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_84);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
else
{
lean_object* x_110; 
lean_dec(x_3);
lean_dec(x_1);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_84);
lean_ctor_set(x_110, 1, x_85);
return x_110;
}
}
else
{
lean_object* x_111; 
lean_dec(x_3);
lean_dec(x_1);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_84);
lean_ctor_set(x_111, 1, x_85);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_3);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_35);
if (x_112 == 0)
{
return x_35;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_35, 0);
x_114 = lean_ctor_get(x_35, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_35);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = lean_ctor_get(x_34, 0);
lean_inc(x_116);
lean_dec(x_34);
lean_ctor_set(x_28, 0, x_116);
return x_28;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_28, 0);
x_118 = lean_ctor_get(x_28, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_28);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec(x_119);
lean_inc(x_1);
x_121 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_120, x_1);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
lean_inc(x_3);
x_122 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_27, x_23, x_2, x_3, x_4, x_5, x_118);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
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
x_126 = l_Lean_Expr_hasMVar(x_1);
if (x_126 == 0)
{
uint8_t x_127; 
x_127 = l_Lean_Expr_hasMVar(x_123);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_125);
x_128 = lean_st_ref_take(x_3, x_124);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_129, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_129, 3);
lean_inc(x_134);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 lean_ctor_release(x_129, 2);
 lean_ctor_release(x_129, 3);
 x_135 = x_129;
} else {
 lean_dec_ref(x_129);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_130, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_130, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_130, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_130, 3);
lean_inc(x_139);
x_140 = lean_ctor_get(x_130, 4);
lean_inc(x_140);
x_141 = lean_ctor_get(x_130, 5);
lean_inc(x_141);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 lean_ctor_release(x_130, 3);
 lean_ctor_release(x_130, 4);
 lean_ctor_release(x_130, 5);
 x_142 = x_130;
} else {
 lean_dec_ref(x_130);
 x_142 = lean_box(0);
}
lean_inc(x_123);
x_143 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_136, x_1, x_123);
if (lean_is_scalar(x_142)) {
 x_144 = lean_alloc_ctor(0, 6, 0);
} else {
 x_144 = x_142;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_137);
lean_ctor_set(x_144, 2, x_138);
lean_ctor_set(x_144, 3, x_139);
lean_ctor_set(x_144, 4, x_140);
lean_ctor_set(x_144, 5, x_141);
if (lean_is_scalar(x_135)) {
 x_145 = lean_alloc_ctor(0, 4, 0);
} else {
 x_145 = x_135;
}
lean_ctor_set(x_145, 0, x_132);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set(x_145, 2, x_133);
lean_ctor_set(x_145, 3, x_134);
x_146 = lean_st_ref_set(x_3, x_145, x_131);
lean_dec(x_3);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_123);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
else
{
lean_object* x_150; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_125)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_125;
}
lean_ctor_set(x_150, 0, x_123);
lean_ctor_set(x_150, 1, x_124);
return x_150;
}
}
else
{
lean_object* x_151; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_125)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_125;
}
lean_ctor_set(x_151, 0, x_123);
lean_ctor_set(x_151, 1, x_124);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_3);
lean_dec(x_1);
x_152 = lean_ctor_get(x_122, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_122, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_154 = x_122;
} else {
 lean_dec_ref(x_122);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = lean_ctor_get(x_121, 0);
lean_inc(x_156);
lean_dec(x_121);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_118);
return x_157;
}
}
}
}
case 5:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_158 = lean_ctor_get(x_1, 0);
lean_inc(x_158);
x_159 = l_Lean_Expr_getAppFn(x_158);
lean_dec(x_158);
x_160 = lean_unsigned_to_nat(0u);
x_161 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_160);
x_162 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__1;
lean_inc(x_161);
x_163 = lean_mk_array(x_161, x_162);
x_164 = lean_unsigned_to_nat(1u);
x_165 = lean_nat_sub(x_161, x_164);
lean_dec(x_161);
lean_inc(x_1);
x_166 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_163, x_165);
x_167 = lean_st_ref_get(x_3, x_6);
x_168 = !lean_is_exclusive(x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_ctor_get(x_167, 0);
x_170 = lean_ctor_get(x_167, 1);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec(x_171);
lean_inc(x_1);
x_173 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_172, x_1);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; 
lean_free_object(x_167);
lean_inc(x_3);
x_174 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_159, x_166, x_2, x_3, x_4, x_5, x_170);
lean_dec(x_166);
if (lean_obj_tag(x_174) == 0)
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = lean_ctor_get(x_174, 0);
x_177 = lean_ctor_get(x_174, 1);
x_178 = l_Lean_Expr_hasMVar(x_1);
if (x_178 == 0)
{
uint8_t x_179; 
x_179 = l_Lean_Expr_hasMVar(x_176);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_free_object(x_174);
x_180 = lean_st_ref_take(x_3, x_177);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_dec(x_180);
x_184 = !lean_is_exclusive(x_181);
if (x_184 == 0)
{
lean_object* x_185; uint8_t x_186; 
x_185 = lean_ctor_get(x_181, 1);
lean_dec(x_185);
x_186 = !lean_is_exclusive(x_182);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_187 = lean_ctor_get(x_182, 0);
lean_inc(x_176);
x_188 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_187, x_1, x_176);
lean_ctor_set(x_182, 0, x_188);
x_189 = lean_st_ref_set(x_3, x_181, x_183);
lean_dec(x_3);
x_190 = !lean_is_exclusive(x_189);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_189, 0);
lean_dec(x_191);
lean_ctor_set(x_189, 0, x_176);
return x_189;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
lean_dec(x_189);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_176);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_194 = lean_ctor_get(x_182, 0);
x_195 = lean_ctor_get(x_182, 1);
x_196 = lean_ctor_get(x_182, 2);
x_197 = lean_ctor_get(x_182, 3);
x_198 = lean_ctor_get(x_182, 4);
x_199 = lean_ctor_get(x_182, 5);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_182);
lean_inc(x_176);
x_200 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_194, x_1, x_176);
x_201 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_195);
lean_ctor_set(x_201, 2, x_196);
lean_ctor_set(x_201, 3, x_197);
lean_ctor_set(x_201, 4, x_198);
lean_ctor_set(x_201, 5, x_199);
lean_ctor_set(x_181, 1, x_201);
x_202 = lean_st_ref_set(x_3, x_181, x_183);
lean_dec(x_3);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_204 = x_202;
} else {
 lean_dec_ref(x_202);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_176);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_206 = lean_ctor_get(x_181, 0);
x_207 = lean_ctor_get(x_181, 2);
x_208 = lean_ctor_get(x_181, 3);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_181);
x_209 = lean_ctor_get(x_182, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_182, 1);
lean_inc(x_210);
x_211 = lean_ctor_get(x_182, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_182, 3);
lean_inc(x_212);
x_213 = lean_ctor_get(x_182, 4);
lean_inc(x_213);
x_214 = lean_ctor_get(x_182, 5);
lean_inc(x_214);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 lean_ctor_release(x_182, 2);
 lean_ctor_release(x_182, 3);
 lean_ctor_release(x_182, 4);
 lean_ctor_release(x_182, 5);
 x_215 = x_182;
} else {
 lean_dec_ref(x_182);
 x_215 = lean_box(0);
}
lean_inc(x_176);
x_216 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_209, x_1, x_176);
if (lean_is_scalar(x_215)) {
 x_217 = lean_alloc_ctor(0, 6, 0);
} else {
 x_217 = x_215;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_210);
lean_ctor_set(x_217, 2, x_211);
lean_ctor_set(x_217, 3, x_212);
lean_ctor_set(x_217, 4, x_213);
lean_ctor_set(x_217, 5, x_214);
x_218 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_218, 0, x_206);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set(x_218, 2, x_207);
lean_ctor_set(x_218, 3, x_208);
x_219 = lean_st_ref_set(x_3, x_218, x_183);
lean_dec(x_3);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_221 = x_219;
} else {
 lean_dec_ref(x_219);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_176);
lean_ctor_set(x_222, 1, x_220);
return x_222;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_174;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_174;
}
}
else
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_223 = lean_ctor_get(x_174, 0);
x_224 = lean_ctor_get(x_174, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_174);
x_225 = l_Lean_Expr_hasMVar(x_1);
if (x_225 == 0)
{
uint8_t x_226; 
x_226 = l_Lean_Expr_hasMVar(x_223);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_227 = lean_st_ref_take(x_3, x_224);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
lean_dec(x_227);
x_231 = lean_ctor_get(x_228, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_228, 2);
lean_inc(x_232);
x_233 = lean_ctor_get(x_228, 3);
lean_inc(x_233);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 lean_ctor_release(x_228, 2);
 lean_ctor_release(x_228, 3);
 x_234 = x_228;
} else {
 lean_dec_ref(x_228);
 x_234 = lean_box(0);
}
x_235 = lean_ctor_get(x_229, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_229, 1);
lean_inc(x_236);
x_237 = lean_ctor_get(x_229, 2);
lean_inc(x_237);
x_238 = lean_ctor_get(x_229, 3);
lean_inc(x_238);
x_239 = lean_ctor_get(x_229, 4);
lean_inc(x_239);
x_240 = lean_ctor_get(x_229, 5);
lean_inc(x_240);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 lean_ctor_release(x_229, 2);
 lean_ctor_release(x_229, 3);
 lean_ctor_release(x_229, 4);
 lean_ctor_release(x_229, 5);
 x_241 = x_229;
} else {
 lean_dec_ref(x_229);
 x_241 = lean_box(0);
}
lean_inc(x_223);
x_242 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_235, x_1, x_223);
if (lean_is_scalar(x_241)) {
 x_243 = lean_alloc_ctor(0, 6, 0);
} else {
 x_243 = x_241;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_236);
lean_ctor_set(x_243, 2, x_237);
lean_ctor_set(x_243, 3, x_238);
lean_ctor_set(x_243, 4, x_239);
lean_ctor_set(x_243, 5, x_240);
if (lean_is_scalar(x_234)) {
 x_244 = lean_alloc_ctor(0, 4, 0);
} else {
 x_244 = x_234;
}
lean_ctor_set(x_244, 0, x_231);
lean_ctor_set(x_244, 1, x_243);
lean_ctor_set(x_244, 2, x_232);
lean_ctor_set(x_244, 3, x_233);
x_245 = lean_st_ref_set(x_3, x_244, x_230);
lean_dec(x_3);
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_247 = x_245;
} else {
 lean_dec_ref(x_245);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_223);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
else
{
lean_object* x_249; 
lean_dec(x_3);
lean_dec(x_1);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_223);
lean_ctor_set(x_249, 1, x_224);
return x_249;
}
}
else
{
lean_object* x_250; 
lean_dec(x_3);
lean_dec(x_1);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_223);
lean_ctor_set(x_250, 1, x_224);
return x_250;
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_3);
lean_dec(x_1);
x_251 = !lean_is_exclusive(x_174);
if (x_251 == 0)
{
return x_174;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_174, 0);
x_253 = lean_ctor_get(x_174, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_174);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
else
{
lean_object* x_255; 
lean_dec(x_166);
lean_dec(x_159);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_255 = lean_ctor_get(x_173, 0);
lean_inc(x_255);
lean_dec(x_173);
lean_ctor_set(x_167, 0, x_255);
return x_167;
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_256 = lean_ctor_get(x_167, 0);
x_257 = lean_ctor_get(x_167, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_167);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_dec(x_258);
lean_inc(x_1);
x_260 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_259, x_1);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; 
lean_inc(x_3);
x_261 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_159, x_166, x_2, x_3, x_4, x_5, x_257);
lean_dec(x_166);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_264 = x_261;
} else {
 lean_dec_ref(x_261);
 x_264 = lean_box(0);
}
x_265 = l_Lean_Expr_hasMVar(x_1);
if (x_265 == 0)
{
uint8_t x_266; 
x_266 = l_Lean_Expr_hasMVar(x_262);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_264);
x_267 = lean_st_ref_take(x_3, x_263);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
x_270 = lean_ctor_get(x_267, 1);
lean_inc(x_270);
lean_dec(x_267);
x_271 = lean_ctor_get(x_268, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_268, 2);
lean_inc(x_272);
x_273 = lean_ctor_get(x_268, 3);
lean_inc(x_273);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 lean_ctor_release(x_268, 2);
 lean_ctor_release(x_268, 3);
 x_274 = x_268;
} else {
 lean_dec_ref(x_268);
 x_274 = lean_box(0);
}
x_275 = lean_ctor_get(x_269, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_269, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_269, 2);
lean_inc(x_277);
x_278 = lean_ctor_get(x_269, 3);
lean_inc(x_278);
x_279 = lean_ctor_get(x_269, 4);
lean_inc(x_279);
x_280 = lean_ctor_get(x_269, 5);
lean_inc(x_280);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 lean_ctor_release(x_269, 2);
 lean_ctor_release(x_269, 3);
 lean_ctor_release(x_269, 4);
 lean_ctor_release(x_269, 5);
 x_281 = x_269;
} else {
 lean_dec_ref(x_269);
 x_281 = lean_box(0);
}
lean_inc(x_262);
x_282 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_275, x_1, x_262);
if (lean_is_scalar(x_281)) {
 x_283 = lean_alloc_ctor(0, 6, 0);
} else {
 x_283 = x_281;
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_276);
lean_ctor_set(x_283, 2, x_277);
lean_ctor_set(x_283, 3, x_278);
lean_ctor_set(x_283, 4, x_279);
lean_ctor_set(x_283, 5, x_280);
if (lean_is_scalar(x_274)) {
 x_284 = lean_alloc_ctor(0, 4, 0);
} else {
 x_284 = x_274;
}
lean_ctor_set(x_284, 0, x_271);
lean_ctor_set(x_284, 1, x_283);
lean_ctor_set(x_284, 2, x_272);
lean_ctor_set(x_284, 3, x_273);
x_285 = lean_st_ref_set(x_3, x_284, x_270);
lean_dec(x_3);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_287 = x_285;
} else {
 lean_dec_ref(x_285);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_262);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
else
{
lean_object* x_289; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_264)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_264;
}
lean_ctor_set(x_289, 0, x_262);
lean_ctor_set(x_289, 1, x_263);
return x_289;
}
}
else
{
lean_object* x_290; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_264)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_264;
}
lean_ctor_set(x_290, 0, x_262);
lean_ctor_set(x_290, 1, x_263);
return x_290;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_3);
lean_dec(x_1);
x_291 = lean_ctor_get(x_261, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_261, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_293 = x_261;
} else {
 lean_dec_ref(x_261);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_166);
lean_dec(x_159);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_295 = lean_ctor_get(x_260, 0);
lean_inc(x_295);
lean_dec(x_260);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_257);
return x_296;
}
}
}
case 7:
{
lean_object* x_297; uint8_t x_298; 
x_297 = lean_st_ref_get(x_3, x_6);
x_298 = !lean_is_exclusive(x_297);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_299 = lean_ctor_get(x_297, 0);
x_300 = lean_ctor_get(x_297, 1);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
lean_dec(x_301);
lean_inc(x_1);
x_303 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_302, x_1);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; 
lean_free_object(x_297);
x_304 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1;
lean_inc(x_3);
lean_inc(x_1);
x_305 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_1, x_304, x_2, x_3, x_4, x_5, x_300);
if (lean_obj_tag(x_305) == 0)
{
uint8_t x_306; 
x_306 = !lean_is_exclusive(x_305);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_307 = lean_ctor_get(x_305, 0);
x_308 = lean_ctor_get(x_305, 1);
x_309 = l_Lean_Expr_hasMVar(x_1);
if (x_309 == 0)
{
uint8_t x_310; 
x_310 = l_Lean_Expr_hasMVar(x_307);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
lean_free_object(x_305);
x_311 = lean_st_ref_take(x_3, x_308);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
x_314 = lean_ctor_get(x_311, 1);
lean_inc(x_314);
lean_dec(x_311);
x_315 = !lean_is_exclusive(x_312);
if (x_315 == 0)
{
lean_object* x_316; uint8_t x_317; 
x_316 = lean_ctor_get(x_312, 1);
lean_dec(x_316);
x_317 = !lean_is_exclusive(x_313);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; 
x_318 = lean_ctor_get(x_313, 0);
lean_inc(x_307);
x_319 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_318, x_1, x_307);
lean_ctor_set(x_313, 0, x_319);
x_320 = lean_st_ref_set(x_3, x_312, x_314);
lean_dec(x_3);
x_321 = !lean_is_exclusive(x_320);
if (x_321 == 0)
{
lean_object* x_322; 
x_322 = lean_ctor_get(x_320, 0);
lean_dec(x_322);
lean_ctor_set(x_320, 0, x_307);
return x_320;
}
else
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_ctor_get(x_320, 1);
lean_inc(x_323);
lean_dec(x_320);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_307);
lean_ctor_set(x_324, 1, x_323);
return x_324;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_325 = lean_ctor_get(x_313, 0);
x_326 = lean_ctor_get(x_313, 1);
x_327 = lean_ctor_get(x_313, 2);
x_328 = lean_ctor_get(x_313, 3);
x_329 = lean_ctor_get(x_313, 4);
x_330 = lean_ctor_get(x_313, 5);
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_313);
lean_inc(x_307);
x_331 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_325, x_1, x_307);
x_332 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_326);
lean_ctor_set(x_332, 2, x_327);
lean_ctor_set(x_332, 3, x_328);
lean_ctor_set(x_332, 4, x_329);
lean_ctor_set(x_332, 5, x_330);
lean_ctor_set(x_312, 1, x_332);
x_333 = lean_st_ref_set(x_3, x_312, x_314);
lean_dec(x_3);
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_335 = x_333;
} else {
 lean_dec_ref(x_333);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_307);
lean_ctor_set(x_336, 1, x_334);
return x_336;
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_337 = lean_ctor_get(x_312, 0);
x_338 = lean_ctor_get(x_312, 2);
x_339 = lean_ctor_get(x_312, 3);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_312);
x_340 = lean_ctor_get(x_313, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_313, 1);
lean_inc(x_341);
x_342 = lean_ctor_get(x_313, 2);
lean_inc(x_342);
x_343 = lean_ctor_get(x_313, 3);
lean_inc(x_343);
x_344 = lean_ctor_get(x_313, 4);
lean_inc(x_344);
x_345 = lean_ctor_get(x_313, 5);
lean_inc(x_345);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 lean_ctor_release(x_313, 2);
 lean_ctor_release(x_313, 3);
 lean_ctor_release(x_313, 4);
 lean_ctor_release(x_313, 5);
 x_346 = x_313;
} else {
 lean_dec_ref(x_313);
 x_346 = lean_box(0);
}
lean_inc(x_307);
x_347 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_340, x_1, x_307);
if (lean_is_scalar(x_346)) {
 x_348 = lean_alloc_ctor(0, 6, 0);
} else {
 x_348 = x_346;
}
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_341);
lean_ctor_set(x_348, 2, x_342);
lean_ctor_set(x_348, 3, x_343);
lean_ctor_set(x_348, 4, x_344);
lean_ctor_set(x_348, 5, x_345);
x_349 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_349, 0, x_337);
lean_ctor_set(x_349, 1, x_348);
lean_ctor_set(x_349, 2, x_338);
lean_ctor_set(x_349, 3, x_339);
x_350 = lean_st_ref_set(x_3, x_349, x_314);
lean_dec(x_3);
x_351 = lean_ctor_get(x_350, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_352 = x_350;
} else {
 lean_dec_ref(x_350);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_307);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_305;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_305;
}
}
else
{
lean_object* x_354; lean_object* x_355; uint8_t x_356; 
x_354 = lean_ctor_get(x_305, 0);
x_355 = lean_ctor_get(x_305, 1);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_305);
x_356 = l_Lean_Expr_hasMVar(x_1);
if (x_356 == 0)
{
uint8_t x_357; 
x_357 = l_Lean_Expr_hasMVar(x_354);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_358 = lean_st_ref_take(x_3, x_355);
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_359, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_358, 1);
lean_inc(x_361);
lean_dec(x_358);
x_362 = lean_ctor_get(x_359, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_359, 2);
lean_inc(x_363);
x_364 = lean_ctor_get(x_359, 3);
lean_inc(x_364);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 lean_ctor_release(x_359, 2);
 lean_ctor_release(x_359, 3);
 x_365 = x_359;
} else {
 lean_dec_ref(x_359);
 x_365 = lean_box(0);
}
x_366 = lean_ctor_get(x_360, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_360, 1);
lean_inc(x_367);
x_368 = lean_ctor_get(x_360, 2);
lean_inc(x_368);
x_369 = lean_ctor_get(x_360, 3);
lean_inc(x_369);
x_370 = lean_ctor_get(x_360, 4);
lean_inc(x_370);
x_371 = lean_ctor_get(x_360, 5);
lean_inc(x_371);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 lean_ctor_release(x_360, 2);
 lean_ctor_release(x_360, 3);
 lean_ctor_release(x_360, 4);
 lean_ctor_release(x_360, 5);
 x_372 = x_360;
} else {
 lean_dec_ref(x_360);
 x_372 = lean_box(0);
}
lean_inc(x_354);
x_373 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_366, x_1, x_354);
if (lean_is_scalar(x_372)) {
 x_374 = lean_alloc_ctor(0, 6, 0);
} else {
 x_374 = x_372;
}
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_367);
lean_ctor_set(x_374, 2, x_368);
lean_ctor_set(x_374, 3, x_369);
lean_ctor_set(x_374, 4, x_370);
lean_ctor_set(x_374, 5, x_371);
if (lean_is_scalar(x_365)) {
 x_375 = lean_alloc_ctor(0, 4, 0);
} else {
 x_375 = x_365;
}
lean_ctor_set(x_375, 0, x_362);
lean_ctor_set(x_375, 1, x_374);
lean_ctor_set(x_375, 2, x_363);
lean_ctor_set(x_375, 3, x_364);
x_376 = lean_st_ref_set(x_3, x_375, x_361);
lean_dec(x_3);
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_378 = x_376;
} else {
 lean_dec_ref(x_376);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_354);
lean_ctor_set(x_379, 1, x_377);
return x_379;
}
else
{
lean_object* x_380; 
lean_dec(x_3);
lean_dec(x_1);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_354);
lean_ctor_set(x_380, 1, x_355);
return x_380;
}
}
else
{
lean_object* x_381; 
lean_dec(x_3);
lean_dec(x_1);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_354);
lean_ctor_set(x_381, 1, x_355);
return x_381;
}
}
}
else
{
uint8_t x_382; 
lean_dec(x_3);
lean_dec(x_1);
x_382 = !lean_is_exclusive(x_305);
if (x_382 == 0)
{
return x_305;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_305, 0);
x_384 = lean_ctor_get(x_305, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_305);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
return x_385;
}
}
}
else
{
lean_object* x_386; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_386 = lean_ctor_get(x_303, 0);
lean_inc(x_386);
lean_dec(x_303);
lean_ctor_set(x_297, 0, x_386);
return x_297;
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_387 = lean_ctor_get(x_297, 0);
x_388 = lean_ctor_get(x_297, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_297);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec(x_387);
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
lean_dec(x_389);
lean_inc(x_1);
x_391 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_390, x_1);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; 
x_392 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___closed__1;
lean_inc(x_3);
lean_inc(x_1);
x_393 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_1, x_392, x_2, x_3, x_4, x_5, x_388);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_396 = x_393;
} else {
 lean_dec_ref(x_393);
 x_396 = lean_box(0);
}
x_397 = l_Lean_Expr_hasMVar(x_1);
if (x_397 == 0)
{
uint8_t x_398; 
x_398 = l_Lean_Expr_hasMVar(x_394);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec(x_396);
x_399 = lean_st_ref_take(x_3, x_395);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_400, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_399, 1);
lean_inc(x_402);
lean_dec(x_399);
x_403 = lean_ctor_get(x_400, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_400, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_400, 3);
lean_inc(x_405);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 lean_ctor_release(x_400, 2);
 lean_ctor_release(x_400, 3);
 x_406 = x_400;
} else {
 lean_dec_ref(x_400);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_401, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_401, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_401, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_401, 3);
lean_inc(x_410);
x_411 = lean_ctor_get(x_401, 4);
lean_inc(x_411);
x_412 = lean_ctor_get(x_401, 5);
lean_inc(x_412);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 lean_ctor_release(x_401, 2);
 lean_ctor_release(x_401, 3);
 lean_ctor_release(x_401, 4);
 lean_ctor_release(x_401, 5);
 x_413 = x_401;
} else {
 lean_dec_ref(x_401);
 x_413 = lean_box(0);
}
lean_inc(x_394);
x_414 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_407, x_1, x_394);
if (lean_is_scalar(x_413)) {
 x_415 = lean_alloc_ctor(0, 6, 0);
} else {
 x_415 = x_413;
}
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_408);
lean_ctor_set(x_415, 2, x_409);
lean_ctor_set(x_415, 3, x_410);
lean_ctor_set(x_415, 4, x_411);
lean_ctor_set(x_415, 5, x_412);
if (lean_is_scalar(x_406)) {
 x_416 = lean_alloc_ctor(0, 4, 0);
} else {
 x_416 = x_406;
}
lean_ctor_set(x_416, 0, x_403);
lean_ctor_set(x_416, 1, x_415);
lean_ctor_set(x_416, 2, x_404);
lean_ctor_set(x_416, 3, x_405);
x_417 = lean_st_ref_set(x_3, x_416, x_402);
lean_dec(x_3);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 x_419 = x_417;
} else {
 lean_dec_ref(x_417);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(0, 2, 0);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_394);
lean_ctor_set(x_420, 1, x_418);
return x_420;
}
else
{
lean_object* x_421; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_396)) {
 x_421 = lean_alloc_ctor(0, 2, 0);
} else {
 x_421 = x_396;
}
lean_ctor_set(x_421, 0, x_394);
lean_ctor_set(x_421, 1, x_395);
return x_421;
}
}
else
{
lean_object* x_422; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_396)) {
 x_422 = lean_alloc_ctor(0, 2, 0);
} else {
 x_422 = x_396;
}
lean_ctor_set(x_422, 0, x_394);
lean_ctor_set(x_422, 1, x_395);
return x_422;
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_3);
lean_dec(x_1);
x_423 = lean_ctor_get(x_393, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_393, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_425 = x_393;
} else {
 lean_dec_ref(x_393);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(1, 2, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_423);
lean_ctor_set(x_426, 1, x_424);
return x_426;
}
}
else
{
lean_object* x_427; lean_object* x_428; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_427 = lean_ctor_get(x_391, 0);
lean_inc(x_427);
lean_dec(x_391);
x_428 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_388);
return x_428;
}
}
}
case 9:
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_429 = lean_ctor_get(x_1, 0);
lean_inc(x_429);
lean_dec(x_1);
x_430 = l_Lean_Literal_type(x_429);
lean_dec(x_429);
x_431 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_6);
return x_431;
}
case 10:
{
lean_object* x_432; 
x_432 = lean_ctor_get(x_1, 1);
lean_inc(x_432);
lean_dec(x_1);
x_1 = x_432;
goto _start;
}
case 11:
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; 
x_434 = lean_ctor_get(x_1, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_1, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_1, 2);
lean_inc(x_436);
x_437 = lean_st_ref_get(x_3, x_6);
x_438 = !lean_is_exclusive(x_437);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_439 = lean_ctor_get(x_437, 0);
x_440 = lean_ctor_get(x_437, 1);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
lean_dec(x_441);
lean_inc(x_1);
x_443 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_442, x_1);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; 
lean_free_object(x_437);
lean_inc(x_3);
x_444 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(x_434, x_435, x_436, x_2, x_3, x_4, x_5, x_440);
if (lean_obj_tag(x_444) == 0)
{
uint8_t x_445; 
x_445 = !lean_is_exclusive(x_444);
if (x_445 == 0)
{
lean_object* x_446; lean_object* x_447; uint8_t x_448; 
x_446 = lean_ctor_get(x_444, 0);
x_447 = lean_ctor_get(x_444, 1);
x_448 = l_Lean_Expr_hasMVar(x_1);
if (x_448 == 0)
{
uint8_t x_449; 
x_449 = l_Lean_Expr_hasMVar(x_446);
if (x_449 == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; 
lean_free_object(x_444);
x_450 = lean_st_ref_take(x_3, x_447);
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_451, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_450, 1);
lean_inc(x_453);
lean_dec(x_450);
x_454 = !lean_is_exclusive(x_451);
if (x_454 == 0)
{
lean_object* x_455; uint8_t x_456; 
x_455 = lean_ctor_get(x_451, 1);
lean_dec(x_455);
x_456 = !lean_is_exclusive(x_452);
if (x_456 == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; uint8_t x_460; 
x_457 = lean_ctor_get(x_452, 0);
lean_inc(x_446);
x_458 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_457, x_1, x_446);
lean_ctor_set(x_452, 0, x_458);
x_459 = lean_st_ref_set(x_3, x_451, x_453);
lean_dec(x_3);
x_460 = !lean_is_exclusive(x_459);
if (x_460 == 0)
{
lean_object* x_461; 
x_461 = lean_ctor_get(x_459, 0);
lean_dec(x_461);
lean_ctor_set(x_459, 0, x_446);
return x_459;
}
else
{
lean_object* x_462; lean_object* x_463; 
x_462 = lean_ctor_get(x_459, 1);
lean_inc(x_462);
lean_dec(x_459);
x_463 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_463, 0, x_446);
lean_ctor_set(x_463, 1, x_462);
return x_463;
}
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_464 = lean_ctor_get(x_452, 0);
x_465 = lean_ctor_get(x_452, 1);
x_466 = lean_ctor_get(x_452, 2);
x_467 = lean_ctor_get(x_452, 3);
x_468 = lean_ctor_get(x_452, 4);
x_469 = lean_ctor_get(x_452, 5);
lean_inc(x_469);
lean_inc(x_468);
lean_inc(x_467);
lean_inc(x_466);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_452);
lean_inc(x_446);
x_470 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_464, x_1, x_446);
x_471 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_471, 0, x_470);
lean_ctor_set(x_471, 1, x_465);
lean_ctor_set(x_471, 2, x_466);
lean_ctor_set(x_471, 3, x_467);
lean_ctor_set(x_471, 4, x_468);
lean_ctor_set(x_471, 5, x_469);
lean_ctor_set(x_451, 1, x_471);
x_472 = lean_st_ref_set(x_3, x_451, x_453);
lean_dec(x_3);
x_473 = lean_ctor_get(x_472, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_474 = x_472;
} else {
 lean_dec_ref(x_472);
 x_474 = lean_box(0);
}
if (lean_is_scalar(x_474)) {
 x_475 = lean_alloc_ctor(0, 2, 0);
} else {
 x_475 = x_474;
}
lean_ctor_set(x_475, 0, x_446);
lean_ctor_set(x_475, 1, x_473);
return x_475;
}
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_476 = lean_ctor_get(x_451, 0);
x_477 = lean_ctor_get(x_451, 2);
x_478 = lean_ctor_get(x_451, 3);
lean_inc(x_478);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_451);
x_479 = lean_ctor_get(x_452, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_452, 1);
lean_inc(x_480);
x_481 = lean_ctor_get(x_452, 2);
lean_inc(x_481);
x_482 = lean_ctor_get(x_452, 3);
lean_inc(x_482);
x_483 = lean_ctor_get(x_452, 4);
lean_inc(x_483);
x_484 = lean_ctor_get(x_452, 5);
lean_inc(x_484);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 lean_ctor_release(x_452, 2);
 lean_ctor_release(x_452, 3);
 lean_ctor_release(x_452, 4);
 lean_ctor_release(x_452, 5);
 x_485 = x_452;
} else {
 lean_dec_ref(x_452);
 x_485 = lean_box(0);
}
lean_inc(x_446);
x_486 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_479, x_1, x_446);
if (lean_is_scalar(x_485)) {
 x_487 = lean_alloc_ctor(0, 6, 0);
} else {
 x_487 = x_485;
}
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_480);
lean_ctor_set(x_487, 2, x_481);
lean_ctor_set(x_487, 3, x_482);
lean_ctor_set(x_487, 4, x_483);
lean_ctor_set(x_487, 5, x_484);
x_488 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_488, 0, x_476);
lean_ctor_set(x_488, 1, x_487);
lean_ctor_set(x_488, 2, x_477);
lean_ctor_set(x_488, 3, x_478);
x_489 = lean_st_ref_set(x_3, x_488, x_453);
lean_dec(x_3);
x_490 = lean_ctor_get(x_489, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 lean_ctor_release(x_489, 1);
 x_491 = x_489;
} else {
 lean_dec_ref(x_489);
 x_491 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_492 = lean_alloc_ctor(0, 2, 0);
} else {
 x_492 = x_491;
}
lean_ctor_set(x_492, 0, x_446);
lean_ctor_set(x_492, 1, x_490);
return x_492;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_444;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_444;
}
}
else
{
lean_object* x_493; lean_object* x_494; uint8_t x_495; 
x_493 = lean_ctor_get(x_444, 0);
x_494 = lean_ctor_get(x_444, 1);
lean_inc(x_494);
lean_inc(x_493);
lean_dec(x_444);
x_495 = l_Lean_Expr_hasMVar(x_1);
if (x_495 == 0)
{
uint8_t x_496; 
x_496 = l_Lean_Expr_hasMVar(x_493);
if (x_496 == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_497 = lean_st_ref_take(x_3, x_494);
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_498, 1);
lean_inc(x_499);
x_500 = lean_ctor_get(x_497, 1);
lean_inc(x_500);
lean_dec(x_497);
x_501 = lean_ctor_get(x_498, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_498, 2);
lean_inc(x_502);
x_503 = lean_ctor_get(x_498, 3);
lean_inc(x_503);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 lean_ctor_release(x_498, 2);
 lean_ctor_release(x_498, 3);
 x_504 = x_498;
} else {
 lean_dec_ref(x_498);
 x_504 = lean_box(0);
}
x_505 = lean_ctor_get(x_499, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_499, 1);
lean_inc(x_506);
x_507 = lean_ctor_get(x_499, 2);
lean_inc(x_507);
x_508 = lean_ctor_get(x_499, 3);
lean_inc(x_508);
x_509 = lean_ctor_get(x_499, 4);
lean_inc(x_509);
x_510 = lean_ctor_get(x_499, 5);
lean_inc(x_510);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 lean_ctor_release(x_499, 2);
 lean_ctor_release(x_499, 3);
 lean_ctor_release(x_499, 4);
 lean_ctor_release(x_499, 5);
 x_511 = x_499;
} else {
 lean_dec_ref(x_499);
 x_511 = lean_box(0);
}
lean_inc(x_493);
x_512 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_505, x_1, x_493);
if (lean_is_scalar(x_511)) {
 x_513 = lean_alloc_ctor(0, 6, 0);
} else {
 x_513 = x_511;
}
lean_ctor_set(x_513, 0, x_512);
lean_ctor_set(x_513, 1, x_506);
lean_ctor_set(x_513, 2, x_507);
lean_ctor_set(x_513, 3, x_508);
lean_ctor_set(x_513, 4, x_509);
lean_ctor_set(x_513, 5, x_510);
if (lean_is_scalar(x_504)) {
 x_514 = lean_alloc_ctor(0, 4, 0);
} else {
 x_514 = x_504;
}
lean_ctor_set(x_514, 0, x_501);
lean_ctor_set(x_514, 1, x_513);
lean_ctor_set(x_514, 2, x_502);
lean_ctor_set(x_514, 3, x_503);
x_515 = lean_st_ref_set(x_3, x_514, x_500);
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
lean_ctor_set(x_518, 0, x_493);
lean_ctor_set(x_518, 1, x_516);
return x_518;
}
else
{
lean_object* x_519; 
lean_dec(x_3);
lean_dec(x_1);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_493);
lean_ctor_set(x_519, 1, x_494);
return x_519;
}
}
else
{
lean_object* x_520; 
lean_dec(x_3);
lean_dec(x_1);
x_520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_520, 0, x_493);
lean_ctor_set(x_520, 1, x_494);
return x_520;
}
}
}
else
{
uint8_t x_521; 
lean_dec(x_3);
lean_dec(x_1);
x_521 = !lean_is_exclusive(x_444);
if (x_521 == 0)
{
return x_444;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_522 = lean_ctor_get(x_444, 0);
x_523 = lean_ctor_get(x_444, 1);
lean_inc(x_523);
lean_inc(x_522);
lean_dec(x_444);
x_524 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_524, 0, x_522);
lean_ctor_set(x_524, 1, x_523);
return x_524;
}
}
}
else
{
lean_object* x_525; 
lean_dec(x_436);
lean_dec(x_435);
lean_dec(x_434);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_525 = lean_ctor_get(x_443, 0);
lean_inc(x_525);
lean_dec(x_443);
lean_ctor_set(x_437, 0, x_525);
return x_437;
}
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_526 = lean_ctor_get(x_437, 0);
x_527 = lean_ctor_get(x_437, 1);
lean_inc(x_527);
lean_inc(x_526);
lean_dec(x_437);
x_528 = lean_ctor_get(x_526, 1);
lean_inc(x_528);
lean_dec(x_526);
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
lean_dec(x_528);
lean_inc(x_1);
x_530 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_529, x_1);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; 
lean_inc(x_3);
x_531 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(x_434, x_435, x_436, x_2, x_3, x_4, x_5, x_527);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; uint8_t x_535; 
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_531, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 lean_ctor_release(x_531, 1);
 x_534 = x_531;
} else {
 lean_dec_ref(x_531);
 x_534 = lean_box(0);
}
x_535 = l_Lean_Expr_hasMVar(x_1);
if (x_535 == 0)
{
uint8_t x_536; 
x_536 = l_Lean_Expr_hasMVar(x_532);
if (x_536 == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
lean_dec(x_534);
x_537 = lean_st_ref_take(x_3, x_533);
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_538, 1);
lean_inc(x_539);
x_540 = lean_ctor_get(x_537, 1);
lean_inc(x_540);
lean_dec(x_537);
x_541 = lean_ctor_get(x_538, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_538, 2);
lean_inc(x_542);
x_543 = lean_ctor_get(x_538, 3);
lean_inc(x_543);
if (lean_is_exclusive(x_538)) {
 lean_ctor_release(x_538, 0);
 lean_ctor_release(x_538, 1);
 lean_ctor_release(x_538, 2);
 lean_ctor_release(x_538, 3);
 x_544 = x_538;
} else {
 lean_dec_ref(x_538);
 x_544 = lean_box(0);
}
x_545 = lean_ctor_get(x_539, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_539, 1);
lean_inc(x_546);
x_547 = lean_ctor_get(x_539, 2);
lean_inc(x_547);
x_548 = lean_ctor_get(x_539, 3);
lean_inc(x_548);
x_549 = lean_ctor_get(x_539, 4);
lean_inc(x_549);
x_550 = lean_ctor_get(x_539, 5);
lean_inc(x_550);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 lean_ctor_release(x_539, 2);
 lean_ctor_release(x_539, 3);
 lean_ctor_release(x_539, 4);
 lean_ctor_release(x_539, 5);
 x_551 = x_539;
} else {
 lean_dec_ref(x_539);
 x_551 = lean_box(0);
}
lean_inc(x_532);
x_552 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_545, x_1, x_532);
if (lean_is_scalar(x_551)) {
 x_553 = lean_alloc_ctor(0, 6, 0);
} else {
 x_553 = x_551;
}
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_546);
lean_ctor_set(x_553, 2, x_547);
lean_ctor_set(x_553, 3, x_548);
lean_ctor_set(x_553, 4, x_549);
lean_ctor_set(x_553, 5, x_550);
if (lean_is_scalar(x_544)) {
 x_554 = lean_alloc_ctor(0, 4, 0);
} else {
 x_554 = x_544;
}
lean_ctor_set(x_554, 0, x_541);
lean_ctor_set(x_554, 1, x_553);
lean_ctor_set(x_554, 2, x_542);
lean_ctor_set(x_554, 3, x_543);
x_555 = lean_st_ref_set(x_3, x_554, x_540);
lean_dec(x_3);
x_556 = lean_ctor_get(x_555, 1);
lean_inc(x_556);
if (lean_is_exclusive(x_555)) {
 lean_ctor_release(x_555, 0);
 lean_ctor_release(x_555, 1);
 x_557 = x_555;
} else {
 lean_dec_ref(x_555);
 x_557 = lean_box(0);
}
if (lean_is_scalar(x_557)) {
 x_558 = lean_alloc_ctor(0, 2, 0);
} else {
 x_558 = x_557;
}
lean_ctor_set(x_558, 0, x_532);
lean_ctor_set(x_558, 1, x_556);
return x_558;
}
else
{
lean_object* x_559; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_534)) {
 x_559 = lean_alloc_ctor(0, 2, 0);
} else {
 x_559 = x_534;
}
lean_ctor_set(x_559, 0, x_532);
lean_ctor_set(x_559, 1, x_533);
return x_559;
}
}
else
{
lean_object* x_560; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_534)) {
 x_560 = lean_alloc_ctor(0, 2, 0);
} else {
 x_560 = x_534;
}
lean_ctor_set(x_560, 0, x_532);
lean_ctor_set(x_560, 1, x_533);
return x_560;
}
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
lean_dec(x_3);
lean_dec(x_1);
x_561 = lean_ctor_get(x_531, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_531, 1);
lean_inc(x_562);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 lean_ctor_release(x_531, 1);
 x_563 = x_531;
} else {
 lean_dec_ref(x_531);
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
lean_object* x_565; lean_object* x_566; 
lean_dec(x_436);
lean_dec(x_435);
lean_dec(x_434);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_565 = lean_ctor_get(x_530, 0);
lean_inc(x_565);
lean_dec(x_530);
x_566 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_527);
return x_566;
}
}
}
default: 
{
lean_object* x_567; uint8_t x_568; 
x_567 = lean_st_ref_get(x_3, x_6);
x_568 = !lean_is_exclusive(x_567);
if (x_568 == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_569 = lean_ctor_get(x_567, 0);
x_570 = lean_ctor_get(x_567, 1);
x_571 = lean_ctor_get(x_569, 1);
lean_inc(x_571);
lean_dec(x_569);
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
lean_dec(x_571);
lean_inc(x_1);
x_573 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_572, x_1);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; 
lean_free_object(x_567);
x_574 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1;
lean_inc(x_3);
lean_inc(x_1);
x_575 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_1, x_574, x_2, x_3, x_4, x_5, x_570);
if (lean_obj_tag(x_575) == 0)
{
uint8_t x_576; 
x_576 = !lean_is_exclusive(x_575);
if (x_576 == 0)
{
lean_object* x_577; lean_object* x_578; uint8_t x_579; 
x_577 = lean_ctor_get(x_575, 0);
x_578 = lean_ctor_get(x_575, 1);
x_579 = l_Lean_Expr_hasMVar(x_1);
if (x_579 == 0)
{
uint8_t x_580; 
x_580 = l_Lean_Expr_hasMVar(x_577);
if (x_580 == 0)
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; uint8_t x_585; 
lean_free_object(x_575);
x_581 = lean_st_ref_take(x_3, x_578);
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_582, 1);
lean_inc(x_583);
x_584 = lean_ctor_get(x_581, 1);
lean_inc(x_584);
lean_dec(x_581);
x_585 = !lean_is_exclusive(x_582);
if (x_585 == 0)
{
lean_object* x_586; uint8_t x_587; 
x_586 = lean_ctor_get(x_582, 1);
lean_dec(x_586);
x_587 = !lean_is_exclusive(x_583);
if (x_587 == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; 
x_588 = lean_ctor_get(x_583, 0);
lean_inc(x_577);
x_589 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_588, x_1, x_577);
lean_ctor_set(x_583, 0, x_589);
x_590 = lean_st_ref_set(x_3, x_582, x_584);
lean_dec(x_3);
x_591 = !lean_is_exclusive(x_590);
if (x_591 == 0)
{
lean_object* x_592; 
x_592 = lean_ctor_get(x_590, 0);
lean_dec(x_592);
lean_ctor_set(x_590, 0, x_577);
return x_590;
}
else
{
lean_object* x_593; lean_object* x_594; 
x_593 = lean_ctor_get(x_590, 1);
lean_inc(x_593);
lean_dec(x_590);
x_594 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_594, 0, x_577);
lean_ctor_set(x_594, 1, x_593);
return x_594;
}
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_595 = lean_ctor_get(x_583, 0);
x_596 = lean_ctor_get(x_583, 1);
x_597 = lean_ctor_get(x_583, 2);
x_598 = lean_ctor_get(x_583, 3);
x_599 = lean_ctor_get(x_583, 4);
x_600 = lean_ctor_get(x_583, 5);
lean_inc(x_600);
lean_inc(x_599);
lean_inc(x_598);
lean_inc(x_597);
lean_inc(x_596);
lean_inc(x_595);
lean_dec(x_583);
lean_inc(x_577);
x_601 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_595, x_1, x_577);
x_602 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_602, 0, x_601);
lean_ctor_set(x_602, 1, x_596);
lean_ctor_set(x_602, 2, x_597);
lean_ctor_set(x_602, 3, x_598);
lean_ctor_set(x_602, 4, x_599);
lean_ctor_set(x_602, 5, x_600);
lean_ctor_set(x_582, 1, x_602);
x_603 = lean_st_ref_set(x_3, x_582, x_584);
lean_dec(x_3);
x_604 = lean_ctor_get(x_603, 1);
lean_inc(x_604);
if (lean_is_exclusive(x_603)) {
 lean_ctor_release(x_603, 0);
 lean_ctor_release(x_603, 1);
 x_605 = x_603;
} else {
 lean_dec_ref(x_603);
 x_605 = lean_box(0);
}
if (lean_is_scalar(x_605)) {
 x_606 = lean_alloc_ctor(0, 2, 0);
} else {
 x_606 = x_605;
}
lean_ctor_set(x_606, 0, x_577);
lean_ctor_set(x_606, 1, x_604);
return x_606;
}
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_607 = lean_ctor_get(x_582, 0);
x_608 = lean_ctor_get(x_582, 2);
x_609 = lean_ctor_get(x_582, 3);
lean_inc(x_609);
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_582);
x_610 = lean_ctor_get(x_583, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_583, 1);
lean_inc(x_611);
x_612 = lean_ctor_get(x_583, 2);
lean_inc(x_612);
x_613 = lean_ctor_get(x_583, 3);
lean_inc(x_613);
x_614 = lean_ctor_get(x_583, 4);
lean_inc(x_614);
x_615 = lean_ctor_get(x_583, 5);
lean_inc(x_615);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 lean_ctor_release(x_583, 1);
 lean_ctor_release(x_583, 2);
 lean_ctor_release(x_583, 3);
 lean_ctor_release(x_583, 4);
 lean_ctor_release(x_583, 5);
 x_616 = x_583;
} else {
 lean_dec_ref(x_583);
 x_616 = lean_box(0);
}
lean_inc(x_577);
x_617 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_610, x_1, x_577);
if (lean_is_scalar(x_616)) {
 x_618 = lean_alloc_ctor(0, 6, 0);
} else {
 x_618 = x_616;
}
lean_ctor_set(x_618, 0, x_617);
lean_ctor_set(x_618, 1, x_611);
lean_ctor_set(x_618, 2, x_612);
lean_ctor_set(x_618, 3, x_613);
lean_ctor_set(x_618, 4, x_614);
lean_ctor_set(x_618, 5, x_615);
x_619 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_619, 0, x_607);
lean_ctor_set(x_619, 1, x_618);
lean_ctor_set(x_619, 2, x_608);
lean_ctor_set(x_619, 3, x_609);
x_620 = lean_st_ref_set(x_3, x_619, x_584);
lean_dec(x_3);
x_621 = lean_ctor_get(x_620, 1);
lean_inc(x_621);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 lean_ctor_release(x_620, 1);
 x_622 = x_620;
} else {
 lean_dec_ref(x_620);
 x_622 = lean_box(0);
}
if (lean_is_scalar(x_622)) {
 x_623 = lean_alloc_ctor(0, 2, 0);
} else {
 x_623 = x_622;
}
lean_ctor_set(x_623, 0, x_577);
lean_ctor_set(x_623, 1, x_621);
return x_623;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_575;
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_575;
}
}
else
{
lean_object* x_624; lean_object* x_625; uint8_t x_626; 
x_624 = lean_ctor_get(x_575, 0);
x_625 = lean_ctor_get(x_575, 1);
lean_inc(x_625);
lean_inc(x_624);
lean_dec(x_575);
x_626 = l_Lean_Expr_hasMVar(x_1);
if (x_626 == 0)
{
uint8_t x_627; 
x_627 = l_Lean_Expr_hasMVar(x_624);
if (x_627 == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_628 = lean_st_ref_take(x_3, x_625);
x_629 = lean_ctor_get(x_628, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_629, 1);
lean_inc(x_630);
x_631 = lean_ctor_get(x_628, 1);
lean_inc(x_631);
lean_dec(x_628);
x_632 = lean_ctor_get(x_629, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_629, 2);
lean_inc(x_633);
x_634 = lean_ctor_get(x_629, 3);
lean_inc(x_634);
if (lean_is_exclusive(x_629)) {
 lean_ctor_release(x_629, 0);
 lean_ctor_release(x_629, 1);
 lean_ctor_release(x_629, 2);
 lean_ctor_release(x_629, 3);
 x_635 = x_629;
} else {
 lean_dec_ref(x_629);
 x_635 = lean_box(0);
}
x_636 = lean_ctor_get(x_630, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_630, 1);
lean_inc(x_637);
x_638 = lean_ctor_get(x_630, 2);
lean_inc(x_638);
x_639 = lean_ctor_get(x_630, 3);
lean_inc(x_639);
x_640 = lean_ctor_get(x_630, 4);
lean_inc(x_640);
x_641 = lean_ctor_get(x_630, 5);
lean_inc(x_641);
if (lean_is_exclusive(x_630)) {
 lean_ctor_release(x_630, 0);
 lean_ctor_release(x_630, 1);
 lean_ctor_release(x_630, 2);
 lean_ctor_release(x_630, 3);
 lean_ctor_release(x_630, 4);
 lean_ctor_release(x_630, 5);
 x_642 = x_630;
} else {
 lean_dec_ref(x_630);
 x_642 = lean_box(0);
}
lean_inc(x_624);
x_643 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_636, x_1, x_624);
if (lean_is_scalar(x_642)) {
 x_644 = lean_alloc_ctor(0, 6, 0);
} else {
 x_644 = x_642;
}
lean_ctor_set(x_644, 0, x_643);
lean_ctor_set(x_644, 1, x_637);
lean_ctor_set(x_644, 2, x_638);
lean_ctor_set(x_644, 3, x_639);
lean_ctor_set(x_644, 4, x_640);
lean_ctor_set(x_644, 5, x_641);
if (lean_is_scalar(x_635)) {
 x_645 = lean_alloc_ctor(0, 4, 0);
} else {
 x_645 = x_635;
}
lean_ctor_set(x_645, 0, x_632);
lean_ctor_set(x_645, 1, x_644);
lean_ctor_set(x_645, 2, x_633);
lean_ctor_set(x_645, 3, x_634);
x_646 = lean_st_ref_set(x_3, x_645, x_631);
lean_dec(x_3);
x_647 = lean_ctor_get(x_646, 1);
lean_inc(x_647);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 lean_ctor_release(x_646, 1);
 x_648 = x_646;
} else {
 lean_dec_ref(x_646);
 x_648 = lean_box(0);
}
if (lean_is_scalar(x_648)) {
 x_649 = lean_alloc_ctor(0, 2, 0);
} else {
 x_649 = x_648;
}
lean_ctor_set(x_649, 0, x_624);
lean_ctor_set(x_649, 1, x_647);
return x_649;
}
else
{
lean_object* x_650; 
lean_dec(x_3);
lean_dec(x_1);
x_650 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_650, 0, x_624);
lean_ctor_set(x_650, 1, x_625);
return x_650;
}
}
else
{
lean_object* x_651; 
lean_dec(x_3);
lean_dec(x_1);
x_651 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_651, 0, x_624);
lean_ctor_set(x_651, 1, x_625);
return x_651;
}
}
}
else
{
uint8_t x_652; 
lean_dec(x_3);
lean_dec(x_1);
x_652 = !lean_is_exclusive(x_575);
if (x_652 == 0)
{
return x_575;
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_653 = lean_ctor_get(x_575, 0);
x_654 = lean_ctor_get(x_575, 1);
lean_inc(x_654);
lean_inc(x_653);
lean_dec(x_575);
x_655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_655, 0, x_653);
lean_ctor_set(x_655, 1, x_654);
return x_655;
}
}
}
else
{
lean_object* x_656; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_656 = lean_ctor_get(x_573, 0);
lean_inc(x_656);
lean_dec(x_573);
lean_ctor_set(x_567, 0, x_656);
return x_567;
}
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_657 = lean_ctor_get(x_567, 0);
x_658 = lean_ctor_get(x_567, 1);
lean_inc(x_658);
lean_inc(x_657);
lean_dec(x_567);
x_659 = lean_ctor_get(x_657, 1);
lean_inc(x_659);
lean_dec(x_657);
x_660 = lean_ctor_get(x_659, 0);
lean_inc(x_660);
lean_dec(x_659);
lean_inc(x_1);
x_661 = l_Lean_PersistentHashMap_find_x3f___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__1(x_660, x_1);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; lean_object* x_663; 
x_662 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___closed__1;
lean_inc(x_3);
lean_inc(x_1);
x_663 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_1, x_662, x_2, x_3, x_4, x_5, x_658);
if (lean_obj_tag(x_663) == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; uint8_t x_667; 
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_663, 1);
lean_inc(x_665);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 lean_ctor_release(x_663, 1);
 x_666 = x_663;
} else {
 lean_dec_ref(x_663);
 x_666 = lean_box(0);
}
x_667 = l_Lean_Expr_hasMVar(x_1);
if (x_667 == 0)
{
uint8_t x_668; 
x_668 = l_Lean_Expr_hasMVar(x_664);
if (x_668 == 0)
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
lean_dec(x_666);
x_669 = lean_st_ref_take(x_3, x_665);
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_670, 1);
lean_inc(x_671);
x_672 = lean_ctor_get(x_669, 1);
lean_inc(x_672);
lean_dec(x_669);
x_673 = lean_ctor_get(x_670, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_670, 2);
lean_inc(x_674);
x_675 = lean_ctor_get(x_670, 3);
lean_inc(x_675);
if (lean_is_exclusive(x_670)) {
 lean_ctor_release(x_670, 0);
 lean_ctor_release(x_670, 1);
 lean_ctor_release(x_670, 2);
 lean_ctor_release(x_670, 3);
 x_676 = x_670;
} else {
 lean_dec_ref(x_670);
 x_676 = lean_box(0);
}
x_677 = lean_ctor_get(x_671, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_671, 1);
lean_inc(x_678);
x_679 = lean_ctor_get(x_671, 2);
lean_inc(x_679);
x_680 = lean_ctor_get(x_671, 3);
lean_inc(x_680);
x_681 = lean_ctor_get(x_671, 4);
lean_inc(x_681);
x_682 = lean_ctor_get(x_671, 5);
lean_inc(x_682);
if (lean_is_exclusive(x_671)) {
 lean_ctor_release(x_671, 0);
 lean_ctor_release(x_671, 1);
 lean_ctor_release(x_671, 2);
 lean_ctor_release(x_671, 3);
 lean_ctor_release(x_671, 4);
 lean_ctor_release(x_671, 5);
 x_683 = x_671;
} else {
 lean_dec_ref(x_671);
 x_683 = lean_box(0);
}
lean_inc(x_664);
x_684 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___spec__4(x_677, x_1, x_664);
if (lean_is_scalar(x_683)) {
 x_685 = lean_alloc_ctor(0, 6, 0);
} else {
 x_685 = x_683;
}
lean_ctor_set(x_685, 0, x_684);
lean_ctor_set(x_685, 1, x_678);
lean_ctor_set(x_685, 2, x_679);
lean_ctor_set(x_685, 3, x_680);
lean_ctor_set(x_685, 4, x_681);
lean_ctor_set(x_685, 5, x_682);
if (lean_is_scalar(x_676)) {
 x_686 = lean_alloc_ctor(0, 4, 0);
} else {
 x_686 = x_676;
}
lean_ctor_set(x_686, 0, x_673);
lean_ctor_set(x_686, 1, x_685);
lean_ctor_set(x_686, 2, x_674);
lean_ctor_set(x_686, 3, x_675);
x_687 = lean_st_ref_set(x_3, x_686, x_672);
lean_dec(x_3);
x_688 = lean_ctor_get(x_687, 1);
lean_inc(x_688);
if (lean_is_exclusive(x_687)) {
 lean_ctor_release(x_687, 0);
 lean_ctor_release(x_687, 1);
 x_689 = x_687;
} else {
 lean_dec_ref(x_687);
 x_689 = lean_box(0);
}
if (lean_is_scalar(x_689)) {
 x_690 = lean_alloc_ctor(0, 2, 0);
} else {
 x_690 = x_689;
}
lean_ctor_set(x_690, 0, x_664);
lean_ctor_set(x_690, 1, x_688);
return x_690;
}
else
{
lean_object* x_691; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_666)) {
 x_691 = lean_alloc_ctor(0, 2, 0);
} else {
 x_691 = x_666;
}
lean_ctor_set(x_691, 0, x_664);
lean_ctor_set(x_691, 1, x_665);
return x_691;
}
}
else
{
lean_object* x_692; 
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_666)) {
 x_692 = lean_alloc_ctor(0, 2, 0);
} else {
 x_692 = x_666;
}
lean_ctor_set(x_692, 0, x_664);
lean_ctor_set(x_692, 1, x_665);
return x_692;
}
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
lean_dec(x_3);
lean_dec(x_1);
x_693 = lean_ctor_get(x_663, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_663, 1);
lean_inc(x_694);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 lean_ctor_release(x_663, 1);
 x_695 = x_663;
} else {
 lean_dec_ref(x_663);
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
lean_object* x_697; lean_object* x_698; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_697 = lean_ctor_get(x_661, 0);
lean_inc(x_697);
lean_dec(x_661);
x_698 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_698, 0, x_697);
lean_ctor_set(x_698, 1, x_658);
return x_698;
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
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
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
x_18 = lean_nat_dec_eq(x_10, x_11);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_20 = lean_ctor_get(x_4, 10);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 9);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 8);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 7);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 6);
lean_dec(x_24);
x_25 = lean_ctor_get(x_4, 5);
lean_dec(x_25);
x_26 = lean_ctor_get(x_4, 4);
lean_dec(x_26);
x_27 = lean_ctor_get(x_4, 3);
lean_dec(x_27);
x_28 = lean_ctor_get(x_4, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_4, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_4, 0);
lean_dec(x_30);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_10, x_31);
lean_dec(x_10);
lean_ctor_set(x_4, 3, x_32);
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
uint8_t x_36; lean_object* x_37; 
x_36 = 1;
lean_ctor_set_uint8(x_34, 5, x_36);
x_37 = l_Lean_Meta_inferTypeImp_infer(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_46 = lean_ctor_get_uint8(x_34, 0);
x_47 = lean_ctor_get_uint8(x_34, 1);
x_48 = lean_ctor_get_uint8(x_34, 2);
x_49 = lean_ctor_get_uint8(x_34, 3);
x_50 = lean_ctor_get_uint8(x_34, 4);
x_51 = lean_ctor_get_uint8(x_34, 6);
x_52 = lean_ctor_get_uint8(x_34, 7);
x_53 = lean_ctor_get_uint8(x_34, 8);
x_54 = lean_ctor_get_uint8(x_34, 9);
x_55 = lean_ctor_get_uint8(x_34, 10);
x_56 = lean_ctor_get_uint8(x_34, 11);
x_57 = lean_ctor_get_uint8(x_34, 12);
lean_dec(x_34);
x_58 = 1;
x_59 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_59, 0, x_46);
lean_ctor_set_uint8(x_59, 1, x_47);
lean_ctor_set_uint8(x_59, 2, x_48);
lean_ctor_set_uint8(x_59, 3, x_49);
lean_ctor_set_uint8(x_59, 4, x_50);
lean_ctor_set_uint8(x_59, 5, x_58);
lean_ctor_set_uint8(x_59, 6, x_51);
lean_ctor_set_uint8(x_59, 7, x_52);
lean_ctor_set_uint8(x_59, 8, x_53);
lean_ctor_set_uint8(x_59, 9, x_54);
lean_ctor_set_uint8(x_59, 10, x_55);
lean_ctor_set_uint8(x_59, 11, x_56);
lean_ctor_set_uint8(x_59, 12, x_57);
lean_ctor_set(x_2, 0, x_59);
x_60 = l_Lean_Meta_inferTypeImp_infer(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_67 = x_60;
} else {
 lean_dec_ref(x_60);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_69 = lean_ctor_get(x_2, 0);
x_70 = lean_ctor_get(x_2, 1);
x_71 = lean_ctor_get(x_2, 2);
x_72 = lean_ctor_get(x_2, 3);
x_73 = lean_ctor_get(x_2, 4);
x_74 = lean_ctor_get(x_2, 5);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_2);
x_75 = lean_ctor_get_uint8(x_69, 0);
x_76 = lean_ctor_get_uint8(x_69, 1);
x_77 = lean_ctor_get_uint8(x_69, 2);
x_78 = lean_ctor_get_uint8(x_69, 3);
x_79 = lean_ctor_get_uint8(x_69, 4);
x_80 = lean_ctor_get_uint8(x_69, 6);
x_81 = lean_ctor_get_uint8(x_69, 7);
x_82 = lean_ctor_get_uint8(x_69, 8);
x_83 = lean_ctor_get_uint8(x_69, 9);
x_84 = lean_ctor_get_uint8(x_69, 10);
x_85 = lean_ctor_get_uint8(x_69, 11);
x_86 = lean_ctor_get_uint8(x_69, 12);
if (lean_is_exclusive(x_69)) {
 x_87 = x_69;
} else {
 lean_dec_ref(x_69);
 x_87 = lean_box(0);
}
x_88 = 1;
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 0, 13);
} else {
 x_89 = x_87;
}
lean_ctor_set_uint8(x_89, 0, x_75);
lean_ctor_set_uint8(x_89, 1, x_76);
lean_ctor_set_uint8(x_89, 2, x_77);
lean_ctor_set_uint8(x_89, 3, x_78);
lean_ctor_set_uint8(x_89, 4, x_79);
lean_ctor_set_uint8(x_89, 5, x_88);
lean_ctor_set_uint8(x_89, 6, x_80);
lean_ctor_set_uint8(x_89, 7, x_81);
lean_ctor_set_uint8(x_89, 8, x_82);
lean_ctor_set_uint8(x_89, 9, x_83);
lean_ctor_set_uint8(x_89, 10, x_84);
lean_ctor_set_uint8(x_89, 11, x_85);
lean_ctor_set_uint8(x_89, 12, x_86);
x_90 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_70);
lean_ctor_set(x_90, 2, x_71);
lean_ctor_set(x_90, 3, x_72);
lean_ctor_set(x_90, 4, x_73);
lean_ctor_set(x_90, 5, x_74);
x_91 = l_Lean_Meta_inferTypeImp_infer(x_1, x_90, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_91, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_98 = x_91;
} else {
 lean_dec_ref(x_91);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_4);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_add(x_10, x_100);
lean_dec(x_10);
x_102 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_102, 0, x_7);
lean_ctor_set(x_102, 1, x_8);
lean_ctor_set(x_102, 2, x_9);
lean_ctor_set(x_102, 3, x_101);
lean_ctor_set(x_102, 4, x_11);
lean_ctor_set(x_102, 5, x_12);
lean_ctor_set(x_102, 6, x_13);
lean_ctor_set(x_102, 7, x_14);
lean_ctor_set(x_102, 8, x_15);
lean_ctor_set(x_102, 9, x_16);
lean_ctor_set(x_102, 10, x_17);
x_103 = lean_ctor_get(x_2, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_2, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_2, 2);
lean_inc(x_105);
x_106 = lean_ctor_get(x_2, 3);
lean_inc(x_106);
x_107 = lean_ctor_get(x_2, 4);
lean_inc(x_107);
x_108 = lean_ctor_get(x_2, 5);
lean_inc(x_108);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_109 = x_2;
} else {
 lean_dec_ref(x_2);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get_uint8(x_103, 0);
x_111 = lean_ctor_get_uint8(x_103, 1);
x_112 = lean_ctor_get_uint8(x_103, 2);
x_113 = lean_ctor_get_uint8(x_103, 3);
x_114 = lean_ctor_get_uint8(x_103, 4);
x_115 = lean_ctor_get_uint8(x_103, 6);
x_116 = lean_ctor_get_uint8(x_103, 7);
x_117 = lean_ctor_get_uint8(x_103, 8);
x_118 = lean_ctor_get_uint8(x_103, 9);
x_119 = lean_ctor_get_uint8(x_103, 10);
x_120 = lean_ctor_get_uint8(x_103, 11);
x_121 = lean_ctor_get_uint8(x_103, 12);
if (lean_is_exclusive(x_103)) {
 x_122 = x_103;
} else {
 lean_dec_ref(x_103);
 x_122 = lean_box(0);
}
x_123 = 1;
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 0, 13);
} else {
 x_124 = x_122;
}
lean_ctor_set_uint8(x_124, 0, x_110);
lean_ctor_set_uint8(x_124, 1, x_111);
lean_ctor_set_uint8(x_124, 2, x_112);
lean_ctor_set_uint8(x_124, 3, x_113);
lean_ctor_set_uint8(x_124, 4, x_114);
lean_ctor_set_uint8(x_124, 5, x_123);
lean_ctor_set_uint8(x_124, 6, x_115);
lean_ctor_set_uint8(x_124, 7, x_116);
lean_ctor_set_uint8(x_124, 8, x_117);
lean_ctor_set_uint8(x_124, 9, x_118);
lean_ctor_set_uint8(x_124, 10, x_119);
lean_ctor_set_uint8(x_124, 11, x_120);
lean_ctor_set_uint8(x_124, 12, x_121);
if (lean_is_scalar(x_109)) {
 x_125 = lean_alloc_ctor(0, 6, 0);
} else {
 x_125 = x_109;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_104);
lean_ctor_set(x_125, 2, x_105);
lean_ctor_set(x_125, 3, x_106);
lean_ctor_set(x_125, 4, x_107);
lean_ctor_set(x_125, 5, x_108);
x_126 = l_Lean_Meta_inferTypeImp_infer(x_1, x_125, x_3, x_102, x_5, x_6);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_126, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_126, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_133 = x_126;
} else {
 lean_dec_ref(x_126);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
}
else
{
lean_object* x_135; 
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
x_135 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_inferTypeImp___spec__1(x_12, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_135;
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_19);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_29);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_9);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_19);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_33);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_ctor_get(x_5, 2);
x_22 = lean_ctor_get(x_5, 3);
x_23 = lean_ctor_get(x_5, 4);
x_24 = lean_ctor_get(x_5, 5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_25 = 0;
x_26 = l_Lean_LocalContext_mkLocalDecl(x_20, x_11, x_1, x_3, x_2, x_25);
x_27 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_21);
lean_ctor_set(x_27, 3, x_22);
lean_ctor_set(x_27, 4, x_23);
lean_ctor_set(x_27, 5, x_24);
x_28 = lean_apply_6(x_4, x_13, x_27, x_6, x_7, x_8, x_12);
return x_28;
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
LEAN_EXPORT uint8_t l_Lean_Meta_isTypeFormerTypeQuick(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 7:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerTypeQuick___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_isTypeFormerTypeQuick(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_isTypeFormerType_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
case 7:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
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
lean_dec(x_3);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_25);
lean_ctor_set(x_28, 4, x_26);
lean_ctor_set(x_28, 5, x_27);
x_29 = lean_array_push(x_2, x_19);
x_1 = x_13;
x_2 = x_29;
x_3 = x_28;
x_7 = x_18;
goto _start;
}
default: 
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_32 = l_Lean_Meta_whnfD(x_31, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
switch (lean_obj_tag(x_33)) {
case 3:
{
uint8_t x_34; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = 1;
x_37 = lean_box(x_36);
lean_ctor_set(x_32, 0, x_37);
return x_32;
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = 1;
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
case 7:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_dec(x_32);
x_43 = l_Lean_Meta_isTypeFormerType_go___closed__1;
x_1 = x_33;
x_2 = x_43;
x_7 = x_42;
goto _start;
}
default: 
{
uint8_t x_45; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_32);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_32, 0);
lean_dec(x_46);
x_47 = 0;
x_48 = lean_box(x_47);
lean_ctor_set(x_32, 0, x_48);
return x_32;
}
else
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_32, 1);
lean_inc(x_49);
lean_dec(x_32);
x_50 = 0;
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
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
x_53 = !lean_is_exclusive(x_32);
if (x_53 == 0)
{
return x_32;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_32, 0);
x_55 = lean_ctor_get(x_32, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_32);
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
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Meta_isTypeFormerTypeQuick(x_1);
if (x_7 == 0)
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
x_12 = l_Lean_Meta_isTypeFormerType_go___closed__1;
lean_inc(x_3);
x_13 = l_Lean_Meta_isTypeFormerType_go(x_1, x_12, x_2, x_3, x_4, x_5, x_10);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 2);
x_28 = lean_ctor_get(x_17, 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_11);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_st_ref_set(x_3, x_29, x_18);
lean_dec(x_3);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_13, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_dec(x_13);
x_36 = lean_st_ref_take(x_3, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_37, 1);
lean_dec(x_40);
lean_ctor_set(x_37, 1, x_11);
x_41 = lean_st_ref_set(x_3, x_37, x_38);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 0, x_34);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_34);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_37, 2);
x_48 = lean_ctor_get(x_37, 3);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_37);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_11);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set(x_49, 3, x_48);
x_50 = lean_st_ref_set(x_3, x_49, x_38);
lean_dec(x_3);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
 lean_ctor_set_tag(x_53, 1);
}
lean_ctor_set(x_53, 0, x_34);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = 1;
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_6);
return x_56;
}
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_LBool(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_LBool(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10___closed__1 = _init_l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10___closed__1();
lean_mark_persistent(l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10___closed__1);
l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10___closed__2 = _init_l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10___closed__2();
lean_mark_persistent(l_panic___at_Lean_Expr_instantiateBetaRevRange_visit___spec__10___closed__2);
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
l_Lean_Meta_isTypeFormerType_go___closed__1 = _init_l_Lean_Meta_isTypeFormerType_go___closed__1();
lean_mark_persistent(l_Lean_Meta_isTypeFormerType_go___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
