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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_arrowDomainsN___lam__0___closed__3;
lean_object* l_Lean_hashMVarId____x40_Lean_Expr___hyg_1872____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__1;
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
lean_object* l_Lean_MetavarContext_findDecl_x3f(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
static lean_object* l_Lean_Meta_throwUnknownMVar___redArg___closed__2;
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__3;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2___redArg(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__4;
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__0;
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__14;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Expr_instantiateBetaRevRange_visit_spec__6___redArg(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object*, lean_object*);
lean_object* l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__1;
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__0;
extern lean_object* l_Lean_unknownIdentifierMessageTag;
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__12;
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
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
uint8_t l_Lean_Level_isZero(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__4;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_arrowDomainsN_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_arrowDomainsN_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Literal_type(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__3;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__2;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_arrowDomainsN_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
static lean_object* l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__5;
lean_object* l_Lean_Meta_instBEqExprConfigCacheKey___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at_____private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Meta_mkExprConfigCacheKey___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_arrowDomainsN___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__0;
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
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Lean_Meta_isPropFormerType_spec__0(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Expr_instantiateBetaRevRange_visit_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Expr_instantiateBetaRevRange_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0;
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__1;
static lean_object* l_Lean_Meta_throwTypeExpected___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_instantiateBetaRevRange_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevelQuick___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__6;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_level_mvars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__6;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__6;
static lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_inferTypeImp_infer___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___Lean_Meta_arrowDomainsN_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l_Lean_Meta_instDecidableEqProjReductionKind(uint8_t, uint8_t);
static lean_object* l_Lean_Meta_throwFunctionExpected___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_isPropQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___redArg(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___closed__0;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object*);
static lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Lean_Meta_isPropFormerType_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Expr_instantiateBetaRevRange_visit_spec__6___redArg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg___closed__5;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__1;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_consume_type_annotations(lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwFunctionExpected___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_equal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at_____private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_414_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__2;
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwTypeExpected___redArg___closed__1;
lean_object* l_Lean_FVarId_throwUnknown___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at_____private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_inferTypeImp_infer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Expr_instantiateBetaRevRange_visit_spec__5___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadStateCacheT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Expr_instantiateBetaRevRange_visit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__7;
static lean_object* l_Lean_Meta_arrowDomainsN___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___Lean_Expr_instantiateBetaRevRange_visit_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__0;
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_arrowDomainsN_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4_spec__4___closed__3;
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__16;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__7;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
static lean_object* l_Lean_Meta_throwUnknownMVar___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_arrowDomainsN___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__13;
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isProofQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__4;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_typeFormerTypeLevel___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___boxed(lean_object**);
static lean_object* l_Lean_Meta_inferTypeImp_infer___closed__1;
static lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Meta_arrowDomainsN___lam__0___closed__2;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_throwUnknownMVar___redArg___closed__0;
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__11;
static lean_object* l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___Lean_Expr_instantiateBetaRevRange_visit_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_arrowDomainsN___lam__0___closed__1;
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_instantiateBetaRevRange(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__9;
lean_object* l_Lean_Meta_instHashableExprConfigCacheKey___private__1___boxed(lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Expr_instantiateBetaRevRange_visit_spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__2;
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_instantiateBetaRevRange_visit_spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_instantiateBetaRevRange_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isNeverZero(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Expr_instantiateBetaRevRange_visit_spec__6___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isPropFormerType___closed__0;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at_____private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__4;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_arrowDomainsN_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange_visit___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_beqMVarId____x40_Lean_Expr___hyg_1814____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Expr_instantiateBetaRevRange_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_throwUnknownMVar___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__15;
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__6;
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isTypeQuick(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_throwFunctionExpected___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Expr_instantiateBetaRevRange_visit_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__7;
lean_object* l_Lean_Meta_getConfig___redArg(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_instantiateBetaRevRange_spec__0(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(x_12);
x_15 = lean_unsigned_to_nat(0u);
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
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_expr_equal(x_9, x_11);
if (x_13 == 0)
{
x_6 = x_13;
goto block_8;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_10, x_12);
x_6 = x_14;
goto block_8;
}
block_8:
{
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_1);
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
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_5);
x_10 = lean_array_push(x_6, x_9);
x_5 = x_8;
x_6 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
lean_inc(x_4);
lean_inc_ref(x_5);
x_12 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_5, x_4, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_array_size(x_6);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at___Lean_Expr_instantiateBetaRevRange_visit_spec__0(x_1, x_2, x_3, x_4, x_15, x_16, x_6, x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_Expr_isBVar(x_5);
lean_dec_ref(x_5);
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
uint8_t x_22; lean_object* x_23; 
x_22 = 0;
x_23 = l_Lean_Expr_betaRev(x_13, x_19, x_22, x_22);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = l_Lean_Expr_isBVar(x_5);
lean_dec_ref(x_5);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_mkAppRev(x_13, x_24);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = 0;
x_30 = l_Lean_Expr_betaRev(x_13, x_24, x_29, x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
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
x_3 = lean_unsigned_to_nat(67u);
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
x_3 = lean_unsigned_to_nat(68u);
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
x_3 = lean_unsigned_to_nat(69u);
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
x_3 = lean_unsigned_to_nat(66u);
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
x_3 = lean_unsigned_to_nat(70u);
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
lean_inc_ref(x_10);
lean_inc(x_5);
lean_inc_ref(x_4);
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
lean_dec_ref(x_6);
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
lean_dec_ref(x_91);
x_12 = x_93;
x_13 = x_9;
x_14 = x_10;
goto block_53;
}
}
case 1:
{
lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_10);
lean_dec(x_9);
x_94 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__3;
x_95 = l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7(x_94, x_6);
x_59 = x_95;
goto block_62;
}
case 2:
{
lean_object* x_96; lean_object* x_97; 
lean_dec_ref(x_10);
lean_dec(x_9);
x_96 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__4;
x_97 = l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7(x_96, x_6);
x_59 = x_97;
goto block_62;
}
case 3:
{
lean_object* x_98; lean_object* x_99; 
lean_dec_ref(x_10);
lean_dec(x_9);
x_98 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__5;
x_99 = l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7(x_98, x_6);
x_59 = x_99;
goto block_62;
}
case 4:
{
lean_object* x_100; lean_object* x_101; 
lean_dec_ref(x_10);
lean_dec(x_9);
x_100 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__6;
x_101 = l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7(x_100, x_6);
x_59 = x_101;
goto block_62;
}
case 5:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec_ref(x_10);
lean_dec(x_9);
x_102 = l_Lean_Expr_getAppNumArgs(x_4);
x_103 = lean_mk_empty_array_with_capacity(x_102);
lean_dec(x_102);
lean_inc_ref(x_4);
lean_inc(x_5);
x_104 = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___Lean_Expr_instantiateBetaRevRange_visit_spec__8(x_1, x_2, x_3, x_5, x_4, x_103, x_6);
x_59 = x_104;
goto block_62;
}
case 6:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; size_t x_122; size_t x_123; uint8_t x_124; 
lean_dec_ref(x_10);
lean_dec(x_9);
x_105 = lean_ctor_get(x_4, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_107);
x_108 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
lean_inc(x_5);
lean_inc_ref(x_106);
x_109 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_106, x_5, x_6);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec_ref(x_109);
x_112 = lean_unsigned_to_nat(1u);
x_113 = lean_nat_add(x_5, x_112);
lean_inc_ref(x_107);
x_114 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_107, x_113, x_111);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec_ref(x_114);
x_122 = lean_ptr_addr(x_106);
lean_dec_ref(x_106);
x_123 = lean_ptr_addr(x_110);
x_124 = lean_usize_dec_eq(x_122, x_123);
if (x_124 == 0)
{
lean_dec_ref(x_107);
x_117 = x_124;
goto block_121;
}
else
{
size_t x_125; size_t x_126; uint8_t x_127; 
x_125 = lean_ptr_addr(x_107);
lean_dec_ref(x_107);
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
x_119 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_414_(x_108, x_108);
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
lean_inc_ref(x_4);
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
lean_dec_ref(x_10);
lean_dec(x_9);
x_128 = lean_ctor_get(x_4, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_130);
x_131 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 8);
lean_inc(x_5);
lean_inc_ref(x_129);
x_132 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_129, x_5, x_6);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec_ref(x_132);
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_nat_add(x_5, x_135);
lean_inc_ref(x_130);
x_137 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_130, x_136, x_134);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec_ref(x_137);
x_145 = lean_ptr_addr(x_129);
lean_dec_ref(x_129);
x_146 = lean_ptr_addr(x_133);
x_147 = lean_usize_dec_eq(x_145, x_146);
if (x_147 == 0)
{
lean_dec_ref(x_130);
x_140 = x_147;
goto block_144;
}
else
{
size_t x_148; size_t x_149; uint8_t x_150; 
x_148 = lean_ptr_addr(x_130);
lean_dec_ref(x_130);
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
x_142 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_414_(x_131, x_131);
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
lean_inc_ref(x_4);
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
lean_dec_ref(x_10);
lean_dec(x_9);
x_151 = lean_ctor_get(x_4, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_152);
x_153 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_153);
x_154 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_154);
x_155 = lean_ctor_get_uint8(x_4, sizeof(void*)*4 + 8);
lean_inc(x_5);
lean_inc_ref(x_152);
x_156 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_152, x_5, x_6);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec_ref(x_156);
lean_inc(x_5);
lean_inc_ref(x_153);
x_159 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_153, x_5, x_158);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec_ref(x_159);
x_162 = lean_unsigned_to_nat(1u);
x_163 = lean_nat_add(x_5, x_162);
lean_inc_ref(x_154);
x_164 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_154, x_163, x_161);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec_ref(x_164);
x_174 = lean_ptr_addr(x_152);
lean_dec_ref(x_152);
x_175 = lean_ptr_addr(x_157);
x_176 = lean_usize_dec_eq(x_174, x_175);
if (x_176 == 0)
{
lean_dec_ref(x_153);
x_167 = x_176;
goto block_173;
}
else
{
size_t x_177; size_t x_178; uint8_t x_179; 
x_177 = lean_ptr_addr(x_153);
lean_dec_ref(x_153);
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
lean_dec_ref(x_154);
x_168 = l_Lean_Expr_letE___override(x_151, x_157, x_160, x_165, x_155);
x_54 = x_168;
x_55 = x_166;
goto block_58;
}
else
{
size_t x_169; size_t x_170; uint8_t x_171; 
x_169 = lean_ptr_addr(x_154);
lean_dec_ref(x_154);
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
lean_inc_ref(x_4);
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
lean_dec_ref(x_10);
lean_dec(x_9);
x_180 = l_Lean_Expr_instantiateBetaRevRange_visit___closed__7;
x_181 = l_panic___at___Lean_Expr_instantiateBetaRevRange_visit_spec__7(x_180, x_6);
x_59 = x_181;
goto block_62;
}
case 10:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; size_t x_187; size_t x_188; uint8_t x_189; 
lean_dec_ref(x_10);
lean_dec(x_9);
x_182 = lean_ctor_get(x_4, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_183);
lean_inc(x_5);
lean_inc_ref(x_183);
x_184 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_183, x_5, x_6);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec_ref(x_184);
x_187 = lean_ptr_addr(x_183);
lean_dec_ref(x_183);
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
lean_inc_ref(x_4);
x_54 = x_4;
x_55 = x_186;
goto block_58;
}
}
default: 
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; size_t x_197; size_t x_198; uint8_t x_199; 
lean_dec_ref(x_10);
lean_dec(x_9);
x_191 = lean_ctor_get(x_4, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_4, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_193);
lean_inc(x_5);
lean_inc_ref(x_193);
x_194 = l_Lean_Expr_instantiateBetaRevRange_visit(x_1, x_2, x_3, x_193, x_5, x_6);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec_ref(x_194);
x_197 = lean_ptr_addr(x_193);
lean_dec_ref(x_193);
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
lean_inc_ref(x_4);
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
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
x_201 = lean_ctor_get(x_79, 0);
lean_inc(x_201);
lean_dec_ref(x_79);
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
lean_dec_ref(x_4);
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
lean_inc_ref(x_12);
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
lean_inc_ref(x_12);
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
lean_inc_ref(x_57);
lean_dec_ref(x_55);
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
lean_dec_ref(x_59);
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
lean_dec_ref(x_3);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Expr_instantiateBetaRevRange_visit_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Expr_instantiateBetaRevRange_visit_spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___Lean_Expr_instantiateBetaRevRange_visit_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Expr_0__Lean_Expr_withAppRevAux___at___Lean_Expr_instantiateBetaRevRange_visit_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
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
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Expr_instantiateBetaRevRange_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedExpr;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
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
x_3 = lean_unsigned_to_nat(32u);
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
lean_dec_ref(x_1);
x_8 = l_Lean_Expr_instantiateBetaRevRange___closed__2;
x_9 = l_panic___at___Lean_Expr_instantiateBetaRevRange_spec__0(x_8);
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
lean_dec_ref(x_12);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
lean_inc_ref(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
lean_inc_ref(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_3, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_ctor_get(x_4, 2);
lean_inc(x_35);
lean_inc_ref(x_34);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_1);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
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
x_12 = l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___redArg(x_11, x_2, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_throwFunctionExpected___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwFunctionExpected___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_throwFunctionExpected(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decLt___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
x_15 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___closed__0;
if (lean_obj_tag(x_13) == 7)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_26);
lean_dec_ref(x_13);
lean_ctor_set(x_5, 0, x_26);
x_16 = x_5;
x_17 = x_11;
goto block_25;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_Expr_instantiateBetaRevRange(x_13, x_14, x_6, x_1);
lean_dec(x_14);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_28 = lean_whnf(x_27, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 7)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_ctor_get(x_29, 2);
lean_inc_ref(x_31);
lean_dec_ref(x_29);
lean_inc(x_6);
lean_ctor_set(x_5, 1, x_6);
lean_ctor_set(x_5, 0, x_31);
x_16 = x_5;
x_17 = x_30;
goto block_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_29);
lean_free_object(x_5);
lean_dec(x_4);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec_ref(x_28);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_6, x_33);
lean_dec(x_6);
x_35 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_34, x_1, x_2, x_3);
lean_dec(x_34);
x_36 = l_Lean_Meta_throwFunctionExpected___redArg(x_35, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_free_object(x_5);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_28, 0);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_28);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
block_25:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_20 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_15);
lean_inc(x_19);
lean_inc(x_4);
x_21 = lean_apply_2(x_20, x_4, x_19);
x_22 = lean_unbox(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
else
{
x_5 = x_16;
x_6 = x_19;
x_11 = x_17;
goto _start;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_5, 0);
x_46 = lean_ctor_get(x_5, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_5);
x_47 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___closed__0;
if (lean_obj_tag(x_45) == 7)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_45, 2);
lean_inc_ref(x_58);
lean_dec_ref(x_45);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_46);
x_48 = x_59;
x_49 = x_11;
goto block_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Expr_instantiateBetaRevRange(x_45, x_46, x_6, x_1);
lean_dec(x_46);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_61 = lean_whnf(x_60, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 7)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = lean_ctor_get(x_62, 2);
lean_inc_ref(x_64);
lean_dec_ref(x_62);
lean_inc(x_6);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_6);
x_48 = x_65;
x_49 = x_63;
goto block_57;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_62);
lean_dec(x_4);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_dec_ref(x_61);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_6, x_67);
lean_dec(x_6);
x_69 = l___private_Lean_Expr_0__Lean_mkAppRangeAux(x_68, x_1, x_2, x_3);
lean_dec(x_68);
x_70 = l_Lean_Meta_throwFunctionExpected___redArg(x_69, x_7, x_8, x_9, x_10, x_66);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_75 = lean_ctor_get(x_61, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_61, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_77 = x_61;
} else {
 lean_dec_ref(x_61);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
block_57:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_6, x_50);
lean_dec(x_6);
x_52 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_47);
lean_inc(x_51);
lean_inc(x_4);
x_53 = lean_apply_2(x_52, x_4, x_51);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_51);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
else
{
x_5 = x_48;
x_6 = x_51;
x_11 = x_49;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
x_19 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(x_1, x_2, x_3, x_8, x_10, x_11, x_14, x_15, x_16, x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_12 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___closed__0;
x_13 = lean_array_get_size(x_2);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_12);
lean_inc(x_13);
x_22 = lean_apply_2(x_21, x_13, x_20);
x_23 = lean_unbox(x_22);
if (x_23 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_14 = x_9;
x_15 = x_20;
x_16 = x_10;
goto block_19;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_20);
lean_inc(x_13);
x_25 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(x_2, x_20, x_1, x_13, x_24, x_20, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_14 = x_28;
x_15 = x_29;
x_16 = x_27;
goto block_19;
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_11);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Expr_instantiateBetaRevRange(x_14, x_15, x_13, x_2);
lean_dec(x_13);
lean_dec(x_15);
if (lean_is_scalar(x_11)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_11;
}
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_4);
x_20 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0(x_1, x_2, x_3, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_9);
lean_dec_ref(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
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
x_14 = l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___redArg(x_13, x_3, x_4, x_5, x_6, x_7);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_throwIncorrectNumberOfLevels(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_9;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_unknownIdentifierMessageTag;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___closed__0;
x_9 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__6;
x_2 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5;
x_3 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__4;
x_4 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3;
x_5 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2;
x_6 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_5);
lean_ctor_set(x_8, 5, x_4);
lean_ctor_set(x_8, 6, x_3);
lean_ctor_set(x_8, 7, x_2);
lean_ctor_set(x_8, 8, x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__11() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__9;
x_4 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__10;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__11;
x_3 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__8;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("A private declaration `", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` exists but is not accessible in the current context.", 54, 54);
return x_1;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_16; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_12);
lean_dec(x_10);
x_16 = l_Lean_Name_isAnonymous(x_2);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = lean_ctor_get_uint8(x_12, sizeof(void*)*8);
if (x_17 == 0)
{
lean_dec_ref(x_12);
lean_free_object(x_8);
lean_dec(x_2);
goto block_15;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Environment_setExporting(x_12, x_16);
lean_inc(x_2);
lean_inc_ref(x_18);
x_19 = l_Lean_Environment_contains(x_18, x_2, x_17);
if (x_19 == 0)
{
lean_dec_ref(x_18);
lean_free_object(x_8);
lean_dec(x_2);
goto block_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__7;
x_21 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__12;
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set(x_23, 3, x_22);
x_24 = l_Lean_MessageData_ofConstName(x_2, x_16);
lean_ctor_set_tag(x_8, 3);
lean_ctor_set(x_8, 1, x_24);
lean_ctor_set(x_8, 0, x_23);
x_25 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__14;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_8);
x_27 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__16;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_MessageData_note(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(x_30, x_31, x_3, x_4, x_5, x_6, x_11);
return x_32;
}
}
}
else
{
lean_dec_ref(x_12);
lean_free_object(x_8);
lean_dec(x_2);
goto block_15;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(x_1, x_13, x_3, x_4, x_5, x_6, x_11);
return x_14;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_39; 
x_33 = lean_ctor_get(x_8, 0);
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_8);
x_35 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_35);
lean_dec(x_33);
x_39 = l_Lean_Name_isAnonymous(x_2);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = lean_ctor_get_uint8(x_35, sizeof(void*)*8);
if (x_40 == 0)
{
lean_dec_ref(x_35);
lean_dec(x_2);
goto block_38;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_Environment_setExporting(x_35, x_39);
lean_inc(x_2);
lean_inc_ref(x_41);
x_42 = l_Lean_Environment_contains(x_41, x_2, x_40);
if (x_42 == 0)
{
lean_dec_ref(x_41);
lean_dec(x_2);
goto block_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_43 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__7;
x_44 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__12;
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_44);
lean_ctor_set(x_46, 3, x_45);
x_47 = l_Lean_MessageData_ofConstName(x_2, x_39);
x_48 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__14;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__16;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_MessageData_note(x_52);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_box(0);
x_56 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(x_54, x_55, x_3, x_4, x_5, x_6, x_34);
return x_56;
}
}
}
else
{
lean_dec_ref(x_35);
lean_dec(x_2);
goto block_38;
}
block_38:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(0);
x_37 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(x_1, x_36, x_3, x_4, x_5, x_6, x_34);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 5);
x_10 = l_Lean_replaceRef(x_1, x_9);
lean_dec(x_9);
lean_ctor_set(x_5, 5, x_10);
x_11 = l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get(x_5, 5);
x_18 = lean_ctor_get(x_5, 6);
x_19 = lean_ctor_get(x_5, 7);
x_20 = lean_ctor_get(x_5, 8);
x_21 = lean_ctor_get(x_5, 9);
x_22 = lean_ctor_get(x_5, 10);
x_23 = lean_ctor_get_uint8(x_5, sizeof(void*)*13);
x_24 = lean_ctor_get(x_5, 11);
x_25 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_26 = lean_ctor_get(x_5, 12);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_27 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_28 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_13);
lean_ctor_set(x_28, 2, x_14);
lean_ctor_set(x_28, 3, x_15);
lean_ctor_set(x_28, 4, x_16);
lean_ctor_set(x_28, 5, x_27);
lean_ctor_set(x_28, 6, x_18);
lean_ctor_set(x_28, 7, x_19);
lean_ctor_set(x_28, 8, x_20);
lean_ctor_set(x_28, 9, x_21);
lean_ctor_set(x_28, 10, x_22);
lean_ctor_set(x_28, 11, x_24);
lean_ctor_set(x_28, 12, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*13, x_23);
lean_ctor_set_uint8(x_28, sizeof(void*)*13 + 1, x_25);
x_29 = l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___redArg(x_2, x_3, x_4, x_28, x_6, x_7);
lean_dec_ref(x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__1___redArg(x_1, x_10, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unknown constant `", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__1;
x_9 = 0;
lean_inc(x_2);
x_10 = l_Lean_MessageData_ofConstName(x_2, x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__3;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 5);
lean_inc(x_7);
x_8 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = 0;
lean_inc(x_1);
x_13 = l_Lean_Environment_findConstVal_x3f(x_11, x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_free_object(x_7);
x_14 = l_Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_10);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_4);
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec_ref(x_13);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_18);
lean_dec(x_16);
x_19 = 0;
lean_inc(x_1);
x_20 = l_Lean_Environment_findConstVal_x3f(x_18, x_1, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = l_Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_4);
lean_dec(x_1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc_ref(x_5);
lean_inc(x_1);
x_8 = l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
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
lean_dec_ref(x_5);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_16 = l_Lean_Core_instantiateTypeLevelParams___redArg(x_9, x_2, x_6, x_10);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec_ref(x_5);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = 0;
lean_inc(x_1);
x_13 = l_Lean_Environment_find_x3f(x_11, x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_free_object(x_7);
x_14 = l_Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_10);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_4);
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec_ref(x_13);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_18);
lean_dec(x_16);
x_19 = 0;
lean_inc(x_1);
x_20 = l_Lean_Environment_find_x3f(x_18, x_1, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = l_Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_4);
lean_dec(x_1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_12 = lean_whnf(x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_16 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___closed__0;
if (lean_obj_tag(x_13) == 7)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_27);
lean_dec_ref(x_13);
x_28 = l_Lean_Expr_hasLooseBVars(x_27);
if (x_28 == 0)
{
x_17 = x_27;
x_18 = x_14;
goto block_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_inc_ref(x_2);
lean_inc(x_6);
lean_inc(x_1);
x_29 = l_Lean_Expr_proj___override(x_1, x_6, x_2);
x_30 = lean_expr_instantiate1(x_27, x_29);
lean_dec_ref(x_29);
lean_dec_ref(x_27);
x_17 = x_30;
x_18 = x_14;
goto block_26;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
lean_inc_ref(x_3);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_32 = lean_apply_7(x_3, lean_box(0), x_31, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec_ref(x_32);
x_17 = x_13;
x_18 = x_33;
goto block_26;
}
else
{
uint8_t x_34; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_32);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
block_26:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_6, x_19);
lean_dec(x_6);
x_21 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_16);
lean_inc(x_20);
lean_inc(x_4);
x_22 = lean_apply_2(x_21, x_4, x_20);
x_23 = lean_unbox(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_15)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_15;
}
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
else
{
lean_dec(x_15);
x_5 = x_17;
x_6 = x_20;
x_11 = x_18;
goto _start;
}
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
x_19 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(x_1, x_2, x_3, x_8, x_10, x_11, x_14, x_15, x_16, x_17, x_18);
return x_19;
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
x_22 = l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___redArg(x_21, x_7, x_8, x_9, x_10, x_11);
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
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_9 = lean_infer_type(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_12 = lean_whnf(x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_58; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
lean_inc(x_13);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed), 11, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_13);
x_58 = l_Lean_Expr_getAppFn(x_13);
if (lean_obj_tag(x_58) == 4)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = lean_st_ref_get(x_7, x_14);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_67 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_67);
lean_dec(x_62);
x_68 = 0;
x_69 = l_Lean_Environment_find_x3f(x_67, x_59, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_60);
lean_dec_ref(x_15);
x_70 = lean_box(0);
x_71 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_13, lean_box(0), x_70, x_4, x_5, x_6, x_7, x_63);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_71;
}
else
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
lean_dec_ref(x_69);
if (lean_obj_tag(x_72) == 5)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc_ref(x_73);
lean_dec_ref(x_72);
x_74 = lean_ctor_get(x_73, 4);
lean_inc(x_74);
if (lean_obj_tag(x_74) == 0)
{
lean_dec_ref(x_73);
lean_dec(x_60);
lean_dec_ref(x_15);
goto block_66;
}
else
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_73, 2);
lean_inc(x_78);
lean_dec_ref(x_73);
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
lean_dec_ref(x_74);
lean_inc_ref(x_6);
x_80 = l_Lean_getConstInfo___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(x_79, x_4, x_5, x_6, x_7, x_63);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 6)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_106; uint8_t x_107; 
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec_ref(x_80);
x_83 = lean_ctor_get(x_81, 0);
lean_inc_ref(x_83);
lean_dec_ref(x_81);
x_106 = lean_ctor_get(x_76, 0);
lean_inc(x_106);
lean_dec_ref(x_76);
x_107 = lean_name_eq(x_106, x_1);
lean_dec(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_dec_ref(x_83);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_60);
lean_dec_ref(x_15);
x_108 = lean_box(0);
x_109 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_13, lean_box(0), x_108, x_4, x_5, x_6, x_7, x_82);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
return x_109;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_109);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
else
{
x_84 = x_4;
x_85 = x_5;
x_86 = x_6;
x_87 = x_7;
x_88 = x_82;
goto block_105;
}
block_105:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_89 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0;
x_90 = l_Lean_Expr_getAppNumArgs(x_13);
lean_inc(x_90);
x_91 = lean_mk_array(x_90, x_89);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_sub(x_90, x_92);
lean_dec(x_90);
lean_inc(x_13);
x_94 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_13, x_91, x_93);
x_95 = lean_nat_add(x_77, x_78);
lean_dec(x_78);
x_96 = lean_array_get_size(x_94);
x_97 = lean_nat_dec_eq(x_95, x_96);
lean_dec(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_96);
lean_dec_ref(x_94);
lean_dec_ref(x_83);
lean_dec(x_77);
lean_dec(x_60);
lean_dec_ref(x_15);
x_98 = lean_box(0);
x_99 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_13, lean_box(0), x_98, x_84, x_85, x_86, x_87, x_88);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_100 = lean_ctor_get(x_83, 0);
lean_inc_ref(x_100);
lean_dec_ref(x_83);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
x_102 = l_Lean_Expr_const___override(x_101, x_60);
x_103 = lean_unsigned_to_nat(0u);
x_104 = lean_nat_dec_le(x_77, x_96);
if (x_104 == 0)
{
lean_dec(x_77);
x_37 = x_87;
x_38 = x_88;
x_39 = x_94;
x_40 = x_85;
x_41 = x_86;
x_42 = x_102;
x_43 = x_84;
x_44 = x_103;
x_45 = x_96;
goto block_57;
}
else
{
lean_dec(x_96);
x_37 = x_87;
x_38 = x_88;
x_39 = x_94;
x_40 = x_85;
x_41 = x_86;
x_42 = x_102;
x_43 = x_84;
x_44 = x_103;
x_45 = x_77;
goto block_57;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_81);
lean_dec(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec(x_60);
lean_dec_ref(x_15);
x_114 = lean_ctor_get(x_80, 1);
lean_inc(x_114);
lean_dec_ref(x_80);
x_115 = lean_box(0);
x_116 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_13, lean_box(0), x_115, x_4, x_5, x_6, x_7, x_114);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec(x_60);
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_80);
if (x_117 == 0)
{
return x_80;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_80, 0);
x_119 = lean_ctor_get(x_80, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_80);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_73);
lean_dec(x_60);
lean_dec_ref(x_15);
goto block_66;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_72);
lean_dec(x_60);
lean_dec_ref(x_15);
x_121 = lean_box(0);
x_122 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_13, lean_box(0), x_121, x_4, x_5, x_6, x_7, x_63);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_122;
}
}
block_66:
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_box(0);
x_65 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_13, lean_box(0), x_64, x_4, x_5, x_6, x_7, x_63);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_65;
}
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_58);
lean_dec_ref(x_15);
x_123 = lean_box(0);
x_124 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_13, lean_box(0), x_123, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_124;
}
block_36:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_inc(x_16);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_19);
x_23 = lean_whnf(x_21, x_19, x_17, x_18, x_16, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 7)
{
uint8_t x_25; 
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_27);
lean_dec_ref(x_24);
x_28 = lean_expr_consume_type_annotations(x_27);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_24);
x_31 = lean_expr_consume_type_annotations(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_24);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_dec_ref(x_23);
x_34 = lean_box(0);
x_35 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_13, lean_box(0), x_34, x_19, x_17, x_18, x_16, x_33);
lean_dec(x_16);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_19);
return x_35;
}
}
else
{
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
}
else
{
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
block_57:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = l_Array_toSubarray___redArg(x_39, x_44, x_45);
x_47 = l_Array_ofSubarray___redArg(x_46);
lean_dec_ref(x_46);
lean_inc(x_37);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc_ref(x_43);
x_48 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_42, x_47, x_43, x_40, x_41, x_37, x_38);
lean_dec_ref(x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
x_51 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___closed__0;
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg(x_51);
lean_inc(x_2);
x_54 = lean_apply_2(x_53, x_2, x_52);
x_55 = lean_unbox(x_54);
if (x_55 == 0)
{
lean_dec(x_50);
lean_dec(x_49);
lean_dec_ref(x_15);
x_16 = x_37;
x_17 = x_40;
x_18 = x_41;
x_19 = x_43;
x_20 = x_48;
goto block_36;
}
else
{
lean_object* x_56; 
lean_dec_ref(x_48);
lean_inc(x_37);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc_ref(x_43);
lean_inc(x_2);
lean_inc_ref(x_3);
lean_inc(x_1);
x_56 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___redArg(x_1, x_3, x_15, x_2, x_49, x_52, x_43, x_40, x_41, x_37, x_50);
x_16 = x_37;
x_17 = x_40;
x_18 = x_41;
x_19 = x_43;
x_20 = x_56;
goto block_36;
}
}
else
{
lean_dec_ref(x_43);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_37);
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_48;
}
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfo___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_4);
x_20 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferProjType_spec__1(x_1, x_2, x_3, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_9);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type expected", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwTypeExpected___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_Meta_throwTypeExpected___redArg___closed__1;
x_8 = l_Lean_indentExpr(x_1);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Meta_throwFunctionExpected___redArg___closed__3;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___redArg(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_throwTypeExpected___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_throwTypeExpected___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwTypeExpected___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_throwTypeExpected(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_beqMVarId____x40_Lean_Expr___hyg_1814____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_hashMVarId____x40_Lean_Expr___hyg_1872____boxed), 1, 0);
return x_1;
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
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_7, 7);
x_13 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___closed__0;
x_14 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___closed__1;
x_15 = l_Lean_PersistentHashMap_insert___redArg(x_13, x_14, x_12, x_1, x_2);
lean_ctor_set(x_7, 7, x_15);
x_16 = lean_st_ref_set(x_3, x_6, x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
x_25 = lean_ctor_get(x_7, 2);
x_26 = lean_ctor_get(x_7, 3);
x_27 = lean_ctor_get(x_7, 4);
x_28 = lean_ctor_get(x_7, 5);
x_29 = lean_ctor_get(x_7, 6);
x_30 = lean_ctor_get(x_7, 7);
x_31 = lean_ctor_get(x_7, 8);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_32 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___closed__0;
x_33 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___closed__1;
x_34 = l_Lean_PersistentHashMap_insert___redArg(x_32, x_33, x_30, x_1, x_2);
x_35 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set(x_35, 4, x_27);
lean_ctor_set(x_35, 5, x_28);
lean_ctor_set(x_35, 6, x_29);
lean_ctor_set(x_35, 7, x_34);
lean_ctor_set(x_35, 8, x_31);
lean_ctor_set(x_6, 0, x_35);
x_36 = lean_st_ref_set(x_3, x_6, x_8);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_41 = lean_ctor_get(x_6, 1);
x_42 = lean_ctor_get(x_6, 2);
x_43 = lean_ctor_get(x_6, 3);
x_44 = lean_ctor_get(x_6, 4);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_6);
x_45 = lean_ctor_get(x_7, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_7, 3);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_7, 4);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_7, 5);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_7, 6);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_7, 7);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_7, 8);
lean_inc_ref(x_53);
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
 x_54 = x_7;
} else {
 lean_dec_ref(x_7);
 x_54 = lean_box(0);
}
x_55 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___closed__0;
x_56 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___closed__1;
x_57 = l_Lean_PersistentHashMap_insert___redArg(x_55, x_56, x_52, x_1, x_2);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(0, 9, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_45);
lean_ctor_set(x_58, 1, x_46);
lean_ctor_set(x_58, 2, x_47);
lean_ctor_set(x_58, 3, x_48);
lean_ctor_set(x_58, 4, x_49);
lean_ctor_set(x_58, 5, x_50);
lean_ctor_set(x_58, 6, x_51);
lean_ctor_set(x_58, 7, x_57);
lean_ctor_set(x_58, 8, x_53);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_41);
lean_ctor_set(x_59, 2, x_42);
lean_ctor_set(x_59, 3, x_43);
lean_ctor_set(x_59, 4, x_44);
x_60 = lean_st_ref_set(x_3, x_59, x_8);
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
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
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
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
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
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec_ref(x_11);
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
lean_dec_ref(x_1);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec_ref(x_14);
x_18 = l_Lean_Meta_mkFreshLevelMVar(x_2, x_3, x_4, x_5, x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
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
lean_dec_ref(x_14);
x_28 = l_Lean_Meta_throwTypeExpected___redArg(x_1, x_2, x_3, x_4, x_5, x_27);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_10);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_10, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_11, 0);
lean_inc(x_35);
lean_dec_ref(x_11);
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
lean_dec_ref(x_11);
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
lean_dec_ref(x_10);
x_40 = l_Lean_Meta_throwTypeExpected___redArg(x_1, x_2, x_3, x_4, x_5, x_39);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_14 = lean_infer_type(x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_17 = l_Lean_Meta_getLevel(x_15, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
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
lean_dec_ref(x_17);
x_2 = x_12;
x_4 = x_22;
x_9 = x_23;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_17;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_9);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0), 8, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = 0;
x_11 = lean_box(0);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___redArg(x_10, x_11, x_1, x_9, x_3, x_10, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_23; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_8 = x_23;
goto block_22;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
lean_dec_ref(x_23);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed), 7, 0);
x_8 = 0;
x_9 = l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(x_1, x_7, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
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
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0), 8, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = 1;
x_12 = 0;
x_13 = lean_box(0);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), x_1, x_11, x_11, x_4, x_12, x_13, x_10, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = 0;
x_12 = 1;
x_13 = 1;
x_14 = l_Lean_Meta_mkForallFVars(x_1, x_9, x_11, x_12, x_11, x_13, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_14;
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed), 7, 0);
x_8 = 0;
x_9 = 1;
x_10 = l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(x_1, x_7, x_8, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___redArg(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_lambdaLetTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType_spec__0(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_1);
return x_8;
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
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwUnknownMVar___redArg___closed__2;
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
x_10 = l_Lean_Meta_throwUnknownMVar___redArg___closed__3;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___redArg(x_11, x_2, x_3, x_4, x_5, x_6);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_throwUnknownMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_throwUnknownMVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_inc_ref(x_11);
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
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_15);
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
lean_inc_ref(x_18);
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
lean_dec_ref(x_19);
x_22 = lean_ctor_get(x_21, 2);
lean_inc_ref(x_22);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_6);
lean_dec_ref(x_2);
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
lean_dec_ref(x_7);
x_10 = lean_ctor_get(x_9, 3);
lean_inc_ref(x_10);
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
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
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
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instHashableExprConfigCacheKey___private__1___boxed), 1, 0);
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
lean_dec_ref(x_9);
x_12 = lean_st_ref_get(x_4, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_14);
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
lean_dec_ref(x_22);
x_26 = lean_st_ref_take(x_4, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec_ref(x_26);
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
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_28, 2);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_28, 3);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_28, 4);
lean_inc_ref(x_60);
x_61 = lean_ctor_get(x_28, 5);
lean_inc_ref(x_61);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_70 = lean_ctor_get(x_21, 0);
lean_inc(x_70);
lean_dec_ref(x_21);
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
lean_inc_ref(x_72);
lean_dec_ref(x_14);
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
lean_dec_ref(x_76);
x_80 = lean_st_ref_take(x_4, x_78);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 1);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec_ref(x_80);
x_84 = lean_ctor_get(x_81, 0);
lean_inc_ref(x_84);
x_85 = lean_ctor_get(x_81, 2);
lean_inc(x_85);
x_86 = lean_ctor_get(x_81, 3);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_81, 4);
lean_inc_ref(x_87);
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
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_82, 1);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_82, 2);
lean_inc_ref(x_91);
x_92 = lean_ctor_get(x_82, 3);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_82, 4);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_82, 5);
lean_inc_ref(x_94);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_103 = lean_ctor_get(x_75, 0);
lean_inc(x_103);
lean_dec_ref(x_75);
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
lean_dec_ref(x_1);
x_105 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_105;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_47; lean_object* x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; 
x_170 = l_Lean_Meta_Context_config(x_2);
x_171 = lean_ctor_get_uint8(x_170, 9);
lean_dec_ref(x_170);
x_172 = 1;
x_173 = l_Lean_Meta_TransparencyMode_lt(x_171, x_172);
if (x_173 == 0)
{
x_47 = x_171;
goto block_169;
}
else
{
x_47 = x_172;
goto block_169;
}
block_46:
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Meta_Context_config(x_14);
lean_dec_ref(x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
uint8_t x_20; uint8_t x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = 1;
x_21 = 2;
lean_ctor_set_uint8(x_18, 12, x_20);
lean_ctor_set_uint8(x_18, 13, x_20);
lean_ctor_set_uint8(x_18, 14, x_21);
lean_ctor_set_uint8(x_18, 15, x_20);
lean_ctor_set_uint8(x_18, 16, x_20);
lean_ctor_set_uint8(x_18, 18, x_20);
x_22 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_18);
x_23 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set_uint64(x_23, sizeof(void*)*1, x_22);
x_24 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_12);
lean_ctor_set(x_24, 2, x_8);
lean_ctor_set(x_24, 3, x_10);
lean_ctor_set(x_24, 4, x_16);
lean_ctor_set(x_24, 5, x_11);
lean_ctor_set(x_24, 6, x_15);
lean_ctor_set_uint8(x_24, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_24, sizeof(void*)*7 + 1, x_7);
lean_ctor_set_uint8(x_24, sizeof(void*)*7 + 2, x_13);
x_25 = lean_apply_5(x_1, x_24, x_3, x_4, x_5, x_17);
return x_25;
}
else
{
uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_26 = lean_ctor_get_uint8(x_18, 0);
x_27 = lean_ctor_get_uint8(x_18, 1);
x_28 = lean_ctor_get_uint8(x_18, 2);
x_29 = lean_ctor_get_uint8(x_18, 3);
x_30 = lean_ctor_get_uint8(x_18, 4);
x_31 = lean_ctor_get_uint8(x_18, 5);
x_32 = lean_ctor_get_uint8(x_18, 6);
x_33 = lean_ctor_get_uint8(x_18, 7);
x_34 = lean_ctor_get_uint8(x_18, 8);
x_35 = lean_ctor_get_uint8(x_18, 9);
x_36 = lean_ctor_get_uint8(x_18, 10);
x_37 = lean_ctor_get_uint8(x_18, 11);
x_38 = lean_ctor_get_uint8(x_18, 17);
lean_dec(x_18);
x_39 = 1;
x_40 = 2;
x_41 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_41, 0, x_26);
lean_ctor_set_uint8(x_41, 1, x_27);
lean_ctor_set_uint8(x_41, 2, x_28);
lean_ctor_set_uint8(x_41, 3, x_29);
lean_ctor_set_uint8(x_41, 4, x_30);
lean_ctor_set_uint8(x_41, 5, x_31);
lean_ctor_set_uint8(x_41, 6, x_32);
lean_ctor_set_uint8(x_41, 7, x_33);
lean_ctor_set_uint8(x_41, 8, x_34);
lean_ctor_set_uint8(x_41, 9, x_35);
lean_ctor_set_uint8(x_41, 10, x_36);
lean_ctor_set_uint8(x_41, 11, x_37);
lean_ctor_set_uint8(x_41, 12, x_39);
lean_ctor_set_uint8(x_41, 13, x_39);
lean_ctor_set_uint8(x_41, 14, x_40);
lean_ctor_set_uint8(x_41, 15, x_39);
lean_ctor_set_uint8(x_41, 16, x_39);
lean_ctor_set_uint8(x_41, 17, x_38);
lean_ctor_set_uint8(x_41, 18, x_39);
x_42 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_41);
x_43 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set_uint64(x_43, sizeof(void*)*1, x_42);
x_44 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_12);
lean_ctor_set(x_44, 2, x_8);
lean_ctor_set(x_44, 3, x_10);
lean_ctor_set(x_44, 4, x_16);
lean_ctor_set(x_44, 5, x_11);
lean_ctor_set(x_44, 6, x_15);
lean_ctor_set_uint8(x_44, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_44, sizeof(void*)*7 + 1, x_7);
lean_ctor_set_uint8(x_44, sizeof(void*)*7 + 2, x_13);
x_45 = lean_apply_5(x_1, x_44, x_3, x_4, x_5, x_17);
return x_45;
}
}
block_169:
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_Meta_Context_config(x_2);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; uint64_t x_59; uint8_t x_60; 
x_50 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_2, 4);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 5);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 6);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
x_58 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 2);
lean_ctor_set_uint8(x_48, 9, x_47);
x_59 = l_Lean_Meta_Context_configKey(x_2);
x_60 = !lean_is_exclusive(x_2);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_61 = lean_ctor_get(x_2, 6);
lean_dec(x_61);
x_62 = lean_ctor_get(x_2, 5);
lean_dec(x_62);
x_63 = lean_ctor_get(x_2, 4);
lean_dec(x_63);
x_64 = lean_ctor_get(x_2, 3);
lean_dec(x_64);
x_65 = lean_ctor_get(x_2, 2);
lean_dec(x_65);
x_66 = lean_ctor_get(x_2, 1);
lean_dec(x_66);
x_67 = lean_ctor_get(x_2, 0);
lean_dec(x_67);
x_68 = 2;
x_69 = lean_uint64_shift_right(x_59, x_68);
x_70 = lean_uint64_shift_left(x_69, x_68);
x_71 = l_Lean_Meta_TransparencyMode_toUInt64(x_47);
x_72 = lean_uint64_lor(x_70, x_71);
x_73 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_73, 0, x_48);
lean_ctor_set_uint64(x_73, sizeof(void*)*1, x_72);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
lean_ctor_set(x_2, 0, x_73);
x_74 = l_Lean_Meta_getConfig___redArg(x_2, x_6);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_75, 13);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_75);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec_ref(x_74);
x_7 = x_57;
x_8 = x_52;
x_9 = x_50;
x_10 = x_53;
x_11 = x_55;
x_12 = x_51;
x_13 = x_58;
x_14 = x_2;
x_15 = x_56;
x_16 = x_54;
x_17 = x_77;
goto block_46;
}
else
{
uint8_t x_78; 
x_78 = lean_ctor_get_uint8(x_75, 12);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_75);
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
lean_dec_ref(x_74);
x_7 = x_57;
x_8 = x_52;
x_9 = x_50;
x_10 = x_53;
x_11 = x_55;
x_12 = x_51;
x_13 = x_58;
x_14 = x_2;
x_15 = x_56;
x_16 = x_54;
x_17 = x_79;
goto block_46;
}
else
{
uint8_t x_80; 
x_80 = lean_ctor_get_uint8(x_75, 15);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_75);
x_81 = lean_ctor_get(x_74, 1);
lean_inc(x_81);
lean_dec_ref(x_74);
x_7 = x_57;
x_8 = x_52;
x_9 = x_50;
x_10 = x_53;
x_11 = x_55;
x_12 = x_51;
x_13 = x_58;
x_14 = x_2;
x_15 = x_56;
x_16 = x_54;
x_17 = x_81;
goto block_46;
}
else
{
uint8_t x_82; 
x_82 = lean_ctor_get_uint8(x_75, 18);
if (x_82 == 0)
{
lean_object* x_83; 
lean_dec(x_75);
x_83 = lean_ctor_get(x_74, 1);
lean_inc(x_83);
lean_dec_ref(x_74);
x_7 = x_57;
x_8 = x_52;
x_9 = x_50;
x_10 = x_53;
x_11 = x_55;
x_12 = x_51;
x_13 = x_58;
x_14 = x_2;
x_15 = x_56;
x_16 = x_54;
x_17 = x_83;
goto block_46;
}
else
{
uint8_t x_84; 
x_84 = lean_ctor_get_uint8(x_75, 16);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_75);
x_85 = lean_ctor_get(x_74, 1);
lean_inc(x_85);
lean_dec_ref(x_74);
x_7 = x_57;
x_8 = x_52;
x_9 = x_50;
x_10 = x_53;
x_11 = x_55;
x_12 = x_51;
x_13 = x_58;
x_14 = x_2;
x_15 = x_56;
x_16 = x_54;
x_17 = x_85;
goto block_46;
}
else
{
lean_object* x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_74, 1);
lean_inc(x_86);
lean_dec_ref(x_74);
x_87 = lean_ctor_get_uint8(x_75, 14);
lean_dec(x_75);
x_88 = 2;
x_89 = l_Lean_Meta_instDecidableEqProjReductionKind(x_87, x_88);
if (x_89 == 0)
{
x_7 = x_57;
x_8 = x_52;
x_9 = x_50;
x_10 = x_53;
x_11 = x_55;
x_12 = x_51;
x_13 = x_58;
x_14 = x_2;
x_15 = x_56;
x_16 = x_54;
x_17 = x_86;
goto block_46;
}
else
{
lean_object* x_90; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
x_90 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_86);
return x_90;
}
}
}
}
}
}
}
else
{
uint64_t x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; uint64_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_2);
x_91 = 2;
x_92 = lean_uint64_shift_right(x_59, x_91);
x_93 = lean_uint64_shift_left(x_92, x_91);
x_94 = l_Lean_Meta_TransparencyMode_toUInt64(x_47);
x_95 = lean_uint64_lor(x_93, x_94);
x_96 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_96, 0, x_48);
lean_ctor_set_uint64(x_96, sizeof(void*)*1, x_95);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc_ref(x_52);
lean_inc(x_51);
x_97 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_51);
lean_ctor_set(x_97, 2, x_52);
lean_ctor_set(x_97, 3, x_53);
lean_ctor_set(x_97, 4, x_54);
lean_ctor_set(x_97, 5, x_55);
lean_ctor_set(x_97, 6, x_56);
lean_ctor_set_uint8(x_97, sizeof(void*)*7, x_50);
lean_ctor_set_uint8(x_97, sizeof(void*)*7 + 1, x_57);
lean_ctor_set_uint8(x_97, sizeof(void*)*7 + 2, x_58);
x_98 = l_Lean_Meta_getConfig___redArg(x_97, x_6);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get_uint8(x_99, 13);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_99);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec_ref(x_98);
x_7 = x_57;
x_8 = x_52;
x_9 = x_50;
x_10 = x_53;
x_11 = x_55;
x_12 = x_51;
x_13 = x_58;
x_14 = x_97;
x_15 = x_56;
x_16 = x_54;
x_17 = x_101;
goto block_46;
}
else
{
uint8_t x_102; 
x_102 = lean_ctor_get_uint8(x_99, 12);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_99);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_dec_ref(x_98);
x_7 = x_57;
x_8 = x_52;
x_9 = x_50;
x_10 = x_53;
x_11 = x_55;
x_12 = x_51;
x_13 = x_58;
x_14 = x_97;
x_15 = x_56;
x_16 = x_54;
x_17 = x_103;
goto block_46;
}
else
{
uint8_t x_104; 
x_104 = lean_ctor_get_uint8(x_99, 15);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_99);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec_ref(x_98);
x_7 = x_57;
x_8 = x_52;
x_9 = x_50;
x_10 = x_53;
x_11 = x_55;
x_12 = x_51;
x_13 = x_58;
x_14 = x_97;
x_15 = x_56;
x_16 = x_54;
x_17 = x_105;
goto block_46;
}
else
{
uint8_t x_106; 
x_106 = lean_ctor_get_uint8(x_99, 18);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_99);
x_107 = lean_ctor_get(x_98, 1);
lean_inc(x_107);
lean_dec_ref(x_98);
x_7 = x_57;
x_8 = x_52;
x_9 = x_50;
x_10 = x_53;
x_11 = x_55;
x_12 = x_51;
x_13 = x_58;
x_14 = x_97;
x_15 = x_56;
x_16 = x_54;
x_17 = x_107;
goto block_46;
}
else
{
uint8_t x_108; 
x_108 = lean_ctor_get_uint8(x_99, 16);
if (x_108 == 0)
{
lean_object* x_109; 
lean_dec(x_99);
x_109 = lean_ctor_get(x_98, 1);
lean_inc(x_109);
lean_dec_ref(x_98);
x_7 = x_57;
x_8 = x_52;
x_9 = x_50;
x_10 = x_53;
x_11 = x_55;
x_12 = x_51;
x_13 = x_58;
x_14 = x_97;
x_15 = x_56;
x_16 = x_54;
x_17 = x_109;
goto block_46;
}
else
{
lean_object* x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; 
x_110 = lean_ctor_get(x_98, 1);
lean_inc(x_110);
lean_dec_ref(x_98);
x_111 = lean_ctor_get_uint8(x_99, 14);
lean_dec(x_99);
x_112 = 2;
x_113 = l_Lean_Meta_instDecidableEqProjReductionKind(x_111, x_112);
if (x_113 == 0)
{
x_7 = x_57;
x_8 = x_52;
x_9 = x_50;
x_10 = x_53;
x_11 = x_55;
x_12 = x_51;
x_13 = x_58;
x_14 = x_97;
x_15 = x_56;
x_16 = x_54;
x_17 = x_110;
goto block_46;
}
else
{
lean_object* x_114; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
x_114 = lean_apply_5(x_1, x_97, x_3, x_4, x_5, x_110);
return x_114;
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
uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_141; lean_object* x_142; uint64_t x_143; lean_object* x_144; uint64_t x_145; uint64_t x_146; uint64_t x_147; uint64_t x_148; uint64_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_115 = lean_ctor_get_uint8(x_48, 0);
x_116 = lean_ctor_get_uint8(x_48, 1);
x_117 = lean_ctor_get_uint8(x_48, 2);
x_118 = lean_ctor_get_uint8(x_48, 3);
x_119 = lean_ctor_get_uint8(x_48, 4);
x_120 = lean_ctor_get_uint8(x_48, 5);
x_121 = lean_ctor_get_uint8(x_48, 6);
x_122 = lean_ctor_get_uint8(x_48, 7);
x_123 = lean_ctor_get_uint8(x_48, 8);
x_124 = lean_ctor_get_uint8(x_48, 10);
x_125 = lean_ctor_get_uint8(x_48, 11);
x_126 = lean_ctor_get_uint8(x_48, 12);
x_127 = lean_ctor_get_uint8(x_48, 13);
x_128 = lean_ctor_get_uint8(x_48, 14);
x_129 = lean_ctor_get_uint8(x_48, 15);
x_130 = lean_ctor_get_uint8(x_48, 16);
x_131 = lean_ctor_get_uint8(x_48, 17);
x_132 = lean_ctor_get_uint8(x_48, 18);
lean_dec(x_48);
x_133 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_134 = lean_ctor_get(x_2, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_2, 4);
lean_inc(x_137);
x_138 = lean_ctor_get(x_2, 5);
lean_inc(x_138);
x_139 = lean_ctor_get(x_2, 6);
lean_inc(x_139);
x_140 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
x_141 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 2);
x_142 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_142, 0, x_115);
lean_ctor_set_uint8(x_142, 1, x_116);
lean_ctor_set_uint8(x_142, 2, x_117);
lean_ctor_set_uint8(x_142, 3, x_118);
lean_ctor_set_uint8(x_142, 4, x_119);
lean_ctor_set_uint8(x_142, 5, x_120);
lean_ctor_set_uint8(x_142, 6, x_121);
lean_ctor_set_uint8(x_142, 7, x_122);
lean_ctor_set_uint8(x_142, 8, x_123);
lean_ctor_set_uint8(x_142, 9, x_47);
lean_ctor_set_uint8(x_142, 10, x_124);
lean_ctor_set_uint8(x_142, 11, x_125);
lean_ctor_set_uint8(x_142, 12, x_126);
lean_ctor_set_uint8(x_142, 13, x_127);
lean_ctor_set_uint8(x_142, 14, x_128);
lean_ctor_set_uint8(x_142, 15, x_129);
lean_ctor_set_uint8(x_142, 16, x_130);
lean_ctor_set_uint8(x_142, 17, x_131);
lean_ctor_set_uint8(x_142, 18, x_132);
x_143 = l_Lean_Meta_Context_configKey(x_2);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_144 = x_2;
} else {
 lean_dec_ref(x_2);
 x_144 = lean_box(0);
}
x_145 = 2;
x_146 = lean_uint64_shift_right(x_143, x_145);
x_147 = lean_uint64_shift_left(x_146, x_145);
x_148 = l_Lean_Meta_TransparencyMode_toUInt64(x_47);
x_149 = lean_uint64_lor(x_147, x_148);
x_150 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_150, 0, x_142);
lean_ctor_set_uint64(x_150, sizeof(void*)*1, x_149);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc_ref(x_136);
lean_inc_ref(x_135);
lean_inc(x_134);
if (lean_is_scalar(x_144)) {
 x_151 = lean_alloc_ctor(0, 7, 3);
} else {
 x_151 = x_144;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_134);
lean_ctor_set(x_151, 2, x_135);
lean_ctor_set(x_151, 3, x_136);
lean_ctor_set(x_151, 4, x_137);
lean_ctor_set(x_151, 5, x_138);
lean_ctor_set(x_151, 6, x_139);
lean_ctor_set_uint8(x_151, sizeof(void*)*7, x_133);
lean_ctor_set_uint8(x_151, sizeof(void*)*7 + 1, x_140);
lean_ctor_set_uint8(x_151, sizeof(void*)*7 + 2, x_141);
x_152 = l_Lean_Meta_getConfig___redArg(x_151, x_6);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get_uint8(x_153, 13);
if (x_154 == 0)
{
lean_object* x_155; 
lean_dec(x_153);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_dec_ref(x_152);
x_7 = x_140;
x_8 = x_135;
x_9 = x_133;
x_10 = x_136;
x_11 = x_138;
x_12 = x_134;
x_13 = x_141;
x_14 = x_151;
x_15 = x_139;
x_16 = x_137;
x_17 = x_155;
goto block_46;
}
else
{
uint8_t x_156; 
x_156 = lean_ctor_get_uint8(x_153, 12);
if (x_156 == 0)
{
lean_object* x_157; 
lean_dec(x_153);
x_157 = lean_ctor_get(x_152, 1);
lean_inc(x_157);
lean_dec_ref(x_152);
x_7 = x_140;
x_8 = x_135;
x_9 = x_133;
x_10 = x_136;
x_11 = x_138;
x_12 = x_134;
x_13 = x_141;
x_14 = x_151;
x_15 = x_139;
x_16 = x_137;
x_17 = x_157;
goto block_46;
}
else
{
uint8_t x_158; 
x_158 = lean_ctor_get_uint8(x_153, 15);
if (x_158 == 0)
{
lean_object* x_159; 
lean_dec(x_153);
x_159 = lean_ctor_get(x_152, 1);
lean_inc(x_159);
lean_dec_ref(x_152);
x_7 = x_140;
x_8 = x_135;
x_9 = x_133;
x_10 = x_136;
x_11 = x_138;
x_12 = x_134;
x_13 = x_141;
x_14 = x_151;
x_15 = x_139;
x_16 = x_137;
x_17 = x_159;
goto block_46;
}
else
{
uint8_t x_160; 
x_160 = lean_ctor_get_uint8(x_153, 18);
if (x_160 == 0)
{
lean_object* x_161; 
lean_dec(x_153);
x_161 = lean_ctor_get(x_152, 1);
lean_inc(x_161);
lean_dec_ref(x_152);
x_7 = x_140;
x_8 = x_135;
x_9 = x_133;
x_10 = x_136;
x_11 = x_138;
x_12 = x_134;
x_13 = x_141;
x_14 = x_151;
x_15 = x_139;
x_16 = x_137;
x_17 = x_161;
goto block_46;
}
else
{
uint8_t x_162; 
x_162 = lean_ctor_get_uint8(x_153, 16);
if (x_162 == 0)
{
lean_object* x_163; 
lean_dec(x_153);
x_163 = lean_ctor_get(x_152, 1);
lean_inc(x_163);
lean_dec_ref(x_152);
x_7 = x_140;
x_8 = x_135;
x_9 = x_133;
x_10 = x_136;
x_11 = x_138;
x_12 = x_134;
x_13 = x_141;
x_14 = x_151;
x_15 = x_139;
x_16 = x_137;
x_17 = x_163;
goto block_46;
}
else
{
lean_object* x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; 
x_164 = lean_ctor_get(x_152, 1);
lean_inc(x_164);
lean_dec_ref(x_152);
x_165 = lean_ctor_get_uint8(x_153, 14);
lean_dec(x_153);
x_166 = 2;
x_167 = l_Lean_Meta_instDecidableEqProjReductionKind(x_165, x_166);
if (x_167 == 0)
{
x_7 = x_140;
x_8 = x_135;
x_9 = x_133;
x_10 = x_136;
x_11 = x_138;
x_12 = x_134;
x_13 = x_141;
x_14 = x_151;
x_15 = x_139;
x_16 = x_137;
x_17 = x_164;
goto block_46;
}
else
{
lean_object* x_168; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec_ref(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
x_168 = lean_apply_5(x_1, x_151, x_3, x_4, x_5, x_164);
return x_168;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withInferTypeConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_48; lean_object* x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; 
x_171 = l_Lean_Meta_Context_config(x_3);
x_172 = lean_ctor_get_uint8(x_171, 9);
lean_dec_ref(x_171);
x_173 = 1;
x_174 = l_Lean_Meta_TransparencyMode_lt(x_172, x_173);
if (x_174 == 0)
{
x_48 = x_172;
goto block_170;
}
else
{
x_48 = x_173;
goto block_170;
}
block_47:
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Meta_Context_config(x_15);
lean_dec_ref(x_15);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
uint8_t x_21; uint8_t x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = 1;
x_22 = 2;
lean_ctor_set_uint8(x_19, 12, x_21);
lean_ctor_set_uint8(x_19, 13, x_21);
lean_ctor_set_uint8(x_19, 14, x_22);
lean_ctor_set_uint8(x_19, 15, x_21);
lean_ctor_set_uint8(x_19, 16, x_21);
lean_ctor_set_uint8(x_19, 18, x_21);
x_23 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_19);
x_24 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set_uint64(x_24, sizeof(void*)*1, x_23);
x_25 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_13);
lean_ctor_set(x_25, 2, x_9);
lean_ctor_set(x_25, 3, x_11);
lean_ctor_set(x_25, 4, x_17);
lean_ctor_set(x_25, 5, x_12);
lean_ctor_set(x_25, 6, x_16);
lean_ctor_set_uint8(x_25, sizeof(void*)*7, x_10);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 1, x_8);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 2, x_14);
x_26 = lean_apply_5(x_2, x_25, x_4, x_5, x_6, x_18);
return x_26;
}
else
{
uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_27 = lean_ctor_get_uint8(x_19, 0);
x_28 = lean_ctor_get_uint8(x_19, 1);
x_29 = lean_ctor_get_uint8(x_19, 2);
x_30 = lean_ctor_get_uint8(x_19, 3);
x_31 = lean_ctor_get_uint8(x_19, 4);
x_32 = lean_ctor_get_uint8(x_19, 5);
x_33 = lean_ctor_get_uint8(x_19, 6);
x_34 = lean_ctor_get_uint8(x_19, 7);
x_35 = lean_ctor_get_uint8(x_19, 8);
x_36 = lean_ctor_get_uint8(x_19, 9);
x_37 = lean_ctor_get_uint8(x_19, 10);
x_38 = lean_ctor_get_uint8(x_19, 11);
x_39 = lean_ctor_get_uint8(x_19, 17);
lean_dec(x_19);
x_40 = 1;
x_41 = 2;
x_42 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_42, 0, x_27);
lean_ctor_set_uint8(x_42, 1, x_28);
lean_ctor_set_uint8(x_42, 2, x_29);
lean_ctor_set_uint8(x_42, 3, x_30);
lean_ctor_set_uint8(x_42, 4, x_31);
lean_ctor_set_uint8(x_42, 5, x_32);
lean_ctor_set_uint8(x_42, 6, x_33);
lean_ctor_set_uint8(x_42, 7, x_34);
lean_ctor_set_uint8(x_42, 8, x_35);
lean_ctor_set_uint8(x_42, 9, x_36);
lean_ctor_set_uint8(x_42, 10, x_37);
lean_ctor_set_uint8(x_42, 11, x_38);
lean_ctor_set_uint8(x_42, 12, x_40);
lean_ctor_set_uint8(x_42, 13, x_40);
lean_ctor_set_uint8(x_42, 14, x_41);
lean_ctor_set_uint8(x_42, 15, x_40);
lean_ctor_set_uint8(x_42, 16, x_40);
lean_ctor_set_uint8(x_42, 17, x_39);
lean_ctor_set_uint8(x_42, 18, x_40);
x_43 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_42);
x_44 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set_uint64(x_44, sizeof(void*)*1, x_43);
x_45 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_13);
lean_ctor_set(x_45, 2, x_9);
lean_ctor_set(x_45, 3, x_11);
lean_ctor_set(x_45, 4, x_17);
lean_ctor_set(x_45, 5, x_12);
lean_ctor_set(x_45, 6, x_16);
lean_ctor_set_uint8(x_45, sizeof(void*)*7, x_10);
lean_ctor_set_uint8(x_45, sizeof(void*)*7 + 1, x_8);
lean_ctor_set_uint8(x_45, sizeof(void*)*7 + 2, x_14);
x_46 = lean_apply_5(x_2, x_45, x_4, x_5, x_6, x_18);
return x_46;
}
}
block_170:
{
lean_object* x_49; uint8_t x_50; 
x_49 = l_Lean_Meta_Context_config(x_3);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; uint64_t x_60; uint8_t x_61; 
x_51 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_3, 4);
lean_inc(x_55);
x_56 = lean_ctor_get(x_3, 5);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 6);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_59 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 2);
lean_ctor_set_uint8(x_49, 9, x_48);
x_60 = l_Lean_Meta_Context_configKey(x_3);
x_61 = !lean_is_exclusive(x_3);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_62 = lean_ctor_get(x_3, 6);
lean_dec(x_62);
x_63 = lean_ctor_get(x_3, 5);
lean_dec(x_63);
x_64 = lean_ctor_get(x_3, 4);
lean_dec(x_64);
x_65 = lean_ctor_get(x_3, 3);
lean_dec(x_65);
x_66 = lean_ctor_get(x_3, 2);
lean_dec(x_66);
x_67 = lean_ctor_get(x_3, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_3, 0);
lean_dec(x_68);
x_69 = 2;
x_70 = lean_uint64_shift_right(x_60, x_69);
x_71 = lean_uint64_shift_left(x_70, x_69);
x_72 = l_Lean_Meta_TransparencyMode_toUInt64(x_48);
x_73 = lean_uint64_lor(x_71, x_72);
x_74 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_74, 0, x_49);
lean_ctor_set_uint64(x_74, sizeof(void*)*1, x_73);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc_ref(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_ctor_set(x_3, 0, x_74);
x_75 = l_Lean_Meta_getConfig___redArg(x_3, x_7);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get_uint8(x_76, 13);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_76);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec_ref(x_75);
x_8 = x_58;
x_9 = x_53;
x_10 = x_51;
x_11 = x_54;
x_12 = x_56;
x_13 = x_52;
x_14 = x_59;
x_15 = x_3;
x_16 = x_57;
x_17 = x_55;
x_18 = x_78;
goto block_47;
}
else
{
uint8_t x_79; 
x_79 = lean_ctor_get_uint8(x_76, 12);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_76);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
lean_dec_ref(x_75);
x_8 = x_58;
x_9 = x_53;
x_10 = x_51;
x_11 = x_54;
x_12 = x_56;
x_13 = x_52;
x_14 = x_59;
x_15 = x_3;
x_16 = x_57;
x_17 = x_55;
x_18 = x_80;
goto block_47;
}
else
{
uint8_t x_81; 
x_81 = lean_ctor_get_uint8(x_76, 15);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_76);
x_82 = lean_ctor_get(x_75, 1);
lean_inc(x_82);
lean_dec_ref(x_75);
x_8 = x_58;
x_9 = x_53;
x_10 = x_51;
x_11 = x_54;
x_12 = x_56;
x_13 = x_52;
x_14 = x_59;
x_15 = x_3;
x_16 = x_57;
x_17 = x_55;
x_18 = x_82;
goto block_47;
}
else
{
uint8_t x_83; 
x_83 = lean_ctor_get_uint8(x_76, 18);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_76);
x_84 = lean_ctor_get(x_75, 1);
lean_inc(x_84);
lean_dec_ref(x_75);
x_8 = x_58;
x_9 = x_53;
x_10 = x_51;
x_11 = x_54;
x_12 = x_56;
x_13 = x_52;
x_14 = x_59;
x_15 = x_3;
x_16 = x_57;
x_17 = x_55;
x_18 = x_84;
goto block_47;
}
else
{
uint8_t x_85; 
x_85 = lean_ctor_get_uint8(x_76, 16);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_76);
x_86 = lean_ctor_get(x_75, 1);
lean_inc(x_86);
lean_dec_ref(x_75);
x_8 = x_58;
x_9 = x_53;
x_10 = x_51;
x_11 = x_54;
x_12 = x_56;
x_13 = x_52;
x_14 = x_59;
x_15 = x_3;
x_16 = x_57;
x_17 = x_55;
x_18 = x_86;
goto block_47;
}
else
{
lean_object* x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_75, 1);
lean_inc(x_87);
lean_dec_ref(x_75);
x_88 = lean_ctor_get_uint8(x_76, 14);
lean_dec(x_76);
x_89 = 2;
x_90 = l_Lean_Meta_instDecidableEqProjReductionKind(x_88, x_89);
if (x_90 == 0)
{
x_8 = x_58;
x_9 = x_53;
x_10 = x_51;
x_11 = x_54;
x_12 = x_56;
x_13 = x_52;
x_14 = x_59;
x_15 = x_3;
x_16 = x_57;
x_17 = x_55;
x_18 = x_87;
goto block_47;
}
else
{
lean_object* x_91; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
x_91 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_87);
return x_91;
}
}
}
}
}
}
}
else
{
uint64_t x_92; uint64_t x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_dec(x_3);
x_92 = 2;
x_93 = lean_uint64_shift_right(x_60, x_92);
x_94 = lean_uint64_shift_left(x_93, x_92);
x_95 = l_Lean_Meta_TransparencyMode_toUInt64(x_48);
x_96 = lean_uint64_lor(x_94, x_95);
x_97 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_97, 0, x_49);
lean_ctor_set_uint64(x_97, sizeof(void*)*1, x_96);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc_ref(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
x_98 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_52);
lean_ctor_set(x_98, 2, x_53);
lean_ctor_set(x_98, 3, x_54);
lean_ctor_set(x_98, 4, x_55);
lean_ctor_set(x_98, 5, x_56);
lean_ctor_set(x_98, 6, x_57);
lean_ctor_set_uint8(x_98, sizeof(void*)*7, x_51);
lean_ctor_set_uint8(x_98, sizeof(void*)*7 + 1, x_58);
lean_ctor_set_uint8(x_98, sizeof(void*)*7 + 2, x_59);
x_99 = l_Lean_Meta_getConfig___redArg(x_98, x_7);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get_uint8(x_100, 13);
if (x_101 == 0)
{
lean_object* x_102; 
lean_dec(x_100);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec_ref(x_99);
x_8 = x_58;
x_9 = x_53;
x_10 = x_51;
x_11 = x_54;
x_12 = x_56;
x_13 = x_52;
x_14 = x_59;
x_15 = x_98;
x_16 = x_57;
x_17 = x_55;
x_18 = x_102;
goto block_47;
}
else
{
uint8_t x_103; 
x_103 = lean_ctor_get_uint8(x_100, 12);
if (x_103 == 0)
{
lean_object* x_104; 
lean_dec(x_100);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_dec_ref(x_99);
x_8 = x_58;
x_9 = x_53;
x_10 = x_51;
x_11 = x_54;
x_12 = x_56;
x_13 = x_52;
x_14 = x_59;
x_15 = x_98;
x_16 = x_57;
x_17 = x_55;
x_18 = x_104;
goto block_47;
}
else
{
uint8_t x_105; 
x_105 = lean_ctor_get_uint8(x_100, 15);
if (x_105 == 0)
{
lean_object* x_106; 
lean_dec(x_100);
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
lean_dec_ref(x_99);
x_8 = x_58;
x_9 = x_53;
x_10 = x_51;
x_11 = x_54;
x_12 = x_56;
x_13 = x_52;
x_14 = x_59;
x_15 = x_98;
x_16 = x_57;
x_17 = x_55;
x_18 = x_106;
goto block_47;
}
else
{
uint8_t x_107; 
x_107 = lean_ctor_get_uint8(x_100, 18);
if (x_107 == 0)
{
lean_object* x_108; 
lean_dec(x_100);
x_108 = lean_ctor_get(x_99, 1);
lean_inc(x_108);
lean_dec_ref(x_99);
x_8 = x_58;
x_9 = x_53;
x_10 = x_51;
x_11 = x_54;
x_12 = x_56;
x_13 = x_52;
x_14 = x_59;
x_15 = x_98;
x_16 = x_57;
x_17 = x_55;
x_18 = x_108;
goto block_47;
}
else
{
uint8_t x_109; 
x_109 = lean_ctor_get_uint8(x_100, 16);
if (x_109 == 0)
{
lean_object* x_110; 
lean_dec(x_100);
x_110 = lean_ctor_get(x_99, 1);
lean_inc(x_110);
lean_dec_ref(x_99);
x_8 = x_58;
x_9 = x_53;
x_10 = x_51;
x_11 = x_54;
x_12 = x_56;
x_13 = x_52;
x_14 = x_59;
x_15 = x_98;
x_16 = x_57;
x_17 = x_55;
x_18 = x_110;
goto block_47;
}
else
{
lean_object* x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; 
x_111 = lean_ctor_get(x_99, 1);
lean_inc(x_111);
lean_dec_ref(x_99);
x_112 = lean_ctor_get_uint8(x_100, 14);
lean_dec(x_100);
x_113 = 2;
x_114 = l_Lean_Meta_instDecidableEqProjReductionKind(x_112, x_113);
if (x_114 == 0)
{
x_8 = x_58;
x_9 = x_53;
x_10 = x_51;
x_11 = x_54;
x_12 = x_56;
x_13 = x_52;
x_14 = x_59;
x_15 = x_98;
x_16 = x_57;
x_17 = x_55;
x_18 = x_111;
goto block_47;
}
else
{
lean_object* x_115; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec_ref(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
x_115 = lean_apply_5(x_2, x_98, x_4, x_5, x_6, x_111);
return x_115;
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
uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_142; lean_object* x_143; uint64_t x_144; lean_object* x_145; uint64_t x_146; uint64_t x_147; uint64_t x_148; uint64_t x_149; uint64_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_116 = lean_ctor_get_uint8(x_49, 0);
x_117 = lean_ctor_get_uint8(x_49, 1);
x_118 = lean_ctor_get_uint8(x_49, 2);
x_119 = lean_ctor_get_uint8(x_49, 3);
x_120 = lean_ctor_get_uint8(x_49, 4);
x_121 = lean_ctor_get_uint8(x_49, 5);
x_122 = lean_ctor_get_uint8(x_49, 6);
x_123 = lean_ctor_get_uint8(x_49, 7);
x_124 = lean_ctor_get_uint8(x_49, 8);
x_125 = lean_ctor_get_uint8(x_49, 10);
x_126 = lean_ctor_get_uint8(x_49, 11);
x_127 = lean_ctor_get_uint8(x_49, 12);
x_128 = lean_ctor_get_uint8(x_49, 13);
x_129 = lean_ctor_get_uint8(x_49, 14);
x_130 = lean_ctor_get_uint8(x_49, 15);
x_131 = lean_ctor_get_uint8(x_49, 16);
x_132 = lean_ctor_get_uint8(x_49, 17);
x_133 = lean_ctor_get_uint8(x_49, 18);
lean_dec(x_49);
x_134 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_135 = lean_ctor_get(x_3, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_3, 3);
lean_inc_ref(x_137);
x_138 = lean_ctor_get(x_3, 4);
lean_inc(x_138);
x_139 = lean_ctor_get(x_3, 5);
lean_inc(x_139);
x_140 = lean_ctor_get(x_3, 6);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 1);
x_142 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 2);
x_143 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_143, 0, x_116);
lean_ctor_set_uint8(x_143, 1, x_117);
lean_ctor_set_uint8(x_143, 2, x_118);
lean_ctor_set_uint8(x_143, 3, x_119);
lean_ctor_set_uint8(x_143, 4, x_120);
lean_ctor_set_uint8(x_143, 5, x_121);
lean_ctor_set_uint8(x_143, 6, x_122);
lean_ctor_set_uint8(x_143, 7, x_123);
lean_ctor_set_uint8(x_143, 8, x_124);
lean_ctor_set_uint8(x_143, 9, x_48);
lean_ctor_set_uint8(x_143, 10, x_125);
lean_ctor_set_uint8(x_143, 11, x_126);
lean_ctor_set_uint8(x_143, 12, x_127);
lean_ctor_set_uint8(x_143, 13, x_128);
lean_ctor_set_uint8(x_143, 14, x_129);
lean_ctor_set_uint8(x_143, 15, x_130);
lean_ctor_set_uint8(x_143, 16, x_131);
lean_ctor_set_uint8(x_143, 17, x_132);
lean_ctor_set_uint8(x_143, 18, x_133);
x_144 = l_Lean_Meta_Context_configKey(x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 x_145 = x_3;
} else {
 lean_dec_ref(x_3);
 x_145 = lean_box(0);
}
x_146 = 2;
x_147 = lean_uint64_shift_right(x_144, x_146);
x_148 = lean_uint64_shift_left(x_147, x_146);
x_149 = l_Lean_Meta_TransparencyMode_toUInt64(x_48);
x_150 = lean_uint64_lor(x_148, x_149);
x_151 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_151, 0, x_143);
lean_ctor_set_uint64(x_151, sizeof(void*)*1, x_150);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc_ref(x_137);
lean_inc_ref(x_136);
lean_inc(x_135);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(0, 7, 3);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_135);
lean_ctor_set(x_152, 2, x_136);
lean_ctor_set(x_152, 3, x_137);
lean_ctor_set(x_152, 4, x_138);
lean_ctor_set(x_152, 5, x_139);
lean_ctor_set(x_152, 6, x_140);
lean_ctor_set_uint8(x_152, sizeof(void*)*7, x_134);
lean_ctor_set_uint8(x_152, sizeof(void*)*7 + 1, x_141);
lean_ctor_set_uint8(x_152, sizeof(void*)*7 + 2, x_142);
x_153 = l_Lean_Meta_getConfig___redArg(x_152, x_7);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get_uint8(x_154, 13);
if (x_155 == 0)
{
lean_object* x_156; 
lean_dec(x_154);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec_ref(x_153);
x_8 = x_141;
x_9 = x_136;
x_10 = x_134;
x_11 = x_137;
x_12 = x_139;
x_13 = x_135;
x_14 = x_142;
x_15 = x_152;
x_16 = x_140;
x_17 = x_138;
x_18 = x_156;
goto block_47;
}
else
{
uint8_t x_157; 
x_157 = lean_ctor_get_uint8(x_154, 12);
if (x_157 == 0)
{
lean_object* x_158; 
lean_dec(x_154);
x_158 = lean_ctor_get(x_153, 1);
lean_inc(x_158);
lean_dec_ref(x_153);
x_8 = x_141;
x_9 = x_136;
x_10 = x_134;
x_11 = x_137;
x_12 = x_139;
x_13 = x_135;
x_14 = x_142;
x_15 = x_152;
x_16 = x_140;
x_17 = x_138;
x_18 = x_158;
goto block_47;
}
else
{
uint8_t x_159; 
x_159 = lean_ctor_get_uint8(x_154, 15);
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec(x_154);
x_160 = lean_ctor_get(x_153, 1);
lean_inc(x_160);
lean_dec_ref(x_153);
x_8 = x_141;
x_9 = x_136;
x_10 = x_134;
x_11 = x_137;
x_12 = x_139;
x_13 = x_135;
x_14 = x_142;
x_15 = x_152;
x_16 = x_140;
x_17 = x_138;
x_18 = x_160;
goto block_47;
}
else
{
uint8_t x_161; 
x_161 = lean_ctor_get_uint8(x_154, 18);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_154);
x_162 = lean_ctor_get(x_153, 1);
lean_inc(x_162);
lean_dec_ref(x_153);
x_8 = x_141;
x_9 = x_136;
x_10 = x_134;
x_11 = x_137;
x_12 = x_139;
x_13 = x_135;
x_14 = x_142;
x_15 = x_152;
x_16 = x_140;
x_17 = x_138;
x_18 = x_162;
goto block_47;
}
else
{
uint8_t x_163; 
x_163 = lean_ctor_get_uint8(x_154, 16);
if (x_163 == 0)
{
lean_object* x_164; 
lean_dec(x_154);
x_164 = lean_ctor_get(x_153, 1);
lean_inc(x_164);
lean_dec_ref(x_153);
x_8 = x_141;
x_9 = x_136;
x_10 = x_134;
x_11 = x_137;
x_12 = x_139;
x_13 = x_135;
x_14 = x_142;
x_15 = x_152;
x_16 = x_140;
x_17 = x_138;
x_18 = x_164;
goto block_47;
}
else
{
lean_object* x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; 
x_165 = lean_ctor_get(x_153, 1);
lean_inc(x_165);
lean_dec_ref(x_153);
x_166 = lean_ctor_get_uint8(x_154, 14);
lean_dec(x_154);
x_167 = 2;
x_168 = l_Lean_Meta_instDecidableEqProjReductionKind(x_166, x_167);
if (x_168 == 0)
{
x_8 = x_141;
x_9 = x_136;
x_10 = x_134;
x_11 = x_137;
x_12 = x_139;
x_13 = x_135;
x_14 = x_142;
x_15 = x_152;
x_16 = x_140;
x_17 = x_138;
x_18 = x_165;
goto block_47;
}
else
{
lean_object* x_169; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec_ref(x_137);
lean_dec_ref(x_136);
lean_dec(x_135);
x_169 = lean_apply_5(x_2, x_152, x_4, x_5, x_6, x_165);
return x_169;
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
lean_dec_ref(x_1);
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
x_14 = l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___redArg(x_13, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(x_15, x_2, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_16;
}
case 2:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec_ref(x_1);
x_18 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(x_17, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_18;
}
case 3:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
x_25 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_24, x_23, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_28);
x_31 = lean_st_ref_get(x_3, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc_ref(x_33);
lean_dec(x_32);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_31, 1);
x_36 = lean_ctor_get(x_31, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_37);
lean_dec_ref(x_33);
x_38 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0;
x_39 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1;
lean_inc(x_29);
x_40 = l_Lean_PersistentHashMap_find_x3f___redArg(x_38, x_39, x_37, x_29);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_free_object(x_31);
x_41 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_26, x_23, x_2, x_3, x_4, x_5, x_35);
lean_dec(x_5);
lean_dec_ref(x_2);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
x_44 = l_Lean_Expr_hasMVar(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec_ref(x_41);
x_45 = lean_st_ref_take(x_3, x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec_ref(x_45);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_46, 1);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_42);
x_53 = l_Lean_PersistentHashMap_insert___redArg(x_38, x_39, x_52, x_29, x_42);
lean_ctor_set(x_47, 0, x_53);
x_54 = lean_st_ref_set(x_3, x_46, x_48);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set(x_54, 0, x_42);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_42);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_59 = lean_ctor_get(x_47, 0);
x_60 = lean_ctor_get(x_47, 1);
x_61 = lean_ctor_get(x_47, 2);
x_62 = lean_ctor_get(x_47, 3);
x_63 = lean_ctor_get(x_47, 4);
x_64 = lean_ctor_get(x_47, 5);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_47);
lean_inc(x_42);
x_65 = l_Lean_PersistentHashMap_insert___redArg(x_38, x_39, x_59, x_29, x_42);
x_66 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_60);
lean_ctor_set(x_66, 2, x_61);
lean_ctor_set(x_66, 3, x_62);
lean_ctor_set(x_66, 4, x_63);
lean_ctor_set(x_66, 5, x_64);
lean_ctor_set(x_46, 1, x_66);
x_67 = lean_st_ref_set(x_3, x_46, x_48);
lean_dec(x_3);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_42);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_71 = lean_ctor_get(x_46, 0);
x_72 = lean_ctor_get(x_46, 2);
x_73 = lean_ctor_get(x_46, 3);
x_74 = lean_ctor_get(x_46, 4);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_46);
x_75 = lean_ctor_get(x_47, 0);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_47, 1);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_47, 2);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_47, 3);
lean_inc_ref(x_78);
x_79 = lean_ctor_get(x_47, 4);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_47, 5);
lean_inc_ref(x_80);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 lean_ctor_release(x_47, 4);
 lean_ctor_release(x_47, 5);
 x_81 = x_47;
} else {
 lean_dec_ref(x_47);
 x_81 = lean_box(0);
}
lean_inc(x_42);
x_82 = l_Lean_PersistentHashMap_insert___redArg(x_38, x_39, x_75, x_29, x_42);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 6, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_76);
lean_ctor_set(x_83, 2, x_77);
lean_ctor_set(x_83, 3, x_78);
lean_ctor_set(x_83, 4, x_79);
lean_ctor_set(x_83, 5, x_80);
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_71);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_72);
lean_ctor_set(x_84, 3, x_73);
lean_ctor_set(x_84, 4, x_74);
x_85 = lean_st_ref_set(x_3, x_84, x_48);
lean_dec(x_3);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_42);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_29);
lean_dec(x_3);
return x_41;
}
}
else
{
lean_dec(x_29);
lean_dec(x_3);
return x_41;
}
}
else
{
lean_object* x_89; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec_ref(x_23);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_89 = lean_ctor_get(x_40, 0);
lean_inc(x_89);
lean_dec_ref(x_40);
lean_ctor_set(x_31, 0, x_89);
return x_31;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_31, 1);
lean_inc(x_90);
lean_dec(x_31);
x_91 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_91);
lean_dec_ref(x_33);
x_92 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0;
x_93 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1;
lean_inc(x_29);
x_94 = l_Lean_PersistentHashMap_find_x3f___redArg(x_92, x_93, x_91, x_29);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_26, x_23, x_2, x_3, x_4, x_5, x_90);
lean_dec(x_5);
lean_dec_ref(x_2);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
x_98 = l_Lean_Expr_hasMVar(x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_95);
x_99 = lean_st_ref_take(x_3, x_97);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 1);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec_ref(x_99);
x_103 = lean_ctor_get(x_100, 0);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_100, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_100, 3);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_100, 4);
lean_inc_ref(x_106);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 lean_ctor_release(x_100, 2);
 lean_ctor_release(x_100, 3);
 lean_ctor_release(x_100, 4);
 x_107 = x_100;
} else {
 lean_dec_ref(x_100);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_101, 0);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_101, 1);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_101, 2);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_101, 3);
lean_inc_ref(x_111);
x_112 = lean_ctor_get(x_101, 4);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_101, 5);
lean_inc_ref(x_113);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 lean_ctor_release(x_101, 3);
 lean_ctor_release(x_101, 4);
 lean_ctor_release(x_101, 5);
 x_114 = x_101;
} else {
 lean_dec_ref(x_101);
 x_114 = lean_box(0);
}
lean_inc(x_96);
x_115 = l_Lean_PersistentHashMap_insert___redArg(x_92, x_93, x_108, x_29, x_96);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 6, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_109);
lean_ctor_set(x_116, 2, x_110);
lean_ctor_set(x_116, 3, x_111);
lean_ctor_set(x_116, 4, x_112);
lean_ctor_set(x_116, 5, x_113);
if (lean_is_scalar(x_107)) {
 x_117 = lean_alloc_ctor(0, 5, 0);
} else {
 x_117 = x_107;
}
lean_ctor_set(x_117, 0, x_103);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_117, 2, x_104);
lean_ctor_set(x_117, 3, x_105);
lean_ctor_set(x_117, 4, x_106);
x_118 = lean_st_ref_set(x_3, x_117, x_102);
lean_dec(x_3);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_96);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
else
{
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_29);
lean_dec(x_3);
return x_95;
}
}
else
{
lean_dec(x_29);
lean_dec(x_3);
return x_95;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec_ref(x_23);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_122 = lean_ctor_get(x_94, 0);
lean_inc(x_122);
lean_dec_ref(x_94);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_90);
return x_123;
}
}
}
else
{
lean_object* x_124; 
lean_dec_ref(x_1);
x_124 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_26, x_23, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_124;
}
}
}
case 5:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_125 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_125);
x_126 = l_Lean_Expr_getAppFn(x_125);
lean_dec_ref(x_125);
x_127 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___closed__0;
x_128 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_128);
x_129 = lean_mk_array(x_128, x_127);
x_130 = lean_unsigned_to_nat(1u);
x_131 = lean_nat_sub(x_128, x_130);
lean_dec(x_128);
lean_inc_ref(x_1);
x_132 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_129, x_131);
x_133 = l_Lean_Expr_hasMVar(x_1);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_134 = l_Lean_Meta_mkExprConfigCacheKey___redArg(x_1, x_2, x_6);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec_ref(x_134);
x_137 = lean_st_ref_get(x_3, x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_138, 1);
lean_inc_ref(x_139);
lean_dec(x_138);
x_140 = !lean_is_exclusive(x_137);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_141 = lean_ctor_get(x_137, 1);
x_142 = lean_ctor_get(x_137, 0);
lean_dec(x_142);
x_143 = lean_ctor_get(x_139, 0);
lean_inc_ref(x_143);
lean_dec_ref(x_139);
x_144 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0;
x_145 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1;
lean_inc(x_135);
x_146 = l_Lean_PersistentHashMap_find_x3f___redArg(x_144, x_145, x_143, x_135);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
lean_free_object(x_137);
lean_inc(x_3);
x_147 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_126, x_132, x_2, x_3, x_4, x_5, x_141);
lean_dec_ref(x_132);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
x_150 = l_Lean_Expr_hasMVar(x_148);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
lean_dec_ref(x_147);
x_151 = lean_st_ref_take(x_3, x_149);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_152, 1);
lean_inc_ref(x_153);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec_ref(x_151);
x_155 = !lean_is_exclusive(x_152);
if (x_155 == 0)
{
lean_object* x_156; uint8_t x_157; 
x_156 = lean_ctor_get(x_152, 1);
lean_dec(x_156);
x_157 = !lean_is_exclusive(x_153);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_158 = lean_ctor_get(x_153, 0);
lean_inc(x_148);
x_159 = l_Lean_PersistentHashMap_insert___redArg(x_144, x_145, x_158, x_135, x_148);
lean_ctor_set(x_153, 0, x_159);
x_160 = lean_st_ref_set(x_3, x_152, x_154);
lean_dec(x_3);
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_160, 0);
lean_dec(x_162);
lean_ctor_set(x_160, 0, x_148);
return x_160;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
lean_dec(x_160);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_148);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_165 = lean_ctor_get(x_153, 0);
x_166 = lean_ctor_get(x_153, 1);
x_167 = lean_ctor_get(x_153, 2);
x_168 = lean_ctor_get(x_153, 3);
x_169 = lean_ctor_get(x_153, 4);
x_170 = lean_ctor_get(x_153, 5);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_153);
lean_inc(x_148);
x_171 = l_Lean_PersistentHashMap_insert___redArg(x_144, x_145, x_165, x_135, x_148);
x_172 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_166);
lean_ctor_set(x_172, 2, x_167);
lean_ctor_set(x_172, 3, x_168);
lean_ctor_set(x_172, 4, x_169);
lean_ctor_set(x_172, 5, x_170);
lean_ctor_set(x_152, 1, x_172);
x_173 = lean_st_ref_set(x_3, x_152, x_154);
lean_dec(x_3);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_175 = x_173;
} else {
 lean_dec_ref(x_173);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_148);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_177 = lean_ctor_get(x_152, 0);
x_178 = lean_ctor_get(x_152, 2);
x_179 = lean_ctor_get(x_152, 3);
x_180 = lean_ctor_get(x_152, 4);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_152);
x_181 = lean_ctor_get(x_153, 0);
lean_inc_ref(x_181);
x_182 = lean_ctor_get(x_153, 1);
lean_inc_ref(x_182);
x_183 = lean_ctor_get(x_153, 2);
lean_inc_ref(x_183);
x_184 = lean_ctor_get(x_153, 3);
lean_inc_ref(x_184);
x_185 = lean_ctor_get(x_153, 4);
lean_inc_ref(x_185);
x_186 = lean_ctor_get(x_153, 5);
lean_inc_ref(x_186);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 lean_ctor_release(x_153, 2);
 lean_ctor_release(x_153, 3);
 lean_ctor_release(x_153, 4);
 lean_ctor_release(x_153, 5);
 x_187 = x_153;
} else {
 lean_dec_ref(x_153);
 x_187 = lean_box(0);
}
lean_inc(x_148);
x_188 = l_Lean_PersistentHashMap_insert___redArg(x_144, x_145, x_181, x_135, x_148);
if (lean_is_scalar(x_187)) {
 x_189 = lean_alloc_ctor(0, 6, 0);
} else {
 x_189 = x_187;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_182);
lean_ctor_set(x_189, 2, x_183);
lean_ctor_set(x_189, 3, x_184);
lean_ctor_set(x_189, 4, x_185);
lean_ctor_set(x_189, 5, x_186);
x_190 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_190, 0, x_177);
lean_ctor_set(x_190, 1, x_189);
lean_ctor_set(x_190, 2, x_178);
lean_ctor_set(x_190, 3, x_179);
lean_ctor_set(x_190, 4, x_180);
x_191 = lean_st_ref_set(x_3, x_190, x_154);
lean_dec(x_3);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_193 = x_191;
} else {
 lean_dec_ref(x_191);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_148);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
else
{
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_135);
lean_dec(x_3);
return x_147;
}
}
else
{
lean_dec(x_135);
lean_dec(x_3);
return x_147;
}
}
else
{
lean_object* x_195; 
lean_dec(x_135);
lean_dec_ref(x_132);
lean_dec_ref(x_126);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_195 = lean_ctor_get(x_146, 0);
lean_inc(x_195);
lean_dec_ref(x_146);
lean_ctor_set(x_137, 0, x_195);
return x_137;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_ctor_get(x_137, 1);
lean_inc(x_196);
lean_dec(x_137);
x_197 = lean_ctor_get(x_139, 0);
lean_inc_ref(x_197);
lean_dec_ref(x_139);
x_198 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0;
x_199 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1;
lean_inc(x_135);
x_200 = l_Lean_PersistentHashMap_find_x3f___redArg(x_198, x_199, x_197, x_135);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; 
lean_inc(x_3);
x_201 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_126, x_132, x_2, x_3, x_4, x_5, x_196);
lean_dec_ref(x_132);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
x_204 = l_Lean_Expr_hasMVar(x_202);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec_ref(x_201);
x_205 = lean_st_ref_take(x_3, x_203);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_206, 1);
lean_inc_ref(x_207);
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
lean_dec_ref(x_205);
x_209 = lean_ctor_get(x_206, 0);
lean_inc_ref(x_209);
x_210 = lean_ctor_get(x_206, 2);
lean_inc(x_210);
x_211 = lean_ctor_get(x_206, 3);
lean_inc_ref(x_211);
x_212 = lean_ctor_get(x_206, 4);
lean_inc_ref(x_212);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 lean_ctor_release(x_206, 2);
 lean_ctor_release(x_206, 3);
 lean_ctor_release(x_206, 4);
 x_213 = x_206;
} else {
 lean_dec_ref(x_206);
 x_213 = lean_box(0);
}
x_214 = lean_ctor_get(x_207, 0);
lean_inc_ref(x_214);
x_215 = lean_ctor_get(x_207, 1);
lean_inc_ref(x_215);
x_216 = lean_ctor_get(x_207, 2);
lean_inc_ref(x_216);
x_217 = lean_ctor_get(x_207, 3);
lean_inc_ref(x_217);
x_218 = lean_ctor_get(x_207, 4);
lean_inc_ref(x_218);
x_219 = lean_ctor_get(x_207, 5);
lean_inc_ref(x_219);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 lean_ctor_release(x_207, 4);
 lean_ctor_release(x_207, 5);
 x_220 = x_207;
} else {
 lean_dec_ref(x_207);
 x_220 = lean_box(0);
}
lean_inc(x_202);
x_221 = l_Lean_PersistentHashMap_insert___redArg(x_198, x_199, x_214, x_135, x_202);
if (lean_is_scalar(x_220)) {
 x_222 = lean_alloc_ctor(0, 6, 0);
} else {
 x_222 = x_220;
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_215);
lean_ctor_set(x_222, 2, x_216);
lean_ctor_set(x_222, 3, x_217);
lean_ctor_set(x_222, 4, x_218);
lean_ctor_set(x_222, 5, x_219);
if (lean_is_scalar(x_213)) {
 x_223 = lean_alloc_ctor(0, 5, 0);
} else {
 x_223 = x_213;
}
lean_ctor_set(x_223, 0, x_209);
lean_ctor_set(x_223, 1, x_222);
lean_ctor_set(x_223, 2, x_210);
lean_ctor_set(x_223, 3, x_211);
lean_ctor_set(x_223, 4, x_212);
x_224 = lean_st_ref_set(x_3, x_223, x_208);
lean_dec(x_3);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_226 = x_224;
} else {
 lean_dec_ref(x_224);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_202);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
else
{
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_135);
lean_dec(x_3);
return x_201;
}
}
else
{
lean_dec(x_135);
lean_dec(x_3);
return x_201;
}
}
else
{
lean_object* x_228; lean_object* x_229; 
lean_dec(x_135);
lean_dec_ref(x_132);
lean_dec_ref(x_126);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_228 = lean_ctor_get(x_200, 0);
lean_inc(x_228);
lean_dec_ref(x_200);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_196);
return x_229;
}
}
}
else
{
lean_object* x_230; 
lean_dec_ref(x_1);
x_230 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType(x_126, x_132, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_132);
return x_230;
}
}
case 7:
{
uint8_t x_231; 
x_231 = l_Lean_Expr_hasMVar(x_1);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
lean_inc_ref(x_1);
x_232 = l_Lean_Meta_mkExprConfigCacheKey___redArg(x_1, x_2, x_6);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec_ref(x_232);
x_235 = lean_st_ref_get(x_3, x_234);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_236, 1);
lean_inc_ref(x_237);
lean_dec(x_236);
x_238 = !lean_is_exclusive(x_235);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_239 = lean_ctor_get(x_235, 1);
x_240 = lean_ctor_get(x_235, 0);
lean_dec(x_240);
x_241 = lean_ctor_get(x_237, 0);
lean_inc_ref(x_241);
lean_dec_ref(x_237);
x_242 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0;
x_243 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1;
lean_inc(x_233);
x_244 = l_Lean_PersistentHashMap_find_x3f___redArg(x_242, x_243, x_241, x_233);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; 
lean_free_object(x_235);
lean_inc(x_3);
x_245 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(x_1, x_2, x_3, x_4, x_5, x_239);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
x_248 = l_Lean_Expr_hasMVar(x_246);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
lean_dec_ref(x_245);
x_249 = lean_st_ref_take(x_3, x_247);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_250, 1);
lean_inc_ref(x_251);
x_252 = lean_ctor_get(x_249, 1);
lean_inc(x_252);
lean_dec_ref(x_249);
x_253 = !lean_is_exclusive(x_250);
if (x_253 == 0)
{
lean_object* x_254; uint8_t x_255; 
x_254 = lean_ctor_get(x_250, 1);
lean_dec(x_254);
x_255 = !lean_is_exclusive(x_251);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_256 = lean_ctor_get(x_251, 0);
lean_inc(x_246);
x_257 = l_Lean_PersistentHashMap_insert___redArg(x_242, x_243, x_256, x_233, x_246);
lean_ctor_set(x_251, 0, x_257);
x_258 = lean_st_ref_set(x_3, x_250, x_252);
lean_dec(x_3);
x_259 = !lean_is_exclusive(x_258);
if (x_259 == 0)
{
lean_object* x_260; 
x_260 = lean_ctor_get(x_258, 0);
lean_dec(x_260);
lean_ctor_set(x_258, 0, x_246);
return x_258;
}
else
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
lean_dec(x_258);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_246);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_263 = lean_ctor_get(x_251, 0);
x_264 = lean_ctor_get(x_251, 1);
x_265 = lean_ctor_get(x_251, 2);
x_266 = lean_ctor_get(x_251, 3);
x_267 = lean_ctor_get(x_251, 4);
x_268 = lean_ctor_get(x_251, 5);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_251);
lean_inc(x_246);
x_269 = l_Lean_PersistentHashMap_insert___redArg(x_242, x_243, x_263, x_233, x_246);
x_270 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_264);
lean_ctor_set(x_270, 2, x_265);
lean_ctor_set(x_270, 3, x_266);
lean_ctor_set(x_270, 4, x_267);
lean_ctor_set(x_270, 5, x_268);
lean_ctor_set(x_250, 1, x_270);
x_271 = lean_st_ref_set(x_3, x_250, x_252);
lean_dec(x_3);
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_273 = x_271;
} else {
 lean_dec_ref(x_271);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_246);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_275 = lean_ctor_get(x_250, 0);
x_276 = lean_ctor_get(x_250, 2);
x_277 = lean_ctor_get(x_250, 3);
x_278 = lean_ctor_get(x_250, 4);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_250);
x_279 = lean_ctor_get(x_251, 0);
lean_inc_ref(x_279);
x_280 = lean_ctor_get(x_251, 1);
lean_inc_ref(x_280);
x_281 = lean_ctor_get(x_251, 2);
lean_inc_ref(x_281);
x_282 = lean_ctor_get(x_251, 3);
lean_inc_ref(x_282);
x_283 = lean_ctor_get(x_251, 4);
lean_inc_ref(x_283);
x_284 = lean_ctor_get(x_251, 5);
lean_inc_ref(x_284);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 lean_ctor_release(x_251, 2);
 lean_ctor_release(x_251, 3);
 lean_ctor_release(x_251, 4);
 lean_ctor_release(x_251, 5);
 x_285 = x_251;
} else {
 lean_dec_ref(x_251);
 x_285 = lean_box(0);
}
lean_inc(x_246);
x_286 = l_Lean_PersistentHashMap_insert___redArg(x_242, x_243, x_279, x_233, x_246);
if (lean_is_scalar(x_285)) {
 x_287 = lean_alloc_ctor(0, 6, 0);
} else {
 x_287 = x_285;
}
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_280);
lean_ctor_set(x_287, 2, x_281);
lean_ctor_set(x_287, 3, x_282);
lean_ctor_set(x_287, 4, x_283);
lean_ctor_set(x_287, 5, x_284);
x_288 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_288, 0, x_275);
lean_ctor_set(x_288, 1, x_287);
lean_ctor_set(x_288, 2, x_276);
lean_ctor_set(x_288, 3, x_277);
lean_ctor_set(x_288, 4, x_278);
x_289 = lean_st_ref_set(x_3, x_288, x_252);
lean_dec(x_3);
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_291 = x_289;
} else {
 lean_dec_ref(x_289);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_246);
lean_ctor_set(x_292, 1, x_290);
return x_292;
}
}
else
{
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_233);
lean_dec(x_3);
return x_245;
}
}
else
{
lean_dec(x_233);
lean_dec(x_3);
return x_245;
}
}
else
{
lean_object* x_293; 
lean_dec(x_233);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_293 = lean_ctor_get(x_244, 0);
lean_inc(x_293);
lean_dec_ref(x_244);
lean_ctor_set(x_235, 0, x_293);
return x_235;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_294 = lean_ctor_get(x_235, 1);
lean_inc(x_294);
lean_dec(x_235);
x_295 = lean_ctor_get(x_237, 0);
lean_inc_ref(x_295);
lean_dec_ref(x_237);
x_296 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0;
x_297 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1;
lean_inc(x_233);
x_298 = l_Lean_PersistentHashMap_find_x3f___redArg(x_296, x_297, x_295, x_233);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; 
lean_inc(x_3);
x_299 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(x_1, x_2, x_3, x_4, x_5, x_294);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
x_302 = l_Lean_Expr_hasMVar(x_300);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec_ref(x_299);
x_303 = lean_st_ref_take(x_3, x_301);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_304, 1);
lean_inc_ref(x_305);
x_306 = lean_ctor_get(x_303, 1);
lean_inc(x_306);
lean_dec_ref(x_303);
x_307 = lean_ctor_get(x_304, 0);
lean_inc_ref(x_307);
x_308 = lean_ctor_get(x_304, 2);
lean_inc(x_308);
x_309 = lean_ctor_get(x_304, 3);
lean_inc_ref(x_309);
x_310 = lean_ctor_get(x_304, 4);
lean_inc_ref(x_310);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 lean_ctor_release(x_304, 2);
 lean_ctor_release(x_304, 3);
 lean_ctor_release(x_304, 4);
 x_311 = x_304;
} else {
 lean_dec_ref(x_304);
 x_311 = lean_box(0);
}
x_312 = lean_ctor_get(x_305, 0);
lean_inc_ref(x_312);
x_313 = lean_ctor_get(x_305, 1);
lean_inc_ref(x_313);
x_314 = lean_ctor_get(x_305, 2);
lean_inc_ref(x_314);
x_315 = lean_ctor_get(x_305, 3);
lean_inc_ref(x_315);
x_316 = lean_ctor_get(x_305, 4);
lean_inc_ref(x_316);
x_317 = lean_ctor_get(x_305, 5);
lean_inc_ref(x_317);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 lean_ctor_release(x_305, 2);
 lean_ctor_release(x_305, 3);
 lean_ctor_release(x_305, 4);
 lean_ctor_release(x_305, 5);
 x_318 = x_305;
} else {
 lean_dec_ref(x_305);
 x_318 = lean_box(0);
}
lean_inc(x_300);
x_319 = l_Lean_PersistentHashMap_insert___redArg(x_296, x_297, x_312, x_233, x_300);
if (lean_is_scalar(x_318)) {
 x_320 = lean_alloc_ctor(0, 6, 0);
} else {
 x_320 = x_318;
}
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_313);
lean_ctor_set(x_320, 2, x_314);
lean_ctor_set(x_320, 3, x_315);
lean_ctor_set(x_320, 4, x_316);
lean_ctor_set(x_320, 5, x_317);
if (lean_is_scalar(x_311)) {
 x_321 = lean_alloc_ctor(0, 5, 0);
} else {
 x_321 = x_311;
}
lean_ctor_set(x_321, 0, x_307);
lean_ctor_set(x_321, 1, x_320);
lean_ctor_set(x_321, 2, x_308);
lean_ctor_set(x_321, 3, x_309);
lean_ctor_set(x_321, 4, x_310);
x_322 = lean_st_ref_set(x_3, x_321, x_306);
lean_dec(x_3);
x_323 = lean_ctor_get(x_322, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 x_324 = x_322;
} else {
 lean_dec_ref(x_322);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_300);
lean_ctor_set(x_325, 1, x_323);
return x_325;
}
else
{
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_233);
lean_dec(x_3);
return x_299;
}
}
else
{
lean_dec(x_233);
lean_dec(x_3);
return x_299;
}
}
else
{
lean_object* x_326; lean_object* x_327; 
lean_dec(x_233);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_326 = lean_ctor_get(x_298, 0);
lean_inc(x_326);
lean_dec_ref(x_298);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_294);
return x_327;
}
}
}
else
{
lean_object* x_328; 
x_328 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType(x_1, x_2, x_3, x_4, x_5, x_6);
return x_328;
}
}
case 9:
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_329 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_329);
lean_dec_ref(x_1);
x_330 = l_Lean_Literal_type(x_329);
lean_dec_ref(x_329);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_6);
return x_331;
}
case 10:
{
lean_object* x_332; 
x_332 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_332);
lean_dec_ref(x_1);
x_1 = x_332;
goto _start;
}
case 11:
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_334 = lean_ctor_get(x_1, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_1, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_336);
x_337 = l_Lean_Expr_hasMVar(x_1);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_338 = l_Lean_Meta_mkExprConfigCacheKey___redArg(x_1, x_2, x_6);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec_ref(x_338);
x_341 = lean_st_ref_get(x_3, x_340);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_342, 1);
lean_inc_ref(x_343);
lean_dec(x_342);
x_344 = !lean_is_exclusive(x_341);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_345 = lean_ctor_get(x_341, 1);
x_346 = lean_ctor_get(x_341, 0);
lean_dec(x_346);
x_347 = lean_ctor_get(x_343, 0);
lean_inc_ref(x_347);
lean_dec_ref(x_343);
x_348 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0;
x_349 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1;
lean_inc(x_339);
x_350 = l_Lean_PersistentHashMap_find_x3f___redArg(x_348, x_349, x_347, x_339);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; 
lean_free_object(x_341);
lean_inc(x_3);
x_351 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(x_334, x_335, x_336, x_2, x_3, x_4, x_5, x_345);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
x_354 = l_Lean_Expr_hasMVar(x_352);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; 
lean_dec_ref(x_351);
x_355 = lean_st_ref_take(x_3, x_353);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_356, 1);
lean_inc_ref(x_357);
x_358 = lean_ctor_get(x_355, 1);
lean_inc(x_358);
lean_dec_ref(x_355);
x_359 = !lean_is_exclusive(x_356);
if (x_359 == 0)
{
lean_object* x_360; uint8_t x_361; 
x_360 = lean_ctor_get(x_356, 1);
lean_dec(x_360);
x_361 = !lean_is_exclusive(x_357);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; 
x_362 = lean_ctor_get(x_357, 0);
lean_inc(x_352);
x_363 = l_Lean_PersistentHashMap_insert___redArg(x_348, x_349, x_362, x_339, x_352);
lean_ctor_set(x_357, 0, x_363);
x_364 = lean_st_ref_set(x_3, x_356, x_358);
lean_dec(x_3);
x_365 = !lean_is_exclusive(x_364);
if (x_365 == 0)
{
lean_object* x_366; 
x_366 = lean_ctor_get(x_364, 0);
lean_dec(x_366);
lean_ctor_set(x_364, 0, x_352);
return x_364;
}
else
{
lean_object* x_367; lean_object* x_368; 
x_367 = lean_ctor_get(x_364, 1);
lean_inc(x_367);
lean_dec(x_364);
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_352);
lean_ctor_set(x_368, 1, x_367);
return x_368;
}
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_369 = lean_ctor_get(x_357, 0);
x_370 = lean_ctor_get(x_357, 1);
x_371 = lean_ctor_get(x_357, 2);
x_372 = lean_ctor_get(x_357, 3);
x_373 = lean_ctor_get(x_357, 4);
x_374 = lean_ctor_get(x_357, 5);
lean_inc(x_374);
lean_inc(x_373);
lean_inc(x_372);
lean_inc(x_371);
lean_inc(x_370);
lean_inc(x_369);
lean_dec(x_357);
lean_inc(x_352);
x_375 = l_Lean_PersistentHashMap_insert___redArg(x_348, x_349, x_369, x_339, x_352);
x_376 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_370);
lean_ctor_set(x_376, 2, x_371);
lean_ctor_set(x_376, 3, x_372);
lean_ctor_set(x_376, 4, x_373);
lean_ctor_set(x_376, 5, x_374);
lean_ctor_set(x_356, 1, x_376);
x_377 = lean_st_ref_set(x_3, x_356, x_358);
lean_dec(x_3);
x_378 = lean_ctor_get(x_377, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_379 = x_377;
} else {
 lean_dec_ref(x_377);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_352);
lean_ctor_set(x_380, 1, x_378);
return x_380;
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_381 = lean_ctor_get(x_356, 0);
x_382 = lean_ctor_get(x_356, 2);
x_383 = lean_ctor_get(x_356, 3);
x_384 = lean_ctor_get(x_356, 4);
lean_inc(x_384);
lean_inc(x_383);
lean_inc(x_382);
lean_inc(x_381);
lean_dec(x_356);
x_385 = lean_ctor_get(x_357, 0);
lean_inc_ref(x_385);
x_386 = lean_ctor_get(x_357, 1);
lean_inc_ref(x_386);
x_387 = lean_ctor_get(x_357, 2);
lean_inc_ref(x_387);
x_388 = lean_ctor_get(x_357, 3);
lean_inc_ref(x_388);
x_389 = lean_ctor_get(x_357, 4);
lean_inc_ref(x_389);
x_390 = lean_ctor_get(x_357, 5);
lean_inc_ref(x_390);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 lean_ctor_release(x_357, 4);
 lean_ctor_release(x_357, 5);
 x_391 = x_357;
} else {
 lean_dec_ref(x_357);
 x_391 = lean_box(0);
}
lean_inc(x_352);
x_392 = l_Lean_PersistentHashMap_insert___redArg(x_348, x_349, x_385, x_339, x_352);
if (lean_is_scalar(x_391)) {
 x_393 = lean_alloc_ctor(0, 6, 0);
} else {
 x_393 = x_391;
}
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_386);
lean_ctor_set(x_393, 2, x_387);
lean_ctor_set(x_393, 3, x_388);
lean_ctor_set(x_393, 4, x_389);
lean_ctor_set(x_393, 5, x_390);
x_394 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_394, 0, x_381);
lean_ctor_set(x_394, 1, x_393);
lean_ctor_set(x_394, 2, x_382);
lean_ctor_set(x_394, 3, x_383);
lean_ctor_set(x_394, 4, x_384);
x_395 = lean_st_ref_set(x_3, x_394, x_358);
lean_dec(x_3);
x_396 = lean_ctor_get(x_395, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 x_397 = x_395;
} else {
 lean_dec_ref(x_395);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_352);
lean_ctor_set(x_398, 1, x_396);
return x_398;
}
}
else
{
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_339);
lean_dec(x_3);
return x_351;
}
}
else
{
lean_dec(x_339);
lean_dec(x_3);
return x_351;
}
}
else
{
lean_object* x_399; 
lean_dec(x_339);
lean_dec_ref(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_399 = lean_ctor_get(x_350, 0);
lean_inc(x_399);
lean_dec_ref(x_350);
lean_ctor_set(x_341, 0, x_399);
return x_341;
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_400 = lean_ctor_get(x_341, 1);
lean_inc(x_400);
lean_dec(x_341);
x_401 = lean_ctor_get(x_343, 0);
lean_inc_ref(x_401);
lean_dec_ref(x_343);
x_402 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0;
x_403 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1;
lean_inc(x_339);
x_404 = l_Lean_PersistentHashMap_find_x3f___redArg(x_402, x_403, x_401, x_339);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; 
lean_inc(x_3);
x_405 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(x_334, x_335, x_336, x_2, x_3, x_4, x_5, x_400);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; uint8_t x_408; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
x_408 = l_Lean_Expr_hasMVar(x_406);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec_ref(x_405);
x_409 = lean_st_ref_take(x_3, x_407);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_410, 1);
lean_inc_ref(x_411);
x_412 = lean_ctor_get(x_409, 1);
lean_inc(x_412);
lean_dec_ref(x_409);
x_413 = lean_ctor_get(x_410, 0);
lean_inc_ref(x_413);
x_414 = lean_ctor_get(x_410, 2);
lean_inc(x_414);
x_415 = lean_ctor_get(x_410, 3);
lean_inc_ref(x_415);
x_416 = lean_ctor_get(x_410, 4);
lean_inc_ref(x_416);
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
lean_inc_ref(x_418);
x_419 = lean_ctor_get(x_411, 1);
lean_inc_ref(x_419);
x_420 = lean_ctor_get(x_411, 2);
lean_inc_ref(x_420);
x_421 = lean_ctor_get(x_411, 3);
lean_inc_ref(x_421);
x_422 = lean_ctor_get(x_411, 4);
lean_inc_ref(x_422);
x_423 = lean_ctor_get(x_411, 5);
lean_inc_ref(x_423);
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
lean_inc(x_406);
x_425 = l_Lean_PersistentHashMap_insert___redArg(x_402, x_403, x_418, x_339, x_406);
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
lean_ctor_set(x_431, 0, x_406);
lean_ctor_set(x_431, 1, x_429);
return x_431;
}
else
{
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_339);
lean_dec(x_3);
return x_405;
}
}
else
{
lean_dec(x_339);
lean_dec(x_3);
return x_405;
}
}
else
{
lean_object* x_432; lean_object* x_433; 
lean_dec(x_339);
lean_dec_ref(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_432 = lean_ctor_get(x_404, 0);
lean_inc(x_432);
lean_dec_ref(x_404);
x_433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_400);
return x_433;
}
}
}
else
{
lean_object* x_434; 
lean_dec_ref(x_1);
x_434 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType(x_334, x_335, x_336, x_2, x_3, x_4, x_5, x_6);
return x_434;
}
}
default: 
{
uint8_t x_435; 
x_435 = l_Lean_Expr_hasMVar(x_1);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; 
lean_inc_ref(x_1);
x_436 = l_Lean_Meta_mkExprConfigCacheKey___redArg(x_1, x_2, x_6);
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec_ref(x_436);
x_439 = lean_st_ref_get(x_3, x_438);
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_440, 1);
lean_inc_ref(x_441);
lean_dec(x_440);
x_442 = !lean_is_exclusive(x_439);
if (x_442 == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_443 = lean_ctor_get(x_439, 1);
x_444 = lean_ctor_get(x_439, 0);
lean_dec(x_444);
x_445 = lean_ctor_get(x_441, 0);
lean_inc_ref(x_445);
lean_dec_ref(x_441);
x_446 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0;
x_447 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1;
lean_inc(x_437);
x_448 = l_Lean_PersistentHashMap_find_x3f___redArg(x_446, x_447, x_445, x_437);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; 
lean_free_object(x_439);
lean_inc(x_3);
x_449 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(x_1, x_2, x_3, x_4, x_5, x_443);
if (lean_obj_tag(x_449) == 0)
{
lean_object* x_450; lean_object* x_451; uint8_t x_452; 
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_449, 1);
lean_inc(x_451);
x_452 = l_Lean_Expr_hasMVar(x_450);
if (x_452 == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; 
lean_dec_ref(x_449);
x_453 = lean_st_ref_take(x_3, x_451);
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_454, 1);
lean_inc_ref(x_455);
x_456 = lean_ctor_get(x_453, 1);
lean_inc(x_456);
lean_dec_ref(x_453);
x_457 = !lean_is_exclusive(x_454);
if (x_457 == 0)
{
lean_object* x_458; uint8_t x_459; 
x_458 = lean_ctor_get(x_454, 1);
lean_dec(x_458);
x_459 = !lean_is_exclusive(x_455);
if (x_459 == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; 
x_460 = lean_ctor_get(x_455, 0);
lean_inc(x_450);
x_461 = l_Lean_PersistentHashMap_insert___redArg(x_446, x_447, x_460, x_437, x_450);
lean_ctor_set(x_455, 0, x_461);
x_462 = lean_st_ref_set(x_3, x_454, x_456);
lean_dec(x_3);
x_463 = !lean_is_exclusive(x_462);
if (x_463 == 0)
{
lean_object* x_464; 
x_464 = lean_ctor_get(x_462, 0);
lean_dec(x_464);
lean_ctor_set(x_462, 0, x_450);
return x_462;
}
else
{
lean_object* x_465; lean_object* x_466; 
x_465 = lean_ctor_get(x_462, 1);
lean_inc(x_465);
lean_dec(x_462);
x_466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_466, 0, x_450);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_467 = lean_ctor_get(x_455, 0);
x_468 = lean_ctor_get(x_455, 1);
x_469 = lean_ctor_get(x_455, 2);
x_470 = lean_ctor_get(x_455, 3);
x_471 = lean_ctor_get(x_455, 4);
x_472 = lean_ctor_get(x_455, 5);
lean_inc(x_472);
lean_inc(x_471);
lean_inc(x_470);
lean_inc(x_469);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_455);
lean_inc(x_450);
x_473 = l_Lean_PersistentHashMap_insert___redArg(x_446, x_447, x_467, x_437, x_450);
x_474 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_468);
lean_ctor_set(x_474, 2, x_469);
lean_ctor_set(x_474, 3, x_470);
lean_ctor_set(x_474, 4, x_471);
lean_ctor_set(x_474, 5, x_472);
lean_ctor_set(x_454, 1, x_474);
x_475 = lean_st_ref_set(x_3, x_454, x_456);
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
lean_ctor_set(x_478, 0, x_450);
lean_ctor_set(x_478, 1, x_476);
return x_478;
}
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_479 = lean_ctor_get(x_454, 0);
x_480 = lean_ctor_get(x_454, 2);
x_481 = lean_ctor_get(x_454, 3);
x_482 = lean_ctor_get(x_454, 4);
lean_inc(x_482);
lean_inc(x_481);
lean_inc(x_480);
lean_inc(x_479);
lean_dec(x_454);
x_483 = lean_ctor_get(x_455, 0);
lean_inc_ref(x_483);
x_484 = lean_ctor_get(x_455, 1);
lean_inc_ref(x_484);
x_485 = lean_ctor_get(x_455, 2);
lean_inc_ref(x_485);
x_486 = lean_ctor_get(x_455, 3);
lean_inc_ref(x_486);
x_487 = lean_ctor_get(x_455, 4);
lean_inc_ref(x_487);
x_488 = lean_ctor_get(x_455, 5);
lean_inc_ref(x_488);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 lean_ctor_release(x_455, 2);
 lean_ctor_release(x_455, 3);
 lean_ctor_release(x_455, 4);
 lean_ctor_release(x_455, 5);
 x_489 = x_455;
} else {
 lean_dec_ref(x_455);
 x_489 = lean_box(0);
}
lean_inc(x_450);
x_490 = l_Lean_PersistentHashMap_insert___redArg(x_446, x_447, x_483, x_437, x_450);
if (lean_is_scalar(x_489)) {
 x_491 = lean_alloc_ctor(0, 6, 0);
} else {
 x_491 = x_489;
}
lean_ctor_set(x_491, 0, x_490);
lean_ctor_set(x_491, 1, x_484);
lean_ctor_set(x_491, 2, x_485);
lean_ctor_set(x_491, 3, x_486);
lean_ctor_set(x_491, 4, x_487);
lean_ctor_set(x_491, 5, x_488);
x_492 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_492, 0, x_479);
lean_ctor_set(x_492, 1, x_491);
lean_ctor_set(x_492, 2, x_480);
lean_ctor_set(x_492, 3, x_481);
lean_ctor_set(x_492, 4, x_482);
x_493 = lean_st_ref_set(x_3, x_492, x_456);
lean_dec(x_3);
x_494 = lean_ctor_get(x_493, 1);
lean_inc(x_494);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 lean_ctor_release(x_493, 1);
 x_495 = x_493;
} else {
 lean_dec_ref(x_493);
 x_495 = lean_box(0);
}
if (lean_is_scalar(x_495)) {
 x_496 = lean_alloc_ctor(0, 2, 0);
} else {
 x_496 = x_495;
}
lean_ctor_set(x_496, 0, x_450);
lean_ctor_set(x_496, 1, x_494);
return x_496;
}
}
else
{
lean_dec(x_451);
lean_dec(x_450);
lean_dec(x_437);
lean_dec(x_3);
return x_449;
}
}
else
{
lean_dec(x_437);
lean_dec(x_3);
return x_449;
}
}
else
{
lean_object* x_497; 
lean_dec(x_437);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_497 = lean_ctor_get(x_448, 0);
lean_inc(x_497);
lean_dec_ref(x_448);
lean_ctor_set(x_439, 0, x_497);
return x_439;
}
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_498 = lean_ctor_get(x_439, 1);
lean_inc(x_498);
lean_dec(x_439);
x_499 = lean_ctor_get(x_441, 0);
lean_inc_ref(x_499);
lean_dec_ref(x_441);
x_500 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__0;
x_501 = l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___closed__1;
lean_inc(x_437);
x_502 = l_Lean_PersistentHashMap_find_x3f___redArg(x_500, x_501, x_499, x_437);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; 
lean_inc(x_3);
x_503 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(x_1, x_2, x_3, x_4, x_5, x_498);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; lean_object* x_505; uint8_t x_506; 
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
x_506 = l_Lean_Expr_hasMVar(x_504);
if (x_506 == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
lean_dec_ref(x_503);
x_507 = lean_st_ref_take(x_3, x_505);
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_508, 1);
lean_inc_ref(x_509);
x_510 = lean_ctor_get(x_507, 1);
lean_inc(x_510);
lean_dec_ref(x_507);
x_511 = lean_ctor_get(x_508, 0);
lean_inc_ref(x_511);
x_512 = lean_ctor_get(x_508, 2);
lean_inc(x_512);
x_513 = lean_ctor_get(x_508, 3);
lean_inc_ref(x_513);
x_514 = lean_ctor_get(x_508, 4);
lean_inc_ref(x_514);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 lean_ctor_release(x_508, 2);
 lean_ctor_release(x_508, 3);
 lean_ctor_release(x_508, 4);
 x_515 = x_508;
} else {
 lean_dec_ref(x_508);
 x_515 = lean_box(0);
}
x_516 = lean_ctor_get(x_509, 0);
lean_inc_ref(x_516);
x_517 = lean_ctor_get(x_509, 1);
lean_inc_ref(x_517);
x_518 = lean_ctor_get(x_509, 2);
lean_inc_ref(x_518);
x_519 = lean_ctor_get(x_509, 3);
lean_inc_ref(x_519);
x_520 = lean_ctor_get(x_509, 4);
lean_inc_ref(x_520);
x_521 = lean_ctor_get(x_509, 5);
lean_inc_ref(x_521);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 lean_ctor_release(x_509, 2);
 lean_ctor_release(x_509, 3);
 lean_ctor_release(x_509, 4);
 lean_ctor_release(x_509, 5);
 x_522 = x_509;
} else {
 lean_dec_ref(x_509);
 x_522 = lean_box(0);
}
lean_inc(x_504);
x_523 = l_Lean_PersistentHashMap_insert___redArg(x_500, x_501, x_516, x_437, x_504);
if (lean_is_scalar(x_522)) {
 x_524 = lean_alloc_ctor(0, 6, 0);
} else {
 x_524 = x_522;
}
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_517);
lean_ctor_set(x_524, 2, x_518);
lean_ctor_set(x_524, 3, x_519);
lean_ctor_set(x_524, 4, x_520);
lean_ctor_set(x_524, 5, x_521);
if (lean_is_scalar(x_515)) {
 x_525 = lean_alloc_ctor(0, 5, 0);
} else {
 x_525 = x_515;
}
lean_ctor_set(x_525, 0, x_511);
lean_ctor_set(x_525, 1, x_524);
lean_ctor_set(x_525, 2, x_512);
lean_ctor_set(x_525, 3, x_513);
lean_ctor_set(x_525, 4, x_514);
x_526 = lean_st_ref_set(x_3, x_525, x_510);
lean_dec(x_3);
x_527 = lean_ctor_get(x_526, 1);
lean_inc(x_527);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 x_528 = x_526;
} else {
 lean_dec_ref(x_526);
 x_528 = lean_box(0);
}
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(0, 2, 0);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_504);
lean_ctor_set(x_529, 1, x_527);
return x_529;
}
else
{
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_437);
lean_dec(x_3);
return x_503;
}
}
else
{
lean_dec(x_437);
lean_dec(x_3);
return x_503;
}
}
else
{
lean_object* x_530; lean_object* x_531; 
lean_dec(x_437);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_530 = lean_ctor_get(x_502, 0);
lean_inc(x_530);
lean_dec_ref(x_502);
x_531 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_498);
return x_531;
}
}
}
else
{
lean_object* x_532; 
x_532 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType(x_1, x_2, x_3, x_4, x_5, x_6);
return x_532;
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
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_66; uint8_t x_188; uint8_t x_189; 
x_22 = l_Lean_Meta_Context_config(x_2);
x_23 = lean_ctor_get_uint8(x_22, 9);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
lean_ctor_set(x_4, 3, x_25);
x_188 = 1;
x_189 = l_Lean_Meta_TransparencyMode_lt(x_23, x_188);
if (x_189 == 0)
{
x_66 = x_23;
goto block_187;
}
else
{
x_66 = x_188;
goto block_187;
}
block_65:
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_Meta_Context_config(x_30);
lean_dec_ref(x_30);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
uint8_t x_39; uint8_t x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = 1;
x_40 = 2;
lean_ctor_set_uint8(x_37, 12, x_39);
lean_ctor_set_uint8(x_37, 13, x_39);
lean_ctor_set_uint8(x_37, 14, x_40);
lean_ctor_set_uint8(x_37, 15, x_39);
lean_ctor_set_uint8(x_37, 16, x_39);
lean_ctor_set_uint8(x_37, 18, x_39);
x_41 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_37);
x_42 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set_uint64(x_42, sizeof(void*)*1, x_41);
x_43 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_34);
lean_ctor_set(x_43, 2, x_27);
lean_ctor_set(x_43, 3, x_32);
lean_ctor_set(x_43, 4, x_31);
lean_ctor_set(x_43, 5, x_28);
lean_ctor_set(x_43, 6, x_26);
lean_ctor_set_uint8(x_43, sizeof(void*)*7, x_29);
lean_ctor_set_uint8(x_43, sizeof(void*)*7 + 1, x_36);
lean_ctor_set_uint8(x_43, sizeof(void*)*7 + 2, x_33);
x_44 = l_Lean_Meta_inferTypeImp_infer(x_1, x_43, x_3, x_4, x_5, x_35);
return x_44;
}
else
{
uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_45 = lean_ctor_get_uint8(x_37, 0);
x_46 = lean_ctor_get_uint8(x_37, 1);
x_47 = lean_ctor_get_uint8(x_37, 2);
x_48 = lean_ctor_get_uint8(x_37, 3);
x_49 = lean_ctor_get_uint8(x_37, 4);
x_50 = lean_ctor_get_uint8(x_37, 5);
x_51 = lean_ctor_get_uint8(x_37, 6);
x_52 = lean_ctor_get_uint8(x_37, 7);
x_53 = lean_ctor_get_uint8(x_37, 8);
x_54 = lean_ctor_get_uint8(x_37, 9);
x_55 = lean_ctor_get_uint8(x_37, 10);
x_56 = lean_ctor_get_uint8(x_37, 11);
x_57 = lean_ctor_get_uint8(x_37, 17);
lean_dec(x_37);
x_58 = 1;
x_59 = 2;
x_60 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_60, 0, x_45);
lean_ctor_set_uint8(x_60, 1, x_46);
lean_ctor_set_uint8(x_60, 2, x_47);
lean_ctor_set_uint8(x_60, 3, x_48);
lean_ctor_set_uint8(x_60, 4, x_49);
lean_ctor_set_uint8(x_60, 5, x_50);
lean_ctor_set_uint8(x_60, 6, x_51);
lean_ctor_set_uint8(x_60, 7, x_52);
lean_ctor_set_uint8(x_60, 8, x_53);
lean_ctor_set_uint8(x_60, 9, x_54);
lean_ctor_set_uint8(x_60, 10, x_55);
lean_ctor_set_uint8(x_60, 11, x_56);
lean_ctor_set_uint8(x_60, 12, x_58);
lean_ctor_set_uint8(x_60, 13, x_58);
lean_ctor_set_uint8(x_60, 14, x_59);
lean_ctor_set_uint8(x_60, 15, x_58);
lean_ctor_set_uint8(x_60, 16, x_58);
lean_ctor_set_uint8(x_60, 17, x_57);
lean_ctor_set_uint8(x_60, 18, x_58);
x_61 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_60);
x_62 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set_uint64(x_62, sizeof(void*)*1, x_61);
x_63 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_34);
lean_ctor_set(x_63, 2, x_27);
lean_ctor_set(x_63, 3, x_32);
lean_ctor_set(x_63, 4, x_31);
lean_ctor_set(x_63, 5, x_28);
lean_ctor_set(x_63, 6, x_26);
lean_ctor_set_uint8(x_63, sizeof(void*)*7, x_29);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 1, x_36);
lean_ctor_set_uint8(x_63, sizeof(void*)*7 + 2, x_33);
x_64 = l_Lean_Meta_inferTypeImp_infer(x_1, x_63, x_3, x_4, x_5, x_35);
return x_64;
}
}
block_187:
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_22);
if (x_67 == 0)
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; uint64_t x_77; uint8_t x_78; 
x_68 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_69 = lean_ctor_get(x_2, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_2, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_2, 5);
lean_inc(x_73);
x_74 = lean_ctor_get(x_2, 6);
lean_inc(x_74);
x_75 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
x_76 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 2);
lean_ctor_set_uint8(x_22, 9, x_66);
x_77 = l_Lean_Meta_Context_configKey(x_2);
x_78 = !lean_is_exclusive(x_2);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; uint64_t x_87; uint64_t x_88; uint64_t x_89; uint64_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_79 = lean_ctor_get(x_2, 6);
lean_dec(x_79);
x_80 = lean_ctor_get(x_2, 5);
lean_dec(x_80);
x_81 = lean_ctor_get(x_2, 4);
lean_dec(x_81);
x_82 = lean_ctor_get(x_2, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_2, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_2, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_2, 0);
lean_dec(x_85);
x_86 = 2;
x_87 = lean_uint64_shift_right(x_77, x_86);
x_88 = lean_uint64_shift_left(x_87, x_86);
x_89 = l_Lean_Meta_TransparencyMode_toUInt64(x_66);
x_90 = lean_uint64_lor(x_88, x_89);
x_91 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_91, 0, x_22);
lean_ctor_set_uint64(x_91, sizeof(void*)*1, x_90);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc_ref(x_71);
lean_inc_ref(x_70);
lean_inc(x_69);
lean_ctor_set(x_2, 0, x_91);
x_92 = l_Lean_Meta_getConfig___redArg(x_2, x_6);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get_uint8(x_93, 13);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_93);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec_ref(x_92);
x_26 = x_74;
x_27 = x_70;
x_28 = x_73;
x_29 = x_68;
x_30 = x_2;
x_31 = x_72;
x_32 = x_71;
x_33 = x_76;
x_34 = x_69;
x_35 = x_95;
x_36 = x_75;
goto block_65;
}
else
{
uint8_t x_96; 
x_96 = lean_ctor_get_uint8(x_93, 12);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_93);
x_97 = lean_ctor_get(x_92, 1);
lean_inc(x_97);
lean_dec_ref(x_92);
x_26 = x_74;
x_27 = x_70;
x_28 = x_73;
x_29 = x_68;
x_30 = x_2;
x_31 = x_72;
x_32 = x_71;
x_33 = x_76;
x_34 = x_69;
x_35 = x_97;
x_36 = x_75;
goto block_65;
}
else
{
uint8_t x_98; 
x_98 = lean_ctor_get_uint8(x_93, 15);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec(x_93);
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
lean_dec_ref(x_92);
x_26 = x_74;
x_27 = x_70;
x_28 = x_73;
x_29 = x_68;
x_30 = x_2;
x_31 = x_72;
x_32 = x_71;
x_33 = x_76;
x_34 = x_69;
x_35 = x_99;
x_36 = x_75;
goto block_65;
}
else
{
uint8_t x_100; 
x_100 = lean_ctor_get_uint8(x_93, 18);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_93);
x_101 = lean_ctor_get(x_92, 1);
lean_inc(x_101);
lean_dec_ref(x_92);
x_26 = x_74;
x_27 = x_70;
x_28 = x_73;
x_29 = x_68;
x_30 = x_2;
x_31 = x_72;
x_32 = x_71;
x_33 = x_76;
x_34 = x_69;
x_35 = x_101;
x_36 = x_75;
goto block_65;
}
else
{
uint8_t x_102; 
x_102 = lean_ctor_get_uint8(x_93, 16);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_93);
x_103 = lean_ctor_get(x_92, 1);
lean_inc(x_103);
lean_dec_ref(x_92);
x_26 = x_74;
x_27 = x_70;
x_28 = x_73;
x_29 = x_68;
x_30 = x_2;
x_31 = x_72;
x_32 = x_71;
x_33 = x_76;
x_34 = x_69;
x_35 = x_103;
x_36 = x_75;
goto block_65;
}
else
{
lean_object* x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; 
x_104 = lean_ctor_get(x_92, 1);
lean_inc(x_104);
lean_dec_ref(x_92);
x_105 = lean_ctor_get_uint8(x_93, 14);
lean_dec(x_93);
x_106 = 2;
x_107 = l_Lean_Meta_instDecidableEqProjReductionKind(x_105, x_106);
if (x_107 == 0)
{
x_26 = x_74;
x_27 = x_70;
x_28 = x_73;
x_29 = x_68;
x_30 = x_2;
x_31 = x_72;
x_32 = x_71;
x_33 = x_76;
x_34 = x_69;
x_35 = x_104;
x_36 = x_75;
goto block_65;
}
else
{
lean_object* x_108; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec(x_69);
x_108 = l_Lean_Meta_inferTypeImp_infer(x_1, x_2, x_3, x_4, x_5, x_104);
return x_108;
}
}
}
}
}
}
}
else
{
uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
lean_dec(x_2);
x_109 = 2;
x_110 = lean_uint64_shift_right(x_77, x_109);
x_111 = lean_uint64_shift_left(x_110, x_109);
x_112 = l_Lean_Meta_TransparencyMode_toUInt64(x_66);
x_113 = lean_uint64_lor(x_111, x_112);
x_114 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_114, 0, x_22);
lean_ctor_set_uint64(x_114, sizeof(void*)*1, x_113);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc_ref(x_71);
lean_inc_ref(x_70);
lean_inc(x_69);
x_115 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_69);
lean_ctor_set(x_115, 2, x_70);
lean_ctor_set(x_115, 3, x_71);
lean_ctor_set(x_115, 4, x_72);
lean_ctor_set(x_115, 5, x_73);
lean_ctor_set(x_115, 6, x_74);
lean_ctor_set_uint8(x_115, sizeof(void*)*7, x_68);
lean_ctor_set_uint8(x_115, sizeof(void*)*7 + 1, x_75);
lean_ctor_set_uint8(x_115, sizeof(void*)*7 + 2, x_76);
x_116 = l_Lean_Meta_getConfig___redArg(x_115, x_6);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get_uint8(x_117, 13);
if (x_118 == 0)
{
lean_object* x_119; 
lean_dec(x_117);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_dec_ref(x_116);
x_26 = x_74;
x_27 = x_70;
x_28 = x_73;
x_29 = x_68;
x_30 = x_115;
x_31 = x_72;
x_32 = x_71;
x_33 = x_76;
x_34 = x_69;
x_35 = x_119;
x_36 = x_75;
goto block_65;
}
else
{
uint8_t x_120; 
x_120 = lean_ctor_get_uint8(x_117, 12);
if (x_120 == 0)
{
lean_object* x_121; 
lean_dec(x_117);
x_121 = lean_ctor_get(x_116, 1);
lean_inc(x_121);
lean_dec_ref(x_116);
x_26 = x_74;
x_27 = x_70;
x_28 = x_73;
x_29 = x_68;
x_30 = x_115;
x_31 = x_72;
x_32 = x_71;
x_33 = x_76;
x_34 = x_69;
x_35 = x_121;
x_36 = x_75;
goto block_65;
}
else
{
uint8_t x_122; 
x_122 = lean_ctor_get_uint8(x_117, 15);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_117);
x_123 = lean_ctor_get(x_116, 1);
lean_inc(x_123);
lean_dec_ref(x_116);
x_26 = x_74;
x_27 = x_70;
x_28 = x_73;
x_29 = x_68;
x_30 = x_115;
x_31 = x_72;
x_32 = x_71;
x_33 = x_76;
x_34 = x_69;
x_35 = x_123;
x_36 = x_75;
goto block_65;
}
else
{
uint8_t x_124; 
x_124 = lean_ctor_get_uint8(x_117, 18);
if (x_124 == 0)
{
lean_object* x_125; 
lean_dec(x_117);
x_125 = lean_ctor_get(x_116, 1);
lean_inc(x_125);
lean_dec_ref(x_116);
x_26 = x_74;
x_27 = x_70;
x_28 = x_73;
x_29 = x_68;
x_30 = x_115;
x_31 = x_72;
x_32 = x_71;
x_33 = x_76;
x_34 = x_69;
x_35 = x_125;
x_36 = x_75;
goto block_65;
}
else
{
uint8_t x_126; 
x_126 = lean_ctor_get_uint8(x_117, 16);
if (x_126 == 0)
{
lean_object* x_127; 
lean_dec(x_117);
x_127 = lean_ctor_get(x_116, 1);
lean_inc(x_127);
lean_dec_ref(x_116);
x_26 = x_74;
x_27 = x_70;
x_28 = x_73;
x_29 = x_68;
x_30 = x_115;
x_31 = x_72;
x_32 = x_71;
x_33 = x_76;
x_34 = x_69;
x_35 = x_127;
x_36 = x_75;
goto block_65;
}
else
{
lean_object* x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; 
x_128 = lean_ctor_get(x_116, 1);
lean_inc(x_128);
lean_dec_ref(x_116);
x_129 = lean_ctor_get_uint8(x_117, 14);
lean_dec(x_117);
x_130 = 2;
x_131 = l_Lean_Meta_instDecidableEqProjReductionKind(x_129, x_130);
if (x_131 == 0)
{
x_26 = x_74;
x_27 = x_70;
x_28 = x_73;
x_29 = x_68;
x_30 = x_115;
x_31 = x_72;
x_32 = x_71;
x_33 = x_76;
x_34 = x_69;
x_35 = x_128;
x_36 = x_75;
goto block_65;
}
else
{
lean_object* x_132; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec(x_69);
x_132 = l_Lean_Meta_inferTypeImp_infer(x_1, x_115, x_3, x_4, x_5, x_128);
return x_132;
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
uint8_t x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_159; lean_object* x_160; uint64_t x_161; lean_object* x_162; uint64_t x_163; uint64_t x_164; uint64_t x_165; uint64_t x_166; uint64_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_133 = lean_ctor_get_uint8(x_22, 0);
x_134 = lean_ctor_get_uint8(x_22, 1);
x_135 = lean_ctor_get_uint8(x_22, 2);
x_136 = lean_ctor_get_uint8(x_22, 3);
x_137 = lean_ctor_get_uint8(x_22, 4);
x_138 = lean_ctor_get_uint8(x_22, 5);
x_139 = lean_ctor_get_uint8(x_22, 6);
x_140 = lean_ctor_get_uint8(x_22, 7);
x_141 = lean_ctor_get_uint8(x_22, 8);
x_142 = lean_ctor_get_uint8(x_22, 10);
x_143 = lean_ctor_get_uint8(x_22, 11);
x_144 = lean_ctor_get_uint8(x_22, 12);
x_145 = lean_ctor_get_uint8(x_22, 13);
x_146 = lean_ctor_get_uint8(x_22, 14);
x_147 = lean_ctor_get_uint8(x_22, 15);
x_148 = lean_ctor_get_uint8(x_22, 16);
x_149 = lean_ctor_get_uint8(x_22, 17);
x_150 = lean_ctor_get_uint8(x_22, 18);
lean_dec(x_22);
x_151 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_152 = lean_ctor_get(x_2, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_153);
x_154 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_154);
x_155 = lean_ctor_get(x_2, 4);
lean_inc(x_155);
x_156 = lean_ctor_get(x_2, 5);
lean_inc(x_156);
x_157 = lean_ctor_get(x_2, 6);
lean_inc(x_157);
x_158 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
x_159 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 2);
x_160 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_160, 0, x_133);
lean_ctor_set_uint8(x_160, 1, x_134);
lean_ctor_set_uint8(x_160, 2, x_135);
lean_ctor_set_uint8(x_160, 3, x_136);
lean_ctor_set_uint8(x_160, 4, x_137);
lean_ctor_set_uint8(x_160, 5, x_138);
lean_ctor_set_uint8(x_160, 6, x_139);
lean_ctor_set_uint8(x_160, 7, x_140);
lean_ctor_set_uint8(x_160, 8, x_141);
lean_ctor_set_uint8(x_160, 9, x_66);
lean_ctor_set_uint8(x_160, 10, x_142);
lean_ctor_set_uint8(x_160, 11, x_143);
lean_ctor_set_uint8(x_160, 12, x_144);
lean_ctor_set_uint8(x_160, 13, x_145);
lean_ctor_set_uint8(x_160, 14, x_146);
lean_ctor_set_uint8(x_160, 15, x_147);
lean_ctor_set_uint8(x_160, 16, x_148);
lean_ctor_set_uint8(x_160, 17, x_149);
lean_ctor_set_uint8(x_160, 18, x_150);
x_161 = l_Lean_Meta_Context_configKey(x_2);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_162 = x_2;
} else {
 lean_dec_ref(x_2);
 x_162 = lean_box(0);
}
x_163 = 2;
x_164 = lean_uint64_shift_right(x_161, x_163);
x_165 = lean_uint64_shift_left(x_164, x_163);
x_166 = l_Lean_Meta_TransparencyMode_toUInt64(x_66);
x_167 = lean_uint64_lor(x_165, x_166);
x_168 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_168, 0, x_160);
lean_ctor_set_uint64(x_168, sizeof(void*)*1, x_167);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc_ref(x_154);
lean_inc_ref(x_153);
lean_inc(x_152);
if (lean_is_scalar(x_162)) {
 x_169 = lean_alloc_ctor(0, 7, 3);
} else {
 x_169 = x_162;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_152);
lean_ctor_set(x_169, 2, x_153);
lean_ctor_set(x_169, 3, x_154);
lean_ctor_set(x_169, 4, x_155);
lean_ctor_set(x_169, 5, x_156);
lean_ctor_set(x_169, 6, x_157);
lean_ctor_set_uint8(x_169, sizeof(void*)*7, x_151);
lean_ctor_set_uint8(x_169, sizeof(void*)*7 + 1, x_158);
lean_ctor_set_uint8(x_169, sizeof(void*)*7 + 2, x_159);
x_170 = l_Lean_Meta_getConfig___redArg(x_169, x_6);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get_uint8(x_171, 13);
if (x_172 == 0)
{
lean_object* x_173; 
lean_dec(x_171);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec_ref(x_170);
x_26 = x_157;
x_27 = x_153;
x_28 = x_156;
x_29 = x_151;
x_30 = x_169;
x_31 = x_155;
x_32 = x_154;
x_33 = x_159;
x_34 = x_152;
x_35 = x_173;
x_36 = x_158;
goto block_65;
}
else
{
uint8_t x_174; 
x_174 = lean_ctor_get_uint8(x_171, 12);
if (x_174 == 0)
{
lean_object* x_175; 
lean_dec(x_171);
x_175 = lean_ctor_get(x_170, 1);
lean_inc(x_175);
lean_dec_ref(x_170);
x_26 = x_157;
x_27 = x_153;
x_28 = x_156;
x_29 = x_151;
x_30 = x_169;
x_31 = x_155;
x_32 = x_154;
x_33 = x_159;
x_34 = x_152;
x_35 = x_175;
x_36 = x_158;
goto block_65;
}
else
{
uint8_t x_176; 
x_176 = lean_ctor_get_uint8(x_171, 15);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec(x_171);
x_177 = lean_ctor_get(x_170, 1);
lean_inc(x_177);
lean_dec_ref(x_170);
x_26 = x_157;
x_27 = x_153;
x_28 = x_156;
x_29 = x_151;
x_30 = x_169;
x_31 = x_155;
x_32 = x_154;
x_33 = x_159;
x_34 = x_152;
x_35 = x_177;
x_36 = x_158;
goto block_65;
}
else
{
uint8_t x_178; 
x_178 = lean_ctor_get_uint8(x_171, 18);
if (x_178 == 0)
{
lean_object* x_179; 
lean_dec(x_171);
x_179 = lean_ctor_get(x_170, 1);
lean_inc(x_179);
lean_dec_ref(x_170);
x_26 = x_157;
x_27 = x_153;
x_28 = x_156;
x_29 = x_151;
x_30 = x_169;
x_31 = x_155;
x_32 = x_154;
x_33 = x_159;
x_34 = x_152;
x_35 = x_179;
x_36 = x_158;
goto block_65;
}
else
{
uint8_t x_180; 
x_180 = lean_ctor_get_uint8(x_171, 16);
if (x_180 == 0)
{
lean_object* x_181; 
lean_dec(x_171);
x_181 = lean_ctor_get(x_170, 1);
lean_inc(x_181);
lean_dec_ref(x_170);
x_26 = x_157;
x_27 = x_153;
x_28 = x_156;
x_29 = x_151;
x_30 = x_169;
x_31 = x_155;
x_32 = x_154;
x_33 = x_159;
x_34 = x_152;
x_35 = x_181;
x_36 = x_158;
goto block_65;
}
else
{
lean_object* x_182; uint8_t x_183; uint8_t x_184; uint8_t x_185; 
x_182 = lean_ctor_get(x_170, 1);
lean_inc(x_182);
lean_dec_ref(x_170);
x_183 = lean_ctor_get_uint8(x_171, 14);
lean_dec(x_171);
x_184 = 2;
x_185 = l_Lean_Meta_instDecidableEqProjReductionKind(x_183, x_184);
if (x_185 == 0)
{
x_26 = x_157;
x_27 = x_153;
x_28 = x_156;
x_29 = x_151;
x_30 = x_169;
x_31 = x_155;
x_32 = x_154;
x_33 = x_159;
x_34 = x_152;
x_35 = x_182;
x_36 = x_158;
goto block_65;
}
else
{
lean_object* x_186; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec_ref(x_154);
lean_dec_ref(x_153);
lean_dec(x_152);
x_186 = l_Lean_Meta_inferTypeImp_infer(x_1, x_169, x_3, x_4, x_5, x_182);
return x_186;
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
lean_object* x_190; 
lean_free_object(x_4);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_190 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg(x_13, x_6);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; uint8_t x_206; 
x_191 = lean_ctor_get(x_4, 0);
x_192 = lean_ctor_get(x_4, 1);
x_193 = lean_ctor_get(x_4, 2);
x_194 = lean_ctor_get(x_4, 3);
x_195 = lean_ctor_get(x_4, 4);
x_196 = lean_ctor_get(x_4, 5);
x_197 = lean_ctor_get(x_4, 6);
x_198 = lean_ctor_get(x_4, 7);
x_199 = lean_ctor_get(x_4, 8);
x_200 = lean_ctor_get(x_4, 9);
x_201 = lean_ctor_get(x_4, 10);
x_202 = lean_ctor_get_uint8(x_4, sizeof(void*)*13);
x_203 = lean_ctor_get(x_4, 11);
x_204 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_205 = lean_ctor_get(x_4, 12);
lean_inc(x_205);
lean_inc(x_203);
lean_inc(x_201);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_4);
x_206 = lean_nat_dec_eq(x_194, x_195);
if (x_206 == 0)
{
lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; uint8_t x_246; uint8_t x_303; uint8_t x_304; 
x_207 = l_Lean_Meta_Context_config(x_2);
x_208 = lean_ctor_get_uint8(x_207, 9);
x_209 = lean_unsigned_to_nat(1u);
x_210 = lean_nat_add(x_194, x_209);
lean_dec(x_194);
x_211 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_211, 0, x_191);
lean_ctor_set(x_211, 1, x_192);
lean_ctor_set(x_211, 2, x_193);
lean_ctor_set(x_211, 3, x_210);
lean_ctor_set(x_211, 4, x_195);
lean_ctor_set(x_211, 5, x_196);
lean_ctor_set(x_211, 6, x_197);
lean_ctor_set(x_211, 7, x_198);
lean_ctor_set(x_211, 8, x_199);
lean_ctor_set(x_211, 9, x_200);
lean_ctor_set(x_211, 10, x_201);
lean_ctor_set(x_211, 11, x_203);
lean_ctor_set(x_211, 12, x_205);
lean_ctor_set_uint8(x_211, sizeof(void*)*13, x_202);
lean_ctor_set_uint8(x_211, sizeof(void*)*13 + 1, x_204);
x_303 = 1;
x_304 = l_Lean_Meta_TransparencyMode_lt(x_208, x_303);
if (x_304 == 0)
{
x_246 = x_208;
goto block_302;
}
else
{
x_246 = x_303;
goto block_302;
}
block_245:
{
lean_object* x_223; uint8_t x_224; uint8_t x_225; uint8_t x_226; uint8_t x_227; uint8_t x_228; uint8_t x_229; uint8_t x_230; uint8_t x_231; uint8_t x_232; uint8_t x_233; uint8_t x_234; uint8_t x_235; uint8_t x_236; lean_object* x_237; uint8_t x_238; uint8_t x_239; lean_object* x_240; uint64_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_223 = l_Lean_Meta_Context_config(x_216);
lean_dec_ref(x_216);
x_224 = lean_ctor_get_uint8(x_223, 0);
x_225 = lean_ctor_get_uint8(x_223, 1);
x_226 = lean_ctor_get_uint8(x_223, 2);
x_227 = lean_ctor_get_uint8(x_223, 3);
x_228 = lean_ctor_get_uint8(x_223, 4);
x_229 = lean_ctor_get_uint8(x_223, 5);
x_230 = lean_ctor_get_uint8(x_223, 6);
x_231 = lean_ctor_get_uint8(x_223, 7);
x_232 = lean_ctor_get_uint8(x_223, 8);
x_233 = lean_ctor_get_uint8(x_223, 9);
x_234 = lean_ctor_get_uint8(x_223, 10);
x_235 = lean_ctor_get_uint8(x_223, 11);
x_236 = lean_ctor_get_uint8(x_223, 17);
if (lean_is_exclusive(x_223)) {
 x_237 = x_223;
} else {
 lean_dec_ref(x_223);
 x_237 = lean_box(0);
}
x_238 = 1;
x_239 = 2;
if (lean_is_scalar(x_237)) {
 x_240 = lean_alloc_ctor(0, 0, 19);
} else {
 x_240 = x_237;
}
lean_ctor_set_uint8(x_240, 0, x_224);
lean_ctor_set_uint8(x_240, 1, x_225);
lean_ctor_set_uint8(x_240, 2, x_226);
lean_ctor_set_uint8(x_240, 3, x_227);
lean_ctor_set_uint8(x_240, 4, x_228);
lean_ctor_set_uint8(x_240, 5, x_229);
lean_ctor_set_uint8(x_240, 6, x_230);
lean_ctor_set_uint8(x_240, 7, x_231);
lean_ctor_set_uint8(x_240, 8, x_232);
lean_ctor_set_uint8(x_240, 9, x_233);
lean_ctor_set_uint8(x_240, 10, x_234);
lean_ctor_set_uint8(x_240, 11, x_235);
lean_ctor_set_uint8(x_240, 12, x_238);
lean_ctor_set_uint8(x_240, 13, x_238);
lean_ctor_set_uint8(x_240, 14, x_239);
lean_ctor_set_uint8(x_240, 15, x_238);
lean_ctor_set_uint8(x_240, 16, x_238);
lean_ctor_set_uint8(x_240, 17, x_236);
lean_ctor_set_uint8(x_240, 18, x_238);
x_241 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_240);
x_242 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set_uint64(x_242, sizeof(void*)*1, x_241);
x_243 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_220);
lean_ctor_set(x_243, 2, x_213);
lean_ctor_set(x_243, 3, x_218);
lean_ctor_set(x_243, 4, x_217);
lean_ctor_set(x_243, 5, x_214);
lean_ctor_set(x_243, 6, x_212);
lean_ctor_set_uint8(x_243, sizeof(void*)*7, x_215);
lean_ctor_set_uint8(x_243, sizeof(void*)*7 + 1, x_222);
lean_ctor_set_uint8(x_243, sizeof(void*)*7 + 2, x_219);
x_244 = l_Lean_Meta_inferTypeImp_infer(x_1, x_243, x_3, x_211, x_5, x_221);
return x_244;
}
block_302:
{
uint8_t x_247; uint8_t x_248; uint8_t x_249; uint8_t x_250; uint8_t x_251; uint8_t x_252; uint8_t x_253; uint8_t x_254; uint8_t x_255; uint8_t x_256; uint8_t x_257; uint8_t x_258; uint8_t x_259; uint8_t x_260; uint8_t x_261; uint8_t x_262; uint8_t x_263; uint8_t x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; uint8_t x_274; lean_object* x_275; uint64_t x_276; lean_object* x_277; uint64_t x_278; uint64_t x_279; uint64_t x_280; uint64_t x_281; uint64_t x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_247 = lean_ctor_get_uint8(x_207, 0);
x_248 = lean_ctor_get_uint8(x_207, 1);
x_249 = lean_ctor_get_uint8(x_207, 2);
x_250 = lean_ctor_get_uint8(x_207, 3);
x_251 = lean_ctor_get_uint8(x_207, 4);
x_252 = lean_ctor_get_uint8(x_207, 5);
x_253 = lean_ctor_get_uint8(x_207, 6);
x_254 = lean_ctor_get_uint8(x_207, 7);
x_255 = lean_ctor_get_uint8(x_207, 8);
x_256 = lean_ctor_get_uint8(x_207, 10);
x_257 = lean_ctor_get_uint8(x_207, 11);
x_258 = lean_ctor_get_uint8(x_207, 12);
x_259 = lean_ctor_get_uint8(x_207, 13);
x_260 = lean_ctor_get_uint8(x_207, 14);
x_261 = lean_ctor_get_uint8(x_207, 15);
x_262 = lean_ctor_get_uint8(x_207, 16);
x_263 = lean_ctor_get_uint8(x_207, 17);
x_264 = lean_ctor_get_uint8(x_207, 18);
if (lean_is_exclusive(x_207)) {
 x_265 = x_207;
} else {
 lean_dec_ref(x_207);
 x_265 = lean_box(0);
}
x_266 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_267 = lean_ctor_get(x_2, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_268);
x_269 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_269);
x_270 = lean_ctor_get(x_2, 4);
lean_inc(x_270);
x_271 = lean_ctor_get(x_2, 5);
lean_inc(x_271);
x_272 = lean_ctor_get(x_2, 6);
lean_inc(x_272);
x_273 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
x_274 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 2);
if (lean_is_scalar(x_265)) {
 x_275 = lean_alloc_ctor(0, 0, 19);
} else {
 x_275 = x_265;
}
lean_ctor_set_uint8(x_275, 0, x_247);
lean_ctor_set_uint8(x_275, 1, x_248);
lean_ctor_set_uint8(x_275, 2, x_249);
lean_ctor_set_uint8(x_275, 3, x_250);
lean_ctor_set_uint8(x_275, 4, x_251);
lean_ctor_set_uint8(x_275, 5, x_252);
lean_ctor_set_uint8(x_275, 6, x_253);
lean_ctor_set_uint8(x_275, 7, x_254);
lean_ctor_set_uint8(x_275, 8, x_255);
lean_ctor_set_uint8(x_275, 9, x_246);
lean_ctor_set_uint8(x_275, 10, x_256);
lean_ctor_set_uint8(x_275, 11, x_257);
lean_ctor_set_uint8(x_275, 12, x_258);
lean_ctor_set_uint8(x_275, 13, x_259);
lean_ctor_set_uint8(x_275, 14, x_260);
lean_ctor_set_uint8(x_275, 15, x_261);
lean_ctor_set_uint8(x_275, 16, x_262);
lean_ctor_set_uint8(x_275, 17, x_263);
lean_ctor_set_uint8(x_275, 18, x_264);
x_276 = l_Lean_Meta_Context_configKey(x_2);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_277 = x_2;
} else {
 lean_dec_ref(x_2);
 x_277 = lean_box(0);
}
x_278 = 2;
x_279 = lean_uint64_shift_right(x_276, x_278);
x_280 = lean_uint64_shift_left(x_279, x_278);
x_281 = l_Lean_Meta_TransparencyMode_toUInt64(x_246);
x_282 = lean_uint64_lor(x_280, x_281);
x_283 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_283, 0, x_275);
lean_ctor_set_uint64(x_283, sizeof(void*)*1, x_282);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc_ref(x_269);
lean_inc_ref(x_268);
lean_inc(x_267);
if (lean_is_scalar(x_277)) {
 x_284 = lean_alloc_ctor(0, 7, 3);
} else {
 x_284 = x_277;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_267);
lean_ctor_set(x_284, 2, x_268);
lean_ctor_set(x_284, 3, x_269);
lean_ctor_set(x_284, 4, x_270);
lean_ctor_set(x_284, 5, x_271);
lean_ctor_set(x_284, 6, x_272);
lean_ctor_set_uint8(x_284, sizeof(void*)*7, x_266);
lean_ctor_set_uint8(x_284, sizeof(void*)*7 + 1, x_273);
lean_ctor_set_uint8(x_284, sizeof(void*)*7 + 2, x_274);
x_285 = l_Lean_Meta_getConfig___redArg(x_284, x_6);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get_uint8(x_286, 13);
if (x_287 == 0)
{
lean_object* x_288; 
lean_dec(x_286);
x_288 = lean_ctor_get(x_285, 1);
lean_inc(x_288);
lean_dec_ref(x_285);
x_212 = x_272;
x_213 = x_268;
x_214 = x_271;
x_215 = x_266;
x_216 = x_284;
x_217 = x_270;
x_218 = x_269;
x_219 = x_274;
x_220 = x_267;
x_221 = x_288;
x_222 = x_273;
goto block_245;
}
else
{
uint8_t x_289; 
x_289 = lean_ctor_get_uint8(x_286, 12);
if (x_289 == 0)
{
lean_object* x_290; 
lean_dec(x_286);
x_290 = lean_ctor_get(x_285, 1);
lean_inc(x_290);
lean_dec_ref(x_285);
x_212 = x_272;
x_213 = x_268;
x_214 = x_271;
x_215 = x_266;
x_216 = x_284;
x_217 = x_270;
x_218 = x_269;
x_219 = x_274;
x_220 = x_267;
x_221 = x_290;
x_222 = x_273;
goto block_245;
}
else
{
uint8_t x_291; 
x_291 = lean_ctor_get_uint8(x_286, 15);
if (x_291 == 0)
{
lean_object* x_292; 
lean_dec(x_286);
x_292 = lean_ctor_get(x_285, 1);
lean_inc(x_292);
lean_dec_ref(x_285);
x_212 = x_272;
x_213 = x_268;
x_214 = x_271;
x_215 = x_266;
x_216 = x_284;
x_217 = x_270;
x_218 = x_269;
x_219 = x_274;
x_220 = x_267;
x_221 = x_292;
x_222 = x_273;
goto block_245;
}
else
{
uint8_t x_293; 
x_293 = lean_ctor_get_uint8(x_286, 18);
if (x_293 == 0)
{
lean_object* x_294; 
lean_dec(x_286);
x_294 = lean_ctor_get(x_285, 1);
lean_inc(x_294);
lean_dec_ref(x_285);
x_212 = x_272;
x_213 = x_268;
x_214 = x_271;
x_215 = x_266;
x_216 = x_284;
x_217 = x_270;
x_218 = x_269;
x_219 = x_274;
x_220 = x_267;
x_221 = x_294;
x_222 = x_273;
goto block_245;
}
else
{
uint8_t x_295; 
x_295 = lean_ctor_get_uint8(x_286, 16);
if (x_295 == 0)
{
lean_object* x_296; 
lean_dec(x_286);
x_296 = lean_ctor_get(x_285, 1);
lean_inc(x_296);
lean_dec_ref(x_285);
x_212 = x_272;
x_213 = x_268;
x_214 = x_271;
x_215 = x_266;
x_216 = x_284;
x_217 = x_270;
x_218 = x_269;
x_219 = x_274;
x_220 = x_267;
x_221 = x_296;
x_222 = x_273;
goto block_245;
}
else
{
lean_object* x_297; uint8_t x_298; uint8_t x_299; uint8_t x_300; 
x_297 = lean_ctor_get(x_285, 1);
lean_inc(x_297);
lean_dec_ref(x_285);
x_298 = lean_ctor_get_uint8(x_286, 14);
lean_dec(x_286);
x_299 = 2;
x_300 = l_Lean_Meta_instDecidableEqProjReductionKind(x_298, x_299);
if (x_300 == 0)
{
x_212 = x_272;
x_213 = x_268;
x_214 = x_271;
x_215 = x_266;
x_216 = x_284;
x_217 = x_270;
x_218 = x_269;
x_219 = x_274;
x_220 = x_267;
x_221 = x_297;
x_222 = x_273;
goto block_245;
}
else
{
lean_object* x_301; 
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_270);
lean_dec_ref(x_269);
lean_dec_ref(x_268);
lean_dec(x_267);
x_301 = l_Lean_Meta_inferTypeImp_infer(x_1, x_284, x_3, x_211, x_5, x_297);
return x_301;
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
lean_object* x_305; 
lean_dec_ref(x_205);
lean_dec(x_203);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec_ref(x_192);
lean_dec_ref(x_191);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_305 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_inferTypeImp_spec__0___redArg(x_196, x_6);
return x_305;
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
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
return x_5;
}
else
{
x_1 = x_4;
goto _start;
}
}
case 3:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
x_1 = x_7;
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
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at_____private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_7);
lean_dec(x_5);
x_8 = lean_instantiate_level_mvars(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_9);
x_16 = lean_st_ref_set(x_2, x_12, x_13);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_10);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_12, 1);
x_22 = lean_ctor_get(x_12, 2);
x_23 = lean_ctor_get(x_12, 3);
x_24 = lean_ctor_get(x_12, 4);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_24);
x_26 = lean_st_ref_set(x_2, x_25, x_13);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at_____private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateLevelMVars___at_____private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(x_1, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_2, x_14);
lean_dec(x_2);
if (x_15 == 0)
{
lean_dec(x_13);
x_8 = x_7;
goto block_12;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_instantiateLevelMVars___at_____private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(x_13, x_4, x_7);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(x_18);
lean_dec(x_18);
x_20 = l_Bool_toLBool(x_19);
x_21 = lean_box(x_20);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = l___private_Lean_Meta_InferType_0__Lean_Meta_isAlwaysZero(x_22);
lean_dec(x_22);
x_25 = l_Bool_toLBool(x_24);
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
}
case 7:
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_28);
lean_dec_ref(x_1);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_eq(x_2, x_29);
if (x_30 == 1)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_28);
lean_dec(x_2);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_7);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_2, x_34);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_35;
goto _start;
}
}
case 8:
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_1 = x_37;
goto _start;
}
case 10:
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_39);
lean_dec_ref(x_1);
x_1 = x_39;
goto _start;
}
default: 
{
lean_dec(x_2);
lean_dec_ref(x_1);
x_8 = x_7;
goto block_12;
}
}
block_12:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 2;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at_____private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateLevelMVars___at_____private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at_____private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateLevelMVars___at_____private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_1);
lean_inc_ref(x_3);
x_9 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(x_8, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(x_10, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
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
lean_dec_ref(x_1);
x_18 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(x_17, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(x_19, x_2, x_3, x_4, x_5, x_6, x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
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
lean_dec_ref(x_1);
lean_inc_ref(x_5);
x_28 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_26, x_27, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(x_29, x_2, x_3, x_4, x_5, x_6, x_30);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
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
lean_inc_ref(x_36);
lean_dec_ref(x_1);
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
lean_inc_ref(x_40);
lean_dec_ref(x_1);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_eq(x_2, x_41);
if (x_42 == 1)
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_40);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_43 = 0;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_7);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_sub(x_2, x_46);
lean_dec(x_2);
x_1 = x_40;
x_2 = x_47;
goto _start;
}
}
case 8:
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_49);
lean_dec_ref(x_1);
x_1 = x_49;
goto _start;
}
case 10:
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_51);
lean_dec_ref(x_1);
x_1 = x_51;
goto _start;
}
default: 
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_11 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(x_10, x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(x_12, x_14, x_2, x_3, x_4, x_5, x_13);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
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
lean_dec_ref(x_1);
x_21 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(x_20, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(x_22, x_24, x_2, x_3, x_4, x_5, x_23);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
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
lean_dec_ref(x_1);
lean_inc_ref(x_4);
x_32 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_30, x_31, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp(x_33, x_35, x_2, x_3, x_4, x_5, x_34);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
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
lean_inc_ref(x_41);
lean_dec_ref(x_1);
x_42 = lean_unsigned_to_nat(1u);
x_43 = l___private_Lean_Meta_InferType_0__Lean_Meta_isPropQuickApp(x_41, x_42, x_2, x_3, x_4, x_5, x_6);
return x_43;
}
case 7:
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_44);
lean_dec_ref(x_1);
x_1 = x_44;
goto _start;
}
case 8:
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_46);
lean_dec_ref(x_1);
x_1 = x_46;
goto _start;
}
case 10:
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_48);
lean_dec_ref(x_1);
x_1 = x_48;
goto _start;
}
case 11:
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_7);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_27 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
lean_inc(x_3);
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
lean_dec_ref(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = l_Lean_instantiateLevelMVars___at_____private_Lean_Meta_InferType_0__Lean_Meta_isArrowProp_spec__0___redArg(x_33, x_3, x_32);
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_box(1);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_box(2);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
default: 
{
uint8_t x_4; 
x_4 = 2;
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("outParam", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Level_isNeverZero(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Level_isZero(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(2);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_box(1);
return x_6;
}
}
else
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
}
case 5:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0;
x_14 = lean_string_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_box(2);
return x_15;
}
else
{
x_1 = x_11;
goto _start;
}
}
else
{
lean_object* x_17; 
x_17 = lean_box(2);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = lean_box(2);
return x_18;
}
}
else
{
lean_object* x_19; 
x_19 = lean_box(2);
return x_19;
}
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(2);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 1)
{
lean_object* x_7; 
lean_free_object(x_1);
lean_dec(x_4);
x_7 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_10, x_11);
if (x_12 == 1)
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp(x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_10, x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec_ref(x_1);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_2, x_34);
if (x_35 == 0)
{
lean_dec(x_33);
x_8 = x_7;
goto block_11;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_7);
return x_37;
}
}
case 7:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_39);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_eq(x_2, x_40);
if (x_41 == 1)
{
lean_dec_ref(x_39);
lean_dec_ref(x_38);
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
goto block_32;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_1);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_2, x_42);
x_44 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(x_39, x_43, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(x_46, x_38);
lean_dec_ref(x_38);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_50 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(x_48, x_38);
lean_dec_ref(x_38);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_dec_ref(x_38);
return x_44;
}
}
}
case 8:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_69; uint8_t x_70; 
x_52 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_53);
lean_dec_ref(x_1);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_nat_dec_eq(x_2, x_69);
if (x_70 == 0)
{
x_54 = x_2;
x_55 = x_3;
x_56 = x_4;
x_57 = x_5;
x_58 = x_6;
x_59 = x_7;
goto block_68;
}
else
{
x_54 = x_69;
x_55 = x_3;
x_56 = x_4;
x_57 = x_5;
x_58 = x_6;
x_59 = x_7;
goto block_68;
}
block_68:
{
lean_object* x_60; 
x_60 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(x_53, x_54, x_55, x_56, x_57, x_58, x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(x_62, x_52);
lean_dec_ref(x_52);
lean_ctor_set(x_60, 0, x_63);
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_60);
x_66 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_processResult(x_64, x_52);
lean_dec_ref(x_52);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_dec_ref(x_52);
return x_60;
}
}
}
case 10:
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_71);
lean_dec_ref(x_1);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_dec_eq(x_2, x_72);
if (x_73 == 0)
{
x_1 = x_71;
goto _start;
}
else
{
x_1 = x_71;
x_2 = x_72;
goto _start;
}
}
default: 
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_dec_eq(x_2, x_76);
if (x_77 == 0)
{
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_8 = x_7;
goto block_11;
}
else
{
x_12 = x_1;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
goto block_32;
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
block_32:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_isPropQuick(x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
x_22 = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(x_21);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_unbox(x_23);
lean_dec(x_23);
x_26 = l___private_Lean_Meta_InferType_0__Lean_Meta_toArrowPropResult(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = l___private_Lean_Meta_InferType_0__Lean_Meta_ArrowPropResult_toLBool(x_13);
lean_dec(x_13);
x_16 = lean_box(x_15);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
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
lean_dec_ref(x_1);
lean_inc_ref(x_3);
x_9 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(x_8, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(x_10, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_2);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
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
lean_dec_ref(x_1);
x_18 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(x_17, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(x_19, x_2, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_2);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
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
lean_dec_ref(x_1);
lean_inc_ref(x_5);
x_28 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_26, x_27, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(x_29, x_2, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_2);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
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
lean_inc_ref(x_36);
lean_dec_ref(x_1);
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
lean_inc_ref(x_40);
lean_dec_ref(x_1);
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
lean_inc_ref(x_47);
lean_dec_ref(x_1);
x_1 = x_47;
goto _start;
}
case 10:
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_1);
x_1 = x_49;
goto _start;
}
default: 
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_11 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(x_10, x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(x_12, x_14, x_2, x_3, x_4, x_5, x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
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
lean_dec_ref(x_1);
x_21 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(x_20, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(x_22, x_24, x_2, x_3, x_4, x_5, x_23);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
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
lean_dec_ref(x_1);
lean_inc_ref(x_4);
x_32 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_30, x_31, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition(x_33, x_35, x_2, x_3, x_4, x_5, x_34);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
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
lean_inc_ref(x_41);
lean_dec_ref(x_1);
x_42 = lean_unsigned_to_nat(1u);
x_43 = l___private_Lean_Meta_InferType_0__Lean_Meta_isProofQuickApp(x_41, x_42, x_2, x_3, x_4, x_5, x_6);
return x_43;
}
case 6:
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_44);
lean_dec_ref(x_1);
x_1 = x_44;
goto _start;
}
case 8:
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_46);
lean_dec_ref(x_1);
x_1 = x_46;
goto _start;
}
case 10:
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_48);
lean_dec_ref(x_1);
x_1 = x_48;
goto _start;
}
case 11:
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_7);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_27 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = l_Lean_Meta_isProp(x_28, x_2, x_3, x_4, x_5, x_29);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_2, x_9);
lean_dec(x_2);
if (x_10 == 0)
{
x_4 = x_3;
goto block_8;
}
else
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
case 7:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_2, x_15);
if (x_16 == 1)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_2, x_20);
lean_dec(x_2);
x_1 = x_14;
x_2 = x_21;
goto _start;
}
}
case 8:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_1, 3);
x_1 = x_23;
goto _start;
}
case 10:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_1, 1);
x_1 = x_25;
goto _start;
}
default: 
{
lean_dec(x_2);
x_4 = x_3;
goto block_8;
}
}
block_8:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = 2;
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
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
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
x_9 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(x_8, x_3, x_5, x_6, x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
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
lean_dec_ref(x_1);
x_18 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(x_17, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
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
lean_dec_ref(x_1);
x_28 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_26, x_27, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_3);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
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
lean_inc_ref(x_36);
lean_dec_ref(x_1);
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
lean_inc_ref(x_40);
lean_dec_ref(x_1);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_eq(x_2, x_41);
if (x_42 == 1)
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_40);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_43 = 0;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_7);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_sub(x_2, x_46);
lean_dec(x_2);
x_1 = x_40;
x_2 = x_47;
goto _start;
}
}
case 8:
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_49);
lean_dec_ref(x_1);
x_1 = x_49;
goto _start;
}
case 10:
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_51);
lean_dec_ref(x_1);
x_1 = x_51;
goto _start;
}
default: 
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
x_8 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferFVarType___redArg(x_7, x_2, x_4, x_5, x_6);
lean_dec_ref(x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
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
lean_dec_ref(x_1);
x_18 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferMVarType(x_17, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
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
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
x_32 = l___private_Lean_Meta_InferType_0__Lean_Meta_inferConstType(x_30, x_31, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowType___redArg(x_33, x_35, x_34);
lean_dec(x_33);
return x_36;
}
else
{
uint8_t x_37; 
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
lean_inc_ref(x_41);
lean_dec_ref(x_1);
x_42 = lean_unsigned_to_nat(1u);
x_43 = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeQuickApp(x_41, x_42, x_2, x_3, x_4, x_5, x_6);
return x_43;
}
case 6:
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_inc_ref(x_50);
lean_dec_ref(x_1);
x_1 = x_50;
goto _start;
}
case 9:
{
uint8_t x_52; lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_inc_ref(x_55);
lean_dec_ref(x_1);
x_1 = x_55;
goto _start;
}
default: 
{
uint8_t x_57; lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_7);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_27 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = l_Lean_Meta_whnfD(x_28, x_2, x_3, x_4, x_5, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 3)
{
uint8_t x_32; 
lean_dec_ref(x_31);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec_ref(x_1);
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
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_16);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_typeFormerTypeLevel_go___lam__0), 8, 2);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_16);
x_19 = lean_expr_instantiate_rev(x_15, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_15);
x_20 = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(x_14, x_17, x_19, x_18, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
default: 
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec_ref(x_23);
x_8 = x_25;
x_9 = x_24;
goto block_12;
}
case 7:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec_ref(x_22);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_5);
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
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_11);
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
lean_dec_ref(x_13);
lean_inc(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = l_Lean_Meta_typeFormerTypeLevel___lam__0(x_3, x_11, x_16, x_15);
lean_dec_ref(x_16);
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
lean_dec_ref(x_13);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_8);
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
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Lean_Meta_isPropFormerType_spec__0(lean_object* x_1, lean_object* x_2) {
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
x_11 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Lean_Meta_isPropFormerType_spec__0(x_9, x_10);
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
x_16 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Lean_Meta_isPropFormerType_spec__0(x_13, x_15);
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
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Lean_Meta_isPropFormerType_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Lean_Meta_isPropFormerType_spec__0(x_1, x_2);
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
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l_Lean_Meta_isTypeFormerType(x_8, x_2, x_3, x_4, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_6);
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
uint8_t x_11; 
x_11 = 0;
return x_11;
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
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
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_12 = lean_infer_type(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_unsigned_to_nat(0u);
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
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
lean_dec_ref(x_2);
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
lean_dec_ref(x_2);
x_10 = l_Lean_Expr_fvar___override(x_9);
x_11 = l_Array_contains___at___Lean_Meta_arrowDomainsN_spec__0(x_1, x_10);
lean_dec_ref(x_10);
return x_11;
}
case 5:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_2);
x_14 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_arrowDomainsN_spec__3(x_1, x_12);
if (x_14 == 0)
{
x_2 = x_13;
goto _start;
}
else
{
lean_dec_ref(x_13);
return x_3;
}
}
case 6:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_17);
lean_dec_ref(x_2);
x_4 = x_16;
x_5 = x_17;
goto block_8;
}
case 7:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_19);
lean_dec_ref(x_2);
x_4 = x_18;
x_5 = x_19;
goto block_8;
}
case 8:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_22);
lean_dec_ref(x_2);
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
lean_dec_ref(x_22);
return x_3;
}
}
else
{
lean_dec_ref(x_22);
lean_dec_ref(x_21);
return x_3;
}
}
case 10:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_26);
lean_dec_ref(x_2);
x_2 = x_26;
goto _start;
}
case 11:
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_28);
lean_dec_ref(x_2);
x_2 = x_28;
goto _start;
}
default: 
{
uint8_t x_30; 
lean_dec_ref(x_2);
x_30 = 0;
return x_30;
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
lean_dec_ref(x_5);
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
lean_dec_ref(x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_array_uget(x_4, x_6);
lean_inc_ref(x_21);
x_22 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_arrowDomainsN_spec__3(x_1, x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
x_13 = x_2;
x_14 = x_12;
goto block_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_32 = l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___redArg(x_31, x_8, x_9, x_10, x_11, x_12);
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
lean_dec_ref(x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_array_uget(x_4, x_6);
lean_inc_ref(x_21);
x_22 = l_Lean_Expr_hasAnyFVar_visit___at___Lean_Meta_arrowDomainsN_spec__3(x_1, x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
x_13 = x_2;
x_14 = x_12;
goto block_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_32 = l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___redArg(x_31, x_8, x_9, x_10, x_11, x_12);
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
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferForallType_spec__1___redArg___lam__0), 8, 1);
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
lean_dec_ref(x_3);
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
x_23 = l_Lean_throwError___at___Lean_Meta_throwFunctionExpected_spec__0___redArg(x_22, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_3);
x_30 = l_Array_mapMUnsafe_map___at___Lean_Meta_arrowDomainsN_spec__2(x_28, x_29, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_box(0);
x_34 = lean_array_size(x_31);
x_35 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_arrowDomainsN_spec__4(x_3, x_33, x_1, x_31, x_34, x_29, x_33, x_5, x_6, x_7, x_8, x_32);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
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
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
lean_inc(x_1);
lean_inc_ref(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_arrowDomainsN___lam__0___boxed), 9, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = 0;
x_11 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_2, x_9, x_8, x_10, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
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
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___Lean_Meta_arrowDomainsN_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___Lean_Meta_arrowDomainsN_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_1);
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
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
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
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___redArg(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_5);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_arrowDomainsN___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_arrowDomainsN___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Lean_Meta_arrowDomainsN(x_1, x_9, x_3, x_4, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___closed__0 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___closed__0();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferAppType_spec__0___redArg___closed__0);
l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0 = _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__0);
l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1 = _init_l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_throwIncorrectNumberOfLevels___redArg___closed__1);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___closed__0 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___closed__0();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___lam__0___closed__0);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__0);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__1);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__2);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__3);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__4 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__4();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__4);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__5);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__6 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__6();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__6);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__7 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__7();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__7);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__8 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__8();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__8);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__9 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__9();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__9);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__10 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__10();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__10);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__11 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__11();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__11);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__12 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__12();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__12);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__13 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__13();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__13);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__14 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__14();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__14);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__15 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__15();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__15);
l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__16 = _init_l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__16();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessage___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0_spec__0_spec__0___closed__16);
l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__0);
l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__1);
l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__2 = _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__2);
l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__3 = _init_l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___at___Lean_throwUnknownConstant___at___Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0_spec__0_spec__0___redArg___closed__3);
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
l_Lean_Meta_throwTypeExpected___redArg___closed__0 = _init_l_Lean_Meta_throwTypeExpected___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_throwTypeExpected___redArg___closed__0);
l_Lean_Meta_throwTypeExpected___redArg___closed__1 = _init_l_Lean_Meta_throwTypeExpected___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_throwTypeExpected___redArg___closed__1);
l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___closed__0 = _init_l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___closed__0);
l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___closed__1 = _init_l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg___closed__1);
l_Lean_Meta_throwUnknownMVar___redArg___closed__0 = _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_throwUnknownMVar___redArg___closed__0);
l_Lean_Meta_throwUnknownMVar___redArg___closed__1 = _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_throwUnknownMVar___redArg___closed__1);
l_Lean_Meta_throwUnknownMVar___redArg___closed__2 = _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_throwUnknownMVar___redArg___closed__2);
l_Lean_Meta_throwUnknownMVar___redArg___closed__3 = _init_l_Lean_Meta_throwUnknownMVar___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_throwUnknownMVar___redArg___closed__3);
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
l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0 = _init_l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0();
lean_mark_persistent(l___private_Lean_Meta_InferType_0__Lean_Meta_isArrowProposition_x27_checkProp___closed__0);
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
